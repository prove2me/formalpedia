-- Prove2me | solution 1 for CachingML.PredMarker.opt_le_cleanCount
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:55:14.165844+00:00
-- url     : https://prove2.me/submissions/2c1f62d0-2b94-499b-b12e-5065650d7dc1

import Mathlib
import Definitions.Def_CachingML_PredMarker_opt
import Definitions.Def_CachingML_PredMarker_cleanCount

set_option autoImplicit false
open CachingML.PredMarker

namespace PhaseAux

variable {α : Type*} [DecidableEq α]

/-- the set of all elements of the phase that is currently being scanned -/
def phaseElems (k : ℕ) : Finset α → List α → Finset α
  | cur, [] => cur
  | cur, z :: τ =>
    if z ∈ cur then phaseElems k cur τ
    else if cur.card < k then phaseElems k (insert z cur) τ else cur

lemma sub_phase (k : ℕ) : ∀ (τ : List α) (cur : Finset α), cur ⊆ phaseElems k cur τ
  | [], cur => by simp [phaseElems]
  | z :: τ, cur => by
    unfold phaseElems
    by_cases h1 : z ∈ cur
    · simp only [h1, if_true]; exact sub_phase k τ cur
    · by_cases h2 : cur.card < k
      · simp only [h1, h2, if_true, if_false]
        exact (Finset.subset_insert z cur).trans (sub_phase k τ _)
      · simp [h1, h2]

lemma card_phase (k : ℕ) : ∀ (τ : List α) (cur : Finset α), cur.card ≤ k →
    (phaseElems k cur τ).card ≤ k
  | [], cur, h => by simpa [phaseElems] using h
  | z :: τ, cur, h => by
    unfold phaseElems
    by_cases h1 : z ∈ cur
    · simp only [h1, if_true]; exact card_phase k τ cur h
    · by_cases h2 : cur.card < k
      · simp only [h1, h2, if_true, if_false]
        exact card_phase k τ _ (by rw [Finset.card_insert_of_notMem h1]; omega)
      · simp [h1, h2, h]

lemma exists_evict (k : ℕ) (C N : Finset α) (hCk : C.card = k) (hNk : N.card ≤ k) (z : α)
    (hzN : z ∈ N) (hzC : z ∉ C) : ∃ e ∈ C, e ∉ N := by
  by_contra hcon
  push Not at hcon
  have hsub : C ⊆ N := hcon
  have : C.card < N.card :=
    Finset.card_lt_card ⟨hsub, fun h => hzC (h hzN)⟩
  omega

lemma key (k : ℕ) (hk : 1 ≤ k) : ∀ (τ : List α) (prev cur C : Finset α), cur.card ≤ k →
    cur ⊆ C → C.card ≤ k → phaseElems k cur τ ∩ prev ⊆ C →
    optFrom k C τ ≤ cleanCountAux k prev cur τ := by
  intro τ
  induction τ with
  | nil => intros; simp [optFrom, cleanCountAux]
  | cons z τ ih =>
    intro prev cur C hcur hcC hCk hN
    by_cases hz : z ∈ cur
    · have hzC : z ∈ C := hcC hz
      have hN' : phaseElems k cur τ ∩ prev ⊆ C := by simpa [phaseElems, hz] using hN
      rw [optFrom, if_pos hzC, cleanCountAux, if_pos hz]
      exact ih prev cur C hcur hcC hCk hN'
    · by_cases hlt : cur.card < k
      · have hNeq : phaseElems k cur (z :: τ) = phaseElems k (insert z cur) τ := by
          simp [phaseElems, hz, hlt]
        have hzN : z ∈ phaseElems k cur (z :: τ) := by
          rw [hNeq]; exact sub_phase k τ _ (Finset.mem_insert_self z cur)
        have hcur' : (insert z cur).card ≤ k := by
          rw [Finset.card_insert_of_notMem hz]; omega
        have hN2 : phaseElems k (insert z cur) τ ∩ prev ⊆ C := by rw [← hNeq]; exact hN
        rw [cleanCountAux, if_neg hz, if_pos hlt]
        by_cases hzC : z ∈ C
        · rw [optFrom, if_pos hzC]
          have := ih prev (insert z cur) C hcur' (Finset.insert_subset hzC hcC) hCk hN2
          omega
        · have hzp : z ∉ prev := by
            intro hzp
            exact hzC (hN (Finset.mem_inter.2 ⟨hzN, hzp⟩))
          rw [optFrom, if_neg hzC]
          by_cases hCl : C.card < k
          · rw [if_pos hCl]
            have := ih prev (insert z cur) (insert z C) hcur' (Finset.insert_subset_insert z hcC)
              (by rw [Finset.card_insert_of_notMem hzC]; omega)
              (by intro w hw; exact Finset.mem_insert_of_mem (hN2 hw))
            rw [if_neg hzp]
            omega
          · rw [if_neg hCl]
            have hCk' : C.card = k := le_antisymm hCk (not_lt.1 hCl)
            have hCne : C.Nonempty := Finset.card_pos.1 (by omega)
            rw [dif_pos hCne]
            have hNk := card_phase k (z :: τ) cur hcur
            obtain ⟨e, heC, heN⟩ := exists_evict k C _ hCk' hNk z hzN hzC
            have hle : C.inf' hCne (fun e => optFrom k (insert z (C.erase e)) τ) ≤
                optFrom k (insert z (C.erase e)) τ :=
              Finset.inf'_le (fun e => optFrom k (insert z (C.erase e)) τ) heC
            have hcurN := sub_phase k (z :: τ) cur
            have := ih prev (insert z cur) (insert z (C.erase e)) hcur'
              (Finset.insert_subset_insert z (fun w hw => Finset.mem_erase.2
                ⟨fun h => heN (h ▸ hcurN hw), hcC hw⟩))
              (by
                calc (insert z (C.erase e)).card ≤ (C.erase e).card + 1 := Finset.card_insert_le _ _
                  _ ≤ k := by rw [Finset.card_erase_of_mem heC]; omega)
              (by
                intro w hw
                have hwN : w ∈ phaseElems k cur (z :: τ) := by rw [hNeq]; exact (Finset.mem_inter.1 hw).1
                exact Finset.mem_insert_of_mem (Finset.mem_erase.2
                  ⟨fun h => heN (h ▸ hwN), hN (Finset.mem_inter.2 ⟨hwN, (Finset.mem_inter.1 hw).2⟩)⟩))
            rw [if_neg hzp]
            omega
      · have hcurk : cur.card = k := le_antisymm hcur (not_lt.1 hlt)
        have hcurC : cur = C := Finset.eq_of_subset_of_card_le hcC (by omega)
        rw [cleanCountAux, if_neg hz, if_neg hlt]
        have hzC : z ∉ C := hcurC ▸ hz
        have hCk' : C.card = k := by rw [← hcurC]; exact hcurk
        rw [optFrom, if_neg hzC, if_neg (by omega : ¬ C.card < k)]
        have hCne : C.Nonempty := Finset.card_pos.1 (by omega)
        rw [dif_pos hCne]
        have hs1 : ({z} : Finset α).card ≤ k := by simp; omega
        have hNk := card_phase k τ {z} hs1
        have hzN : z ∈ phaseElems k {z} τ := sub_phase k τ {z} (Finset.mem_singleton_self z)
        obtain ⟨e, heC, heN⟩ := exists_evict k C _ (by omega) hNk z hzN hzC
        have hle : C.inf' hCne (fun e => optFrom k (insert z (C.erase e)) τ) ≤
            optFrom k (insert z (C.erase e)) τ :=
          Finset.inf'_le (fun e => optFrom k (insert z (C.erase e)) τ) heC
        have := ih cur {z} (insert z (C.erase e)) hs1
          (by intro w hw; rw [Finset.mem_singleton.1 hw]; exact Finset.mem_insert_self _ _)
          (by
            calc (insert z (C.erase e)).card ≤ (C.erase e).card + 1 := Finset.card_insert_le _ _
              _ ≤ k := by rw [Finset.card_erase_of_mem heC]; omega)
          (by
            intro w hw
            have hwC : w ∈ C := hcurC ▸ (Finset.mem_inter.1 hw).2
            exact Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨fun h => heN (h ▸ (Finset.mem_inter.1 hw).1), hwC⟩))
        omega

end PhaseAux

theorem solution {α : Type*} [DecidableEq α] (k : ℕ) (hk : 1 ≤ k) (σ : List α) :
    opt k σ ≤ cleanCount k σ :=
  PhaseAux.key k hk σ ∅ ∅ ∅ (by simp) (by simp) (by simp) (by simp)
