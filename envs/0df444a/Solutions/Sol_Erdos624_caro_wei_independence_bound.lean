-- Prove2me | solution 1 for Erdos624.caro_wei_independence_bound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-20T13:54:07.338302+00:00
-- url     : https://prove2.me/submissions/113c4271-4b60-483b-90e6-ef605cab1583

import Mathlib
open Finset

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace E624R21CW
open Finset

variable {α : Type*} [DecidableEq α]

/-- Degree of `x` in the simple graph with edge-set `E`. -/
def deg (E : Finset (Finset α)) (x : α) : ℕ :=
  #{e ∈ E | x ∈ e}

lemma deg_mono {E E' : Finset (Finset α)} (h : E' ⊆ E) (x : α) :
    deg E' x ≤ deg E x :=
  card_le_card (filter_subset_filter (fun e => x ∈ e) h)

lemma sum_deg (V : Finset α) (E : Finset (Finset α))
    (hE : ∀ e ∈ E, #e = 2 ∧ e ⊆ V) :
    ∑ x ∈ V, deg E x = 2 * #E := by
  classical
  calc
    ∑ x ∈ V, deg E x
        = ∑ x ∈ V, ∑ e ∈ E, (if x ∈ e then (1 : ℕ) else 0) := by
          refine sum_congr rfl ?_
          intro x _hx
          simp [deg, sum_boole]
    _ = ∑ e ∈ E, ∑ x ∈ V, (if x ∈ e then (1 : ℕ) else 0) := by
          rw [sum_comm]
    _ = ∑ e ∈ E, #(V ∩ e) := by
          refine sum_congr rfl ?_
          intro e _he
          simp [sum_boole]
    _ = ∑ e ∈ E, 2 := by
          refine sum_congr rfl ?_
          intro e he
          rcases hE e he with ⟨h2, hsub⟩
          rw [inter_eq_right.2 hsub, h2]
    _ = 2 * #E := by
          simp [sum_const, mul_comm]

/-- The other endpoint of a 2-edge containing `v`. -/
lemma exists_other_endpoint {e : Finset α} {v : α}
    (h2 : #e = 2) (hv : v ∈ e) :
    ∃ w, w ≠ v ∧ e = {v, w} := by
  have hcard : #(e.erase v) = 1 := by
    rw [card_erase_of_mem hv, h2]
  obtain ⟨w, hw⟩ := card_eq_one.1 hcard
  have hw' : w ∈ e.erase v := by simp [hw]
  have hwv : w ≠ v := (mem_erase.1 hw').1
  have heq : e = {v, w} := by
    ext x
    constructor
    · intro hx
      by_cases hxv : x = v
      · simp [hxv]
      · have : x ∈ e.erase v := mem_erase.2 ⟨hxv, hx⟩
        simp [hw] at this
        simp [this]
    · intro hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hv
      · exact (mem_erase.1 hw').2
  exact ⟨w, hwv, heq⟩

lemma card_closed_neighborhood (V : Finset α) (E : Finset (Finset α)) (v : α)
    (hv : v ∈ V) (hE : ∀ e ∈ E, #e = 2 ∧ e ⊆ V) :
    #{y ∈ V | y = v ∨ ({v, y} : Finset α) ∈ E} = deg E v + 1 := by
  classical
  let Nnbr : Finset α := {y ∈ V | ({v, y} : Finset α) ∈ E}
  have hvnot : v ∉ Nnbr := by
    intro h
    have hvE : ({v, v} : Finset α) ∈ E := (mem_filter.1 h).2
    have : ({v} : Finset α) ∈ E := by simpa using hvE
    have h2 := (hE _ this).1
    simp at h2
  have hN : {y ∈ V | y = v ∨ ({v, y} : Finset α) ∈ E} = insert v Nnbr := by
    ext y
    simp only [mem_filter, mem_insert, Nnbr]
    constructor
    · rintro ⟨hyV, rfl | hyE⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hyV, hyE⟩
    · rintro (rfl | hy)
      · exact ⟨hv, Or.inl rfl⟩
      · exact ⟨hy.1, Or.inr hy.2⟩
  have hbij : #Nnbr = deg E v := by
    refine card_bij (fun y _ => ({v, y} : Finset α)) ?_ ?_ ?_
    · intro y hy
      exact mem_filter.2 ⟨(mem_filter.1 hy).2, by simp⟩
    · intro y hy y' hy' heq
      have hymem : y ∈ ({v, y'} : Finset α) := by
        have : y ∈ ({v, y} : Finset α) := by simp
        rwa [heq] at this
      have hyor : y = v ∨ y = y' := by
        simpa [mem_insert, mem_singleton] using hymem
      rcases hyor with hyv | rfl
      · have hpair : ({v, y} : Finset α) = ({v} : Finset α) := by simp [hyv]
        have hvE : ({v} : Finset α) ∈ E := by
          have hmem := (mem_filter.1 hy).2
          rwa [hpair] at hmem
        have h2 := (hE _ hvE).1
        simp at h2
      · rfl
    · intro e he
      have heE : e ∈ E := (mem_filter.1 he).1
      have hvE : v ∈ e := (mem_filter.1 he).2
      have h2 := (hE e heE).1
      obtain ⟨w, hwne, heq⟩ := exists_other_endpoint h2 hvE
      have hwV : w ∈ V := (hE e heE).2 (by simp [heq])
      refine ⟨w, ?_, heq.symm⟩
      exact mem_filter.2 ⟨hwV, by simpa [heq] using heE⟩
  rw [hN, card_insert_of_notMem hvnot, hbij, add_comm]

/-- Caro–Wei via a minimum-degree deletion: some independent set is at least
`∑ 1/(deg+1)` in size. -/
lemma caro_wei_sum (V : Finset α) (E : Finset (Finset α))
    (hE : ∀ e ∈ E, #e = 2 ∧ e ⊆ V) :
    ∃ S ⊆ V, (∀ e ∈ E, ¬ e ⊆ S) ∧
      (∑ x ∈ V, (1 : ℝ) / (deg E x + 1)) ≤ (#S : ℝ) := by
  classical
  induction V using Finset.strongInductionOn generalizing E with
  | _ V ih =>
    by_cases hV : V.Nonempty
    · obtain ⟨v, hvV, hmin⟩ := exists_min_image V (fun x => deg E x) hV
      let N : Finset α := {y ∈ V | y = v ∨ ({v, y} : Finset α) ∈ E}
      have hvN : v ∈ N := mem_filter.2 ⟨hvV, Or.inl rfl⟩
      have hNV : N ⊆ V := filter_subset _ V
      let V' : Finset α := V \ N
      let E' : Finset (Finset α) := E.filter (fun e => e ⊆ V')
      have hss : V' ⊂ V := sdiff_ssubset hNV ⟨v, hvN⟩
      have hE' : ∀ e ∈ E', #e = 2 ∧ e ⊆ V' := by
        intro e he
        have heE := (mem_filter.1 he).1
        exact ⟨(hE e heE).1, (mem_filter.1 he).2⟩
      obtain ⟨S', hS'V', hindep', hsum'⟩ := ih V' hss E' hE'
      let S : Finset α := insert v S'
      have hvS' : v ∉ S' := by
        intro hv
        exact (mem_sdiff.1 (hS'V' hv)).2 hvN
      have hSV : S ⊆ V := insert_subset hvV (hS'V'.trans sdiff_subset)
      have hindep : ∀ e ∈ E, ¬ e ⊆ S := by
        intro e he heS
        have h2 := (hE e he).1
        by_cases hv_in : v ∈ e
        · obtain ⟨w, hwne, heq⟩ := exists_other_endpoint h2 hv_in
          have hwS : w ∈ S := heS (by simp [heq])
          have hwV : w ∈ V := (hE e he).2 (by simp [heq])
          have hwN : w ∈ N :=
            mem_filter.2 ⟨hwV, Or.inr (by simpa [heq] using he)⟩
          have hwS' : w ∈ S' := (mem_insert.1 hwS).resolve_left hwne
          exact (mem_sdiff.1 (hS'V' hwS')).2 hwN
        · have heS' : e ⊆ S' := by
            intro x hx
            have hxS := heS hx
            rcases mem_insert.1 hxS with rfl | hxS'
            · exact (hv_in hx).elim
            · exact hxS'
          have heE' : e ∈ E' := mem_filter.2 ⟨he, heS'.trans hS'V'⟩
          exact hindep' e heE' heS'
      have hNcard : #N = deg E v + 1 := card_closed_neighborhood V E v hvV hE
      have hboundN : (∑ x ∈ N, (1 : ℝ) / (deg E x + 1)) ≤ 1 := by
        have hle : ∀ x ∈ N, (1 : ℝ) / (deg E x + 1) ≤ 1 / (deg E v + 1) := by
          intro x hx
          have hdeg : deg E v ≤ deg E x := hmin x (hNV hx)
          have hpos : (0 : ℝ) < deg E v + 1 := by exact_mod_cast Nat.succ_pos _
          exact one_div_le_one_div_of_le hpos (by exact_mod_cast Nat.succ_le_succ hdeg)
        have hsumle := sum_le_sum hle
        have hconst :
            ∑ x ∈ N, (1 : ℝ) / (deg E v + 1) = (#N : ℝ) * (1 / (deg E v + 1)) := by
          simp [sum_const, nsmul_eq_mul]
        have hmul : (#N : ℝ) * (1 / (deg E v + 1 : ℝ)) = 1 := by
          have hpos : (deg E v + 1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero (deg E v))
          rw [hNcard, Nat.cast_add, Nat.cast_one, mul_one_div, div_self hpos]
        linarith
      have hdeg' : ∀ x ∈ V', (1 : ℝ) / (deg E x + 1) ≤ 1 / (deg E' x + 1) := by
        intro x hx
        have hle : deg E' x ≤ deg E x := deg_mono (filter_subset _ E) x
        have hpos : (0 : ℝ) < deg E' x + 1 := by exact_mod_cast Nat.succ_pos _
        exact one_div_le_one_div_of_le hpos (by exact_mod_cast Nat.succ_le_succ hle)
      have hsumV' := sum_le_sum hdeg'
      have hdisj : Disjoint V' N := sdiff_disjoint
      have hunion : V' ∪ N = V := sdiff_union_of_subset hNV
      have hsplit :
          (∑ x ∈ V, (1 : ℝ) / (deg E x + 1)) =
            (∑ x ∈ V', (1 : ℝ) / (deg E x + 1)) +
              ∑ x ∈ N, (1 : ℝ) / (deg E x + 1) := by
        rw [← sum_union hdisj, hunion]
      refine ⟨S, hSV, hindep, ?_⟩
      have hcardS : (#S : ℝ) = (#S' : ℝ) + 1 := by
        rw [card_insert_of_notMem hvS', Nat.cast_add, Nat.cast_one]
      calc
        ∑ x ∈ V, (1 : ℝ) / (deg E x + 1)
            = (∑ x ∈ V', (1 : ℝ) / (deg E x + 1)) +
                ∑ x ∈ N, (1 : ℝ) / (deg E x + 1) := hsplit
        _ ≤ (∑ x ∈ V', (1 : ℝ) / (deg E' x + 1)) + 1 := by
              linarith [hsumV', hboundN]
        _ ≤ (#S' : ℝ) + 1 := by linarith [hsum']
        _ = (#S : ℝ) := hcardS.symm
    · have hV0 : V = ∅ := not_nonempty_iff_eq_empty.1 hV
      refine ⟨∅, empty_subset V, ?_, ?_⟩
      · intro e he heS
        have h2 := (hE e he).1
        have : e = ∅ := subset_empty.1 heS
        simp [this] at h2
      · simp [hV0]

/-- The boxed Caro–Wei / Cauchy form. -/
theorem caro_wei_independence_bound (V : Finset α) (E : Finset (Finset α))
    (hE : ∀ e ∈ E, #e = 2 ∧ e ⊆ V) :
    ∃ S ⊆ V, (∀ e ∈ E, ¬ e ⊆ S) ∧
      (#V : ℝ) ^ 2 ≤ (#S : ℝ) * (#V + 2 * #E : ℝ) := by
  classical
  obtain ⟨S, hSV, hindep, hsum⟩ := caro_wei_sum V E hE
  refine ⟨S, hSV, hindep, ?_⟩
  by_cases hV : V.Nonempty
  · have hg : ∀ x ∈ V, (0 : ℝ) < (deg E x + 1 : ℝ) := fun _ _ =>
      by exact_mod_cast Nat.succ_pos _
    have hleft := sq_sum_div_le_sum_sq_div (R := ℝ) V (fun _ => (1 : ℝ)) hg
    have hsum1 : ∑ x ∈ V, (1 : ℝ) = (#V : ℝ) := by simp
    have hden : ∑ x ∈ V, (deg E x + 1 : ℝ) = (#V + 2 * #E : ℝ) := by
      have h1 : ∑ x ∈ V, (deg E x + 1 : ℝ) =
          (∑ x ∈ V, (deg E x : ℝ)) + ∑ x ∈ V, (1 : ℝ) := by
        simp [sum_add_distrib]
      have hdeg : ∑ x ∈ V, (deg E x : ℝ) = (2 * #E : ℝ) := by
        exact_mod_cast sum_deg V E hE
      rw [h1, hdeg, hsum1]
      ring
    have hnum : ∑ x ∈ V, (1 : ℝ) ^ 2 / (deg E x + 1) =
        ∑ x ∈ V, (1 : ℝ) / (deg E x + 1) := by
      simp
    have hpos : (0 : ℝ) < #V + 2 * #E := by
      have : (0 : ℝ) < (#V : ℝ) := by exact_mod_cast card_pos.2 hV
      linarith
    have hfrac : (#V : ℝ) ^ 2 / (#V + 2 * #E : ℝ) ≤
        ∑ x ∈ V, (1 : ℝ) / (deg E x + 1) := by
      simpa [hsum1, hden, hnum] using hleft
    have hmul : (#V : ℝ) ^ 2 ≤
        (∑ x ∈ V, (1 : ℝ) / (deg E x + 1)) * (#V + 2 * #E : ℝ) :=
      (div_le_iff₀ hpos).1 hfrac
    have hscale : (∑ x ∈ V, (1 : ℝ) / (deg E x + 1)) * (#V + 2 * #E : ℝ) ≤
        (#S : ℝ) * (#V + 2 * #E : ℝ) :=
      mul_le_mul_of_nonneg_right hsum (le_of_lt hpos)
    exact le_trans hmul hscale
  · have hV0 : V = ∅ := not_nonempty_iff_eq_empty.1 hV
    subst hV0
    have hS : (0 : ℝ) ≤ (#S : ℝ) := Nat.cast_nonneg _
    have htwo : (0 : ℝ) ≤ (2 : ℝ) := by norm_num
    have hEn : (0 : ℝ) ≤ (#E : ℝ) := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ (#S : ℝ) * ((2 : ℝ) * (#E : ℝ)) :=
      mul_nonneg hS (mul_nonneg htwo hEn)
    simpa using this

end E624R21CW

namespace Erdos624
open Finset

theorem caro_wei_independence_bound {α : Type*} [DecidableEq α]
    (V : Finset α) (E : Finset (Finset α))
    (hE : ∀ e ∈ E, #e = 2 ∧ e ⊆ V) :
    ∃ S ⊆ V, (∀ e ∈ E, ¬ e ⊆ S) ∧
      (#V : ℝ) ^ 2 ≤ (#S : ℝ) * (#V + 2 * #E : ℝ) :=
  E624R21CW.caro_wei_independence_bound V E hE

end Erdos624

open Finset

theorem solution {α : Type*} [DecidableEq α]
    (V : Finset α) (E : Finset (Finset α))
    (hE : ∀ e ∈ E, #e = 2 ∧ e ⊆ V) :
    ∃ S ⊆ V, (∀ e ∈ E, ¬ e ⊆ S) ∧
      (#V : ℝ) ^ 2 ≤ (#S : ℝ) * (#V + 2 * #E : ℝ) :=
  Erdos624.caro_wei_independence_bound V E hE

