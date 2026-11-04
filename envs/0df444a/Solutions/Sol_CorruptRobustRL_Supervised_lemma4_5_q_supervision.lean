-- Prove2me | solution 1 for CorruptRobustRL.Supervised.lemma4_5_q_supervision
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T22:17:00.218239+00:00
-- url     : https://prove2.me/submissions/7ce93f06-9c81-471e-9af7-37439704cc0e

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

open CorruptRobustRL.Supervised
open Finset QSupervisor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace CRRL_L45

variable {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]

theorem Vstar_eq_sup (M : NominalMDP X A) (H h : ℕ) (hh : h < H) (x : X) :
    Vstar M H h x = univ.sup' univ_nonempty (Qstar M H h x) := by
  unfold Vstar Qstar
  rw [show H - h = (H - (h + 1)) + 1 by omega, VstarRem]
  rfl

theorem Qstar_le_Vstar (M : NominalMDP X A) (H h : ℕ) (hh : h < H) (x : X) (a : A) :
    Qstar M H h x a ≤ Vstar M H h x := by
  rw [Vstar_eq_sup M H h hh x]; exact Finset.le_sup' _ (mem_univ a)

theorem exists_opt (M : NominalMDP X A) (H h : ℕ) (hh : h < H) (x : X) :
    ∃ a, a ∈ optActions M H h x := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) (Qstar M H h x)
  refine ⟨a, ?_⟩
  unfold optActions
  simp only [Finset.mem_filter, mem_univ, true_and]
  rw [Vstar_eq_sup M H h hh x, ha]

theorem mem_opt (M : NominalMDP X A) (H h : ℕ) (x : X) (a : A) (ha : a ∈ optActions M H h x) :
    Qstar M H h x a = Vstar M H h x := by
  unfold optActions at ha
  simpa using ha

theorem opt_key (M : NominalMDP X A) (H : ℕ)
    (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (hadm : IsAdmissible M H (ucbviSup H act gl sb sel)) (h : ℕ) (hh : h < H) (x : X)
    (a0 : A) (ha0 : a0 ∈ optActions M H h x) :
    a0 ∈ act h x ∧ CorruptRobustRL.Supervised.maxOn (act h x) ((ucbviSup H act gl sb sel).Qlow h x) ≤
      (ucbviSup H act gl sb sel).Qbar h x a0 := by
  obtain ⟨hsub, hQ⟩ := hadm h hh x
  refine ⟨hsub ha0, ?_⟩
  have hstar := mem_opt M H h x a0 ha0
  unfold CorruptRobustRL.Supervised.maxOn
  split_ifs with hne
  · apply Finset.sup'_le
    intro a _
    calc (ucbviSup H act gl sb sel).Qlow h x a ≤ Qstar M H h x a := (hQ a).1
      _ ≤ Vstar M H h x := Qstar_le_Vstar M H h hh x a
      _ = Qstar M H h x a0 := hstar.symm
      _ ≤ _ := (hQ a0).2
  · exact absurd ⟨a0, hsub ha0⟩ hne

/-- For an admissible learner the filtered set is nonempty, so `nextAct` is the filter. -/
theorem nextAct_spec (M : NominalMDP X A) (H : ℕ)
    (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (hadm : IsAdmissible M H (ucbviSup H act gl sb sel)) (h : ℕ) (hh : h < H) (x : X) (a : A) :
    a ∈ nextAct H act gl sb sel h x ↔ a ∈ act h x ∧
      CorruptRobustRL.Supervised.maxOn (act h x) ((ucbviSup H act gl sb sel).Qlow h x) ≤
        (ucbviSup H act gl sb sel).Qbar h x a := by
  obtain ⟨a0, ha0⟩ := exists_opt M H h hh x
  have k0 := opt_key M H act gl sb sel hadm h hh x a0 ha0
  unfold nextAct
  dsimp only
  split_ifs with hs
  · rw [Finset.mem_filter]
  · exact absurd ⟨a0, by rw [Finset.mem_filter]; exact k0⟩ hs

theorem layerAct_succ (H ℓmax : ℕ) (E : EpisodeEst X A) (sel : Selector A) (d : ℕ)
    (hd : d + 1 ≤ ℓmax) :
    layerAct H ℓmax E sel (ℓmax - (d + 1)) =
      nextAct H (layerAct H ℓmax E sel (ℓmax - d)) (E.gl (ℓmax - d)) (E.sb (ℓmax - d)) sel := by
  unfold layerAct
  rw [show ℓmax - (ℓmax - (d + 1)) = d + 1 by omega, show ℓmax - (ℓmax - d) = d by omega]
  rfl

theorem layerAct_nonempty (H ℓmax : ℕ) (E : EpisodeEst X A) (sel : Selector A) (ℓ h : ℕ) (x : X) :
    (layerAct H ℓmax E sel ℓ h x).Nonempty := by
  unfold layerAct
  generalize ℓmax - ℓ = d
  induction d generalizing h x with
  | zero => exact univ_nonempty
  | succ d ih =>
    simp only [layerActAux]
    unfold nextAct
    dsimp only
    split_ifs with hs
    · exact hs
    · exact ih h x


theorem nextAct_sub (H : ℕ) (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (h : ℕ) (x : X) : nextAct H act gl sb sel h x ⊆ act h x := by
  unfold nextAct
  dsimp only
  split_ifs
  · exact Finset.filter_subset _ _
  · exact subset_refl _

theorem aux_anti (H ℓmax : ℕ) (E : EpisodeEst X A) (sel : Selector A) (d : ℕ) :
    ∀ k h x, layerActAux H ℓmax E sel (d + k) h x ⊆ layerActAux H ℓmax E sel d h x := by
  intro k
  induction k with
  | zero => intro h x; exact subset_refl _
  | succ k ih =>
    intro h x
    rw [← add_assoc]
    exact subset_trans (nextAct_sub H _ _ _ sel h x) (ih h x)

theorem le_maxOn (s : Finset A) (f : A → ℝ) (a : A) (ha : a ∈ s) :
    f a ≤ CorruptRobustRL.Supervised.maxOn s f := by
  unfold CorruptRobustRL.Supervised.maxOn
  rw [dif_pos ⟨a, ha⟩]
  exact Finset.le_sup' f ha

theorem plaus_of_le (M : NominalMDP X A) (H ℓmax : ℕ) (E : EpisodeEst X A) (sel : Selector A)
    (hsel : IsArgmaxSelector sel) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓm : ℓ ≤ ℓmax)
    (hadm : IsAdmissible M H (layerSup H ℓmax E sel ℓ)) (ℓ' : ℕ) (hℓ' : ℓ' ≤ ℓ)
    (h : ℕ) (hh : h < H) (x : X) :
    (layerSup H ℓmax E sel ℓ').ucb h x ∈ plaus (layerSup H ℓmax E sel ℓ) h x := by
  set T := layerSup H ℓmax E sel ℓ with hT
  have hpl : ∀ a, a ∈ layerAct H ℓmax E sel ℓ h x →
      CorruptRobustRL.Supervised.maxOn (layerAct H ℓmax E sel ℓ h x) (T.Qlow h x) ≤ T.Qbar h x a →
      a ∈ plaus T h x := by
    intro a ha hm
    simp only [plaus, Finset.mem_filter]
    exact ⟨ha, fun a' ha' => le_trans (le_maxOn _ _ a' ha') hm⟩
  obtain ⟨a0, ha0⟩ := exists_opt M H h hh x
  have k0 := opt_key M H _ _ _ sel hadm h hh x a0 ha0
  rcases eq_or_lt_of_le hℓ' with heq | hlt
  · subst heq
    have hs := hsel (layerAct H ℓmax E sel ℓ' h x) (fun a => T.Qbar h x a) ⟨a0, k0.1⟩
    exact hpl _ hs.1 (le_trans k0.2 (hs.2 a0 k0.1))
  · have hmem : (layerSup H ℓmax E sel ℓ').ucb h x ∈ layerAct H ℓmax E sel ℓ' h x :=
      (hsel _ _ (layerAct_nonempty H ℓmax E sel ℓ' h x)).1
    have hsub : layerAct H ℓmax E sel ℓ' h x ⊆ layerAct H ℓmax E sel (ℓmax - ((ℓmax - ℓ) + 1)) h x := by
      unfold layerAct
      have := aux_anti H ℓmax E sel (ℓmax - (ℓmax - ((ℓmax - ℓ) + 1))) (ℓ - 1 - ℓ') h x
      rwa [show ℓmax - (ℓmax - ((ℓmax - ℓ) + 1)) + (ℓ - 1 - ℓ') = ℓmax - ℓ' by omega] at this
    rw [layerAct_succ H ℓmax E sel (ℓmax - ℓ) (by omega),
      show ℓmax - (ℓmax - ℓ) = ℓ by omega] at hsub
    have := (nextAct_spec M H _ _ _ sel hadm h hh x _).1 (hsub hmem)
    exact hpl _ this.1 this.2

theorem stepProb_ne_zero (H ℓmax f n : ℕ) (h : stepProb H ℓmax f n ≠ 0) : f ≤ n := by
  by_contra hc
  apply h
  unfold stepProb
  rw [if_neg (by omega), if_neg (by omega)]

theorem lay_mono (H ℓmax : ℕ) (s : Sched H ℓmax) (hs : schedWeight s ≠ 0) :
    ∀ k t (ht : t + k < H), s.lay ⟨t, by omega⟩ ≤ s.lay ⟨t + k, ht⟩ := by
  have hf : ∀ t : Fin H, stepProb H ℓmax
      (if (t : ℕ) = 0 then 1
        else s.lay ⟨(t : ℕ) - 1, lt_of_le_of_lt (Nat.sub_le _ _) t.isLt⟩) (s.lay t) ≠ 0 := by
    intro t
    exact (Finset.prod_ne_zero_iff.mp hs) t (mem_univ t)
  intro k
  induction k with
  | zero => intro t ht; exact le_rfl
  | succ k ih =>
    intro t ht
    refine le_trans (ih t (by omega)) ?_
    have := stepProb_ne_zero _ _ _ _ (hf ⟨t + (k + 1), ht⟩)
    simp only at this
    rw [if_neg (by omega)] at this
    simpa [show t + (k + 1) - 1 = t + k by omega] using this

theorem lay_le_last (H ℓmax : ℕ) (s : Sched H ℓmax) (hs : schedWeight s ≠ 0) (t : Fin H) :
    s.lay t ≤ s.last := by
  unfold Sched.last
  rw [dif_pos (by have := t.isLt; omega)]
  have := lay_mono H ℓmax s hs (H - 1 - t) t (by have := t.isLt; omega)
  simpa [show (t : ℕ) + (H - 1 - t) = H - 1 by have := t.isLt; omega] using this

theorem supervised_gen (M : NominalMDP X A) (H ℓmax : ℕ) (E : EpisodeEst X A) (sel : Selector A)
    (hsel : IsArgmaxSelector sel) (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓm : ℓ ≤ ℓmax)
    (hadm : IsAdmissible M H (layerSup H ℓmax E sel ℓ)) (s : Sched H ℓmax)
    (hs : schedWeight s ≠ 0) (hl : s.last ≤ ℓ) (h : ℕ) (hh : h < H) (x : X) :
    schedPolicy (basePolicies H ℓmax E sel) s h x ∈ plaus (layerSup H ℓmax E sel ℓ) h x := by
  unfold schedPolicy
  rw [dif_pos hh]
  exact plaus_of_le M H ℓmax E sel hsel ℓ hℓ1 hℓm hadm _
    (le_trans (lay_le_last H ℓmax s hs ⟨h, hh⟩) hl) h hh x

end CRRL_L45

open CRRL_L45 in
theorem solution
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H ℓmax : ℕ) (hH : 1 ≤ H)
    (E : EpisodeEst X A) (sel : Selector A) (hsel : IsArgmaxSelector sel) :
    (∀ lst, 1 ≤ lst → lst ≤ ℓmax → IsAdmissible M H (layerSup H ℓmax E sel lst) →
      IsQSupervised H (masterLe H ℓmax (basePolicies H ℓmax E sel) lst)
        (layerSup H ℓmax E sel lst)) ∧
    (∀ ℓ, 1 ≤ ℓ → ℓ ≤ ℓmax → IsAdmissible M H (layerSup H ℓmax E sel ℓ) →
      IsQSupervised H (masterEq H ℓmax (basePolicies H ℓmax E sel) ℓ)
        (layerSup H ℓmax E sel ℓ)) := by
  constructor
  · intro lst h1 h2 hadm s hw h hh x
    change 0 < (if s.last ≤ lst then schedWeight s / qLe H ℓmax lst else 0) at hw
    split_ifs at hw with hl
    · have hs : schedWeight s ≠ 0 := by
        intro h0; rw [h0, zero_div] at hw; exact lt_irrefl _ hw
      exact supervised_gen M H ℓmax E sel hsel lst h1 h2 hadm s hs hl h hh x
    · exact absurd hw (lt_irrefl _)
  · intro ℓ h1 h2 hadm s hw h hh x
    change 0 < (if s.last = ℓ then schedWeight s / q H ℓmax ℓ else 0) at hw
    split_ifs at hw with hl
    · have hs : schedWeight s ≠ 0 := by
        intro h0; rw [h0, zero_div] at hw; exact lt_irrefl _ hw
      exact supervised_gen M H ℓmax E sel hsel ℓ h1 h2 hadm s hs hl.le h hh x
    · exact absurd hw (lt_irrefl _)
