-- Prove2me | solution 1 for CurvatureSubmod.LocalSearch.theorem_6_1_local_opt
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-30T19:55:05.343457+00:00
-- url     : https://prove2.me/submissions/ac2fe887-2558-426b-af28-cb1c5b873cbd

import Definitions.Def_NonmonotoneSubmod_Shared_Submodular
import Definitions.Def_CurvatureSubmod_LocalSearch_Setting
import Theorems.Thm_CurvatureSubmod_LocalSearch_local_opt_bound
import Theorems.Thm_CurvatureSubmod_LocalSearch_lemma_A_1
import Theorems.Thm_CurvatureSubmod_LocalSearch_lemma_2_1
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false

open scoped BigOperators
open CurvatureSubmod.LocalSearch

namespace CurvatureSubmodTheorem61

variable {X : Type}

noncomputable def weightKernel (k j : ℕ) : ℝ :=
  ∫ p in (0 : ℝ)..1,
    Real.exp p / (Real.exp 1 - 1) * p ^ k * (1 - p) ^ j

lemma hPot_one_card (A : Finset X) :
    hPot (fun _ : Finset X => (1 : ℝ)) A =
      ∑ k ∈ Finset.range (A.card + 1), (A.card.choose k : ℝ) *
        (if k = 0 then 0 else weightKernel (k - 1) (A.card - k)) := by
  unfold hPot
  rw [Finset.sum_filter]
  trans ∑ B ∈ A.powerset, if B.card = 0 then 0 else weightKernel (B.card - 1) (A.card - B.card)
  · apply Finset.sum_congr rfl
    intro B _
    by_cases hB : B.Nonempty
    · have hcard : B.card ≠ 0 := Nat.ne_of_gt (Finset.card_pos.mpr hB)
      simp [hB, hcard, weightKernel]
    · have hcard : B.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hB)
      simp [hB, hcard]
  · rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_powersetCard k A
      (fun i => if i = 0 then (0 : ℝ) else weightKernel (i - 1) (A.card - i))]
    simp [nsmul_eq_mul]

lemma hPot_one_eq_of_card_eq (A B : Finset X) (h : A.card = B.card) :
    hPot (fun _ : Finset X => (1 : ℝ)) A = hPot (fun _ : Finset X => (1 : ℝ)) B := by
  rw [hPot_one_card, hPot_one_card, h]

lemma hPot_sub_const (g : Finset X → ℝ) (d : ℝ) (A : Finset X) :
    hPot (fun B => g B - d) A = hPot g A - d * hPot (fun _ => 1) A := by
  simp only [hPot, sub_mul, Finset.sum_sub_distrib, one_mul, Finset.mul_sum]

lemma hPot_shift_difference (g : Finset X → ℝ) (d : ℝ)
    (A B : Finset X) (h : A.card = B.card) :
    hPot (fun C => g C - d) A - hPot (fun C => g C - d) B = hPot g A - hPot g B := by
  rw [hPot_sub_const, hPot_sub_const, hPot_one_eq_of_card_eq A B h]
  ring

lemma mono_union [DecidableEq X] {f : Finset X → ℝ} (hmono : MonoInc f) (A D : Finset X) :
    f A ≤ f (A ∪ D) := by
  induction D using Finset.induction_on with
  | empty => simp
  | insert x D _ ih =>
    rw [Finset.union_insert]
    have h := hmono (A ∪ D) x
    unfold marg at h
    linarith

lemma mono_subset [DecidableEq X] {f : Finset X → ℝ} (hmono : MonoInc f)
    {A B : Finset X} (hAB : A ⊆ B) :
    f A ≤ f B := by
  rw [← Finset.union_sdiff_of_subset hAB]
  exact mono_union hmono A (B \ A)

end CurvatureSubmodTheorem61

open CurvatureSubmodTheorem61

theorem solution {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ)
    (hf0 : ∀ A, 0 ≤ f A) (hmono : MonoInc f) (hsub : NonmonotoneSubmod.Shared.Submodular f)
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hcurv : CurvAtMostInc f c)
    (M : Matroid X) (hE : M.E = Set.univ)
    (S : Finset X) (hS : IsSwapLocalOpt M (psi (gMax f) (wMax f)) S)
    (O : Finset X) (hO : M.Indep (↑O : Set X)) :
    (1 - c * Real.exp (-1)) * f O ≤ f S := by
  classical
  obtain ⟨B, hB, hOB⟩ := hO.exists_isBase_superset
  let O' : Finset X := B.toFinset
  have hO' : M.IsBase (↑O' : Set X) := by
    simpa [O'] using hB
  have hOO' : O ⊆ O' := by
    intro x hx
    exact Set.mem_toFinset.mpr (hOB hx)
  let f0 : Finset X → ℝ := fun A => f A - f ∅
  have hf0_empty : f0 ∅ = 0 := sub_self (f ∅)
  have hf0_marg : ∀ A i, marg f0 A i = marg f A i := by
    intro A i
    unfold marg f0
    ring
  have hf0_mono : MonoInc f0 := by
    intro A i
    rw [hf0_marg]
    exact hmono A i
  have hf0_nonneg : ∀ A, 0 ≤ f0 A := by
    intro A
    have h := mono_subset hmono (Finset.empty_subset A)
    unfold f0
    linarith
  have hf0_sub : NonmonotoneSubmod.Shared.Submodular f0 := by
    intro A1 A2
    have h := hsub A1 A2
    unfold f0
    linarith
  have hf0_curv : CurvAtMostInc f0 c := by
    intro j
    rw [hf0_marg, hf0_marg]
    exact hcurv j
  have hwMax_eq : wMax f0 = wMax f := by
    ext j
    exact hf0_marg (Finset.univ.erase j) j
  have hgMax_eq : gMax f0 = fun A => gMax f A - f ∅ := by
    ext A
    unfold gMax f0
    rw [hwMax_eq]
    ring
  have hS0 : IsSwapLocalOpt M (psi (gMax f0) (wMax f0)) S := by
    refine ⟨hS.1, ?_⟩
    intro a ha b hb hbase
    have hprev := hS.2 a ha b hb hbase
    have hbe : b ∉ S.erase a := fun h => hb (Finset.mem_of_mem_erase h)
    have hcard : (insert b (S.erase a)).card = S.card := by
      rw [Finset.card_insert_of_notMem hbe, Finset.card_erase_add_one ha]
    have hshift := hPot_shift_difference (gMax f) (f ∅) (insert b (S.erase a)) S hcard
    have hpsi_diff :
        psi (gMax f0) (wMax f0) (insert b (S.erase a)) - psi (gMax f0) (wMax f0) S =
          psi (gMax f) (wMax f) (insert b (S.erase a)) - psi (gMax f) (wMax f) S := by
      unfold psi
      rw [hgMax_eq, hwMax_eq]
      calc (1 - Real.exp (-1)) * hPot (fun A => gMax f A - f ∅) (insert b (S.erase a)) +
              linFun (wMax f) (insert b (S.erase a)) -
            ((1 - Real.exp (-1)) * hPot (fun A => gMax f A - f ∅) S + linFun (wMax f) S)
        _ = (1 - Real.exp (-1)) *
              (hPot (fun A => gMax f A - f ∅) (insert b (S.erase a)) -
                hPot (fun A => gMax f A - f ∅) S) +
              (linFun (wMax f) (insert b (S.erase a)) - linFun (wMax f) S) := by ring
        _ = (1 - Real.exp (-1)) * (hPot (gMax f) (insert b (S.erase a)) - hPot (gMax f) S) +
              (linFun (wMax f) (insert b (S.erase a)) - linFun (wMax f) S) := by rw [hshift]
        _ = _ := by ring
    linarith
  obtain ⟨hg_sub, hg_mono, hg_nonneg⟩ := lemma_A_1 f0 hf0_nonneg hf0_mono hf0_sub
  have hloc := local_opt_bound (gMax f0) hg_nonneg hg_mono hg_sub (wMax f0) M S hS0 O' hO'
  have hdecomp_S : gMax f0 S + linFun (wMax f0) S = f0 S := sub_add_cancel _ _
  have hloc_rewr : (1 - Real.exp (-1)) * f0 O' + Real.exp (-1) * linFun (wMax f0) O' =
      (1 - Real.exp (-1)) * gMax f0 O' + linFun (wMax f0) O' := by
    unfold gMax
    ring
  have hl21 : (1 - c) * f0 O' ≤ linFun (wMax f0) O' :=
    lemma_2_1 f0 hf0_nonneg hf0_mono hf0_sub c hf0_curv hf0_empty O'
  have hexp_pos : 0 ≤ Real.exp (-1) := (Real.exp_pos (-1)).le
  have hexp_le_one : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hmul_l21 : Real.exp (-1) * ((1 - c) * f0 O') ≤ Real.exp (-1) * linFun (wMax f0) O' :=
    mul_le_mul_of_nonneg_left hl21 hexp_pos
  have hmul_rewr : (1 - Real.exp (-1)) * f0 O' + Real.exp (-1) * ((1 - c) * f0 O') =
      (1 - c * Real.exp (-1)) * f0 O' := by ring
  have hf0_O'_bound : (1 - c * Real.exp (-1)) * f0 O' ≤ f0 S := by
    linarith
  have hOO'_f0 : f0 O ≤ f0 O' := mono_subset hf0_mono hOO'
  have hce_le_one : c * Real.exp (-1) ≤ 1 :=
    mul_le_one₀ hc1 hexp_pos hexp_le_one
  have hcoeff_nonneg : 0 ≤ 1 - c * Real.exp (-1) := sub_nonneg.mpr hce_le_one
  have hf0_O_bound : (1 - c * Real.exp (-1)) * f0 O ≤ f0 S :=
    (mul_le_mul_of_nonneg_left hOO'_f0 hcoeff_nonneg).trans hf0_O'_bound
  have hce_nonneg : 0 ≤ c * Real.exp (-1) := mul_nonneg hc0 hexp_pos
  have hempty_nonneg : 0 ≤ (c * Real.exp (-1)) * f ∅ := mul_nonneg hce_nonneg (hf0 ∅)
  have hfinal_rewr : (1 - c * Real.exp (-1)) * f O =
      (1 - c * Real.exp (-1)) * f0 O + f ∅ - (c * Real.exp (-1)) * f ∅ := by
    unfold f0
    ring
  have hf0_S_eq : f0 S = f S - f ∅ := rfl
  linarith
