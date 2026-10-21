-- Prove2me | solution 1 for CustAssort.AugGreedy.lemma_E_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T19:35:02.308257+00:00
-- url     : https://prove2.me/submissions/19a3e6cf-67f7-4dac-8ae2-2c60a063ba17

import Mathlib
import Definitions.Def_CustAssort_AugGreedy_Setting

set_option autoImplicit false

namespace ThresholdBound
open ChoiceCDLP.MNL

theorem sum_threshold {ι : Type*} [DecidableEq ι] (U A : Finset ι)
    (w r : ι → ℝ) (z : ℝ) (hA : A ⊆ U) (hw : ∀ i ∈ U, 0 ≤ w i) :
    (∑ i ∈ A, (r i - z) * w i) ≤
      ∑ i ∈ U.filter (fun i => z ≤ r i), (r i - z) * w i := by
  classical
  have hterm : ∀ i ∈ U, (r i - z) * w i ≤
      if z ≤ r i then (r i - z) * w i else 0 := by
    intro i hi
    split_ifs with h
    · rfl
    · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge h)) (hw i hi)
  have hnonneg : ∀ i ∈ U, 0 ≤
      if z ≤ r i then (r i - z) * w i else 0 := by
    intro i hi
    split_ifs with h
    · exact mul_nonneg (sub_nonneg.mpr h) (hw i hi)
    · rfl
  rw [Finset.sum_filter]
  exact (Finset.sum_le_sum (fun i hi => hterm i (hA hi))).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hA (fun i hi _ => hnonneg i hi))

theorem threshold_optimal {ι : Type*} [DecidableEq ι] (U : Finset ι)
    (w r : ι → ℝ) (hw : ∀ i ∈ U, 0 ≤ w i) :
    let z := U.powerset.sup' (Finset.powerset_nonempty U) (mnlObjective w r 1)
    mnlObjective w r 1 (U.filter (fun i => z ≤ r i)) = z := by
  classical
  intro z
  have hden (T : Finset ι) (hT : T ⊆ U) : 0 < (∑ i ∈ T, w i) + 1 := by
    have := Finset.sum_nonneg (fun i hi => hw i (hT hi))
    linarith
  have hupper (T : Finset ι) (hT : T ⊆ U) : mnlObjective w r 1 T ≤ z :=
    Finset.le_sup' _ (Finset.mem_powerset.mpr hT)
  obtain ⟨A, hAU, hAz⟩ := Finset.exists_mem_eq_sup'
    (Finset.powerset_nonempty U) (mnlObjective w r 1)
  have hA := Finset.mem_powerset.mp hAU
  change z = mnlObjective w r 1 A at hAz
  have heq : (∑ i ∈ A, r i * w i) = z * ((∑ i ∈ A, w i) + 1) := by
    exact (div_eq_iff (ne_of_gt (hden A hA))).mp hAz.symm
  have hgap : (∑ i ∈ A, (r i - z) * w i) = z := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    nlinarith [heq]
  have hs := sum_threshold U A w r z hA hw
  rw [hgap] at hs
  have hb : U.filter (fun i => z ≤ r i) ⊆ U := Finset.filter_subset _ _
  apply le_antisymm (hupper _ hb)
  unfold mnlObjective
  apply (le_div_iff₀ (hden _ hb)).2
  simp_rw [sub_mul] at hs
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  nlinarith

theorem monotone_value {n m : ℕ} (v : Fin n → Fin m → ℝ) (r : Fin n → ℝ)
    (j : Fin m) (A B : Finset (Fin n)) (hAB : A ⊆ B) :
    CustAssort.AugGreedy.fj v r j A ≤ CustAssort.AugGreedy.fj v r j B := by
  apply Finset.sup'_le
  intro T hT
  exact Finset.le_sup' _ (Finset.mem_powerset.mpr
    (Finset.Subset.trans (Finset.mem_powerset.mp hT) hAB))

end ThresholdBound

theorem solution {ι : Type*} [DecidableEq ι] (U : Finset ι) (w r : ι → ℝ)
    (hw : ∀ i ∈ U, 0 ≤ w i) :
    let zstar := U.powerset.sup' (Finset.powerset_nonempty U)
      (ChoiceCDLP.MNL.mnlObjective w r 1)
    ChoiceCDLP.MNL.mnlObjective w r 1 (U.filter (fun i => zstar ≤ r i)) = zstar := by
  exact ThresholdBound.threshold_optimal U w r hw

#print axioms solution
