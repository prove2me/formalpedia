-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a208_fullcell_discount_positive_square_le_raw_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:13:54.572361+00:00
-- url     : https://prove2.me/submissions/c3459704-7010-4228-b4e6-aaca4c670ccb

import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_avram_ga_a203_finite_stopped_discount_positive_Lipschitz_raw_energy_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a154_original_gaussian_fullcell_raw_source_sum_cauchy_energy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section
/-- Signed stopped source discount positive square is dominated by its original masked raw square energy. -/
theorem solution
 (m : ℕ) (A : ℕ → Prop) [DecidablePred A]
 (a u v R : ℕ → ℝ) (q Δ L : ℝ)
 (hq : 0 ≤ q) (hΔ : 0 ≤ Δ) (hL : 0 ≤ L)
 (hDisc : ∀ i ∈ Finset.range m, -(q*Δ) ≤ a i ∧ a i ≤ 0)
 (hLip : ∀ i ∈ Finset.range m, |u i - v i| ≤ L*|R i|) :
 (max (∑ i ∈ Finset.range m, if A i then a i*(u i-v i) else 0) 0)^2 ≤
   (q*Δ*L)^2 * (m : ℝ) * ∑ i ∈ Finset.range m, (if A i then R i else 0)^2 := by
 classical
 let U : ℕ → ℝ := fun i => if A i then R i else 0
 let F : ℝ := max (∑ i ∈ Finset.range m, if A i then a i*(u i-v i) else 0) 0
 let T : ℝ := ∑ i ∈ Finset.range m, |U i|
 have hF : 0 ≤ F := le_max_right _ _
 have hT : 0 ≤ T := Finset.sum_nonneg (fun i hi => abs_nonneg _)
 have hα : 0 ≤ q*Δ*L := mul_nonneg (mul_nonneg hq hΔ) hL
 have hTExpr :
      T = ∑ i ∈ Finset.range m, if A i then |R i| else 0 := by
   dsimp [T, U]
   apply Finset.sum_congr rfl
   intro i hi
   split_ifs <;> simp
 have hb : F ≤ q*Δ*L*T := by
   have hbase :=
     avram_ga_a203_finite_stopped_discount_positive_Lipschitz_raw_energy_bound
       (Finset.range m) A a u v R q Δ L hq hΔ hL hDisc hLip
   simpa only [F, hTExpr] using hbase
 have hc : T^2 ≤ (m : ℝ) * ∑ i ∈ Finset.range m, U i^2 :=
   avram_ga_a154_original_gaussian_fullcell_raw_source_sum_cauchy_energy m U
 have hd : F^2 ≤ (q*Δ*L*T)^2 := by
   nlinarith [mul_nonneg (sub_nonneg.mpr hb)
     (add_nonneg hF (mul_nonneg hα hT))]
 calc
  F^2 ≤ (q*Δ*L*T)^2 := hd
  _ = (q*Δ*L)^2*T^2 := by ring
  _ ≤ (q*Δ*L)^2 * ((m:ℝ)*∑ i ∈ Finset.range m, U i^2) :=
      mul_le_mul_of_nonneg_left hc (sq_nonneg _)
  _ = _ := by simp only [F,U]; ring
