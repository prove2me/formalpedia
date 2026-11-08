-- Prove2me | solution 1 for CorrelatedRounding.integral_p12
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:30:27.427205+00:00
-- url     : https://prove2.me/submissions/09e938fb-2512-46ce-ac25-e1d50932072e

import Mathlib

theorem solution (q : ℕ) (hq : 1 ≤ q) :
    (∫ t in Set.Ioi (0 : ℝ), min ((q : ℝ) * Real.exp (-t)) 1) =
        Real.log q + ∫ t in Set.Ioi (Real.log q), (q : ℝ) * Real.exp (-t) ∧
      Real.log q + (∫ t in Set.Ioi (Real.log q), (q : ℝ) * Real.exp (-t)) =
        Real.log q + q * Real.exp (-Real.log q) ∧
      Real.log q + q * Real.exp (-Real.log q) = 1 + Real.log q := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hcont : Continuous (fun t : ℝ => min ((q : ℝ) * Real.exp (-t)) 1) :=
    (continuous_const.mul (Real.continuous_exp.comp continuous_neg)).min continuous_const
  have hint : MeasureTheory.IntegrableOn (fun t : ℝ => (q : ℝ) * Real.exp (-t))
      (Set.Ioi (Real.log q)) :=
    (integrableOn_exp_neg_Ioi _).const_mul _
  have hexp : (q : ℝ) * Real.exp (-Real.log q) = 1 := by
    rw [Real.exp_neg, Real.exp_log hq0]; field_simp
  have hI : (∫ t in Set.Ioi (Real.log q), (q : ℝ) * Real.exp (-t)) =
      q * Real.exp (-Real.log q) := by
    rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]
  refine ⟨?_, by rw [hI], by rw [hexp]; ring⟩
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 (Real.log q) ∪ Set.Ioi (Real.log q) :=
    (Set.Ioc_union_Ioi_eq_Ioi hlog).symm
  rw [hsplit, MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (hint.congr_fun (fun t ht => ?_) measurableSet_Ioi)]
  · congr 1
    · have : (∫ t in Set.Ioc 0 (Real.log q), min ((q : ℝ) * Real.exp (-t)) 1) =
          ∫ t in Set.Ioc 0 (Real.log q), (1 : ℝ) := by
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
        apply min_eq_right
        have : Real.exp (-Real.log q) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith [ht.2])
        nlinarith
      rw [this, MeasureTheory.setIntegral_const]
      simp [hlog]
    · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      apply min_eq_left
      have : Real.exp (-t) ≤ Real.exp (-Real.log q) :=
        Real.exp_le_exp.mpr (by linarith [Set.mem_Ioi.mp ht])
      nlinarith
  · simp only
    symm
    apply min_eq_left
    have : Real.exp (-t) ≤ Real.exp (-Real.log q) :=
      Real.exp_le_exp.mpr (by linarith [Set.mem_Ioi.mp ht])
    nlinarith
