-- Prove2me | solution 1 for CompanionTheory.D.Inhab.HWRep.D_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:28:56.563189+00:00
-- url     : https://prove2.me/submissions/44ee5f31-3b12-4800-b74c-ffc17e02a699

import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_NonemptyOfAntitone
import Definitions.Def_CompanionTheory_HarishChandraModules_NonemptyRepresentations_HWRepD
import Theorems.Thm_CompanionTheory_D_Inhab_HWRep_hasDerivAt_curve
import Theorems.Thm_CompanionTheory_D_Inhab_HWRep_curve_deriv
import Theorems.Thm_CompanionTheory_D_Inhab_HWRep_curve_tri

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Inhab CompanionTheory.D.Inhab.HWRep
variable {k : ℕ} {ν : Fin k → ℤ} (R : HWRep k ν)
namespace CompanionTheory.D.Inhab.HWRep
theorem _root_.solution (a : Fin k) : R.D (Matrix.single a a 1) *ᵥ R.v0 = (ν a : ℂ) • R.v0 := by
  have h := R.hasDerivAt_curve (fun t : ℝ => 1 + (t : ℂ) • Matrix.single a a (1 : ℂ)) _ (by simp)
    (curve_deriv a a) R.v0
  have hdiag : ∀ (t : ℂ) c, (1 + t • Matrix.single a a (1 : ℂ) : Matrix (Fin k) (Fin k) ℂ) c c =
      if c = a then 1 + t else 1 := by
    intro t c
    by_cases hc : c = a
    · simp [hc]
    · simp [Matrix.single_apply, hc, Ne.symm hc]
  have h1 : HasDerivAt (fun t : ℝ => (1 : ℂ) + t) 1 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add (1 : ℂ)
  have hne : ∀ᶠ t : ℝ in nhds 0, (1 : ℂ) + t ≠ 0 :=
    h1.continuousAt.eventually_ne (by simp)
  have e : (fun t : ℝ => ((1 : ℂ) + t) ^ ν a • R.v0) =ᶠ[nhds 0]
      fun t : ℝ => R.ρ (1 + (t : ℂ) • Matrix.single a a (1 : ℂ)) *ᵥ R.v0 := by
    filter_upwards [hne] with t ht
    rw [R.hw _ (curve_tri le_rfl _)]
    · congr 1
      simp only [hdiag]
      rw [Finset.prod_eq_single a] <;> simp +contextual
    · rw [Matrix.det_of_upperTriangular (curve_tri le_rfl _)]
      simp only [hdiag]
      exact Finset.prod_ne_zero_iff.2 fun c _ => by split_ifs <;> simp [ht]
  have hz : HasDerivAt (fun x : ℂ => x ^ ν a) (ν a : ℂ) ((1 : ℂ) + ((0 : ℝ) : ℂ)) := by
    simpa using hasDerivAt_zpow (ν a) (1 : ℂ) (Or.inl one_ne_zero)
  have h2 : HasDerivAt (fun t : ℝ => ((1 : ℂ) + t) ^ ν a) (ν a : ℂ) 0 := by
    have := (hz.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) h1
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, one_smul,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply] at this
    exact this
  exact (h.congr_of_eventuallyEq e).unique (h2.smul_const R.v0)
end CompanionTheory.D.Inhab.HWRep
