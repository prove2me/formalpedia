-- Prove2me | solution 1 for Formalism.L2.LamCM.LemmaG_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:28:35.332319+00:00
-- url     : https://prove2.me/submissions/f8f6d0d0-b881-43cb-8e8a-14eefa15f91b

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementG
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ExistsEvalNeZeroOfTotalDegreeLt
import Theorems.Thm_Formalism_L2_LamCM_coeffIntegralOfUnitEval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open MvPolynomial IsLocalRing
namespace Formalism.L2.LamCM
theorem _root_.solution : BigResExt → LemmaG := by
  intro hB V K _ _ _ _ _ _ B _ m P hc hfin hW μ
  classical
  obtain ⟨W, _, _, _, _, hcW, hfinW, hN, hinj, hloc⟩ := hB V hc hfin (P.totalDegree + ∑ b, m b)
  have hg : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap V W)) :=
    (IsFractionRing.injective W (FractionRing W)).comp hinj
  let f : K →+* FractionRing W := IsFractionRing.lift hg
  have hf : ∀ a : V, f (algebraMap V K a) = algebraMap W (FractionRing W) (algebraMap V W a) :=
    fun a => IsFractionRing.lift_algebraMap hg a
  have hdeg : (map f P).totalDegree ≤ P.totalDegree := by
    unfold totalDegree
    exact Finset.sup_mono (support_map_subset f P)
  have hcoef := coeffIntegralOfUnitEval W (FractionRing W) B m (map f P) (Or.inr (by omega))
    (hW W (FractionRing W) f hcW hfinW hloc hf) μ
  rw [coeff_map] at hcoef
  obtain ⟨w, hw⟩ := hcoef
  set x := coeff μ P
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [hx0, map_zero]⟩
  rcases ValuationRing.isInteger_or_isInteger V x with ⟨r, hr⟩ | ⟨y, hy⟩
  · exact ⟨r, hr⟩
  · by_cases hyu : IsUnit y
    · refine ⟨↑hyu.unit⁻¹, ?_⟩
      have h1 : algebraMap V K y * algebraMap V K ↑hyu.unit⁻¹ = 1 := by
        rw [← map_mul, ← map_one (algebraMap V K)]
        congr 1
        exact hyu.mul_val_inv
      rw [hy] at h1
      rw [← inv_inv x]
      exact (eq_inv_of_mul_eq_one_right h1)
    · exfalso
      apply hyu
      apply isUnit_of_map_unit (algebraMap V W) y
      have h1 : algebraMap W (FractionRing W) (w * algebraMap V W y) = algebraMap W (FractionRing W) 1 := by
        rw [map_mul, hw, ← hf, hy, ← map_mul, mul_inv_cancel₀ hx0, map_one, map_one]
      have h2 := IsFractionRing.injective W (FractionRing W) h1
      exact ⟨⟨algebraMap V W y, w, by rw [mul_comm]; exact h2, h2⟩, rfl⟩
end Formalism.L2.LamCM
