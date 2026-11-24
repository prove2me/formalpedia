-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x1.pull_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:22:43.302503+00:00
-- url     : https://prove2.me/submissions/85b54e18-6c7d-4549-8b76-71b9d61e2c42

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_BlochKatoDuality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_lmulM_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_inc_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_inc_memb
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x1_inc_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x1
variable {k r : ℕ}
variable {U : Set (Mat k r)} {hU : IsClosedSubgroup U}
namespace Formalism.FourierDecayAlt.P.B2x1
theorem _root_.solution (μ : Measure (Mt k r)) (h : ∀ a ∈ U, μ.map (lmulM a) = μ) : (pull hU μ).IsMulLeftInvariant := by
  refine ⟨fun g => ?_⟩
  ext s hs
  rw [Measure.map_apply (continuous_const_mul g).measurable hs, pull, inc_memb.comap_apply, inc_memb.comap_apply]
  have e1 : (μ.map (lmulM (Matrix.of (inc g)))) (inc '' s) = μ (inc '' s) :=
    congrArg (fun m : Measure (Mt k r) => m (inc '' s)) (h (Matrix.of (inc g)) (inc_mem g))
  have e2 := Measure.map_apply (μ := μ) (lmulM_cont (Matrix.of (inc g))).measurable (inc_memb.measurableSet_image.2 hs)
  rw [← e1, e2]
  congr 1
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g * y, hy, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    refine ⟨g⁻¹ * z, ?_, ?_⟩
    · show g * (g⁻¹ * z) ∈ s
      rw [mul_inv_cancel_left]; exact hz
    · rw [inc_mul, hzx]
      exact Matrix.nonsing_inv_mul_cancel_left (Matrix.of (inc g) : Mat k r) (Matrix.of x : Mat k r) (hU.unit _ (inc_mem g))
end Formalism.FourierDecayAlt.P.B2x1
