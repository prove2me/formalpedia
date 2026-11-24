-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:59:48.992263+00:00
-- url     : https://prove2.me/submissions/e54a1ea0-bbcf-4d88-892f-aae3bf6d2414

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliWordSumExpansion
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B5
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
theorem _root_.solution {f₁ f₂ : Mat k r → E} {U : Set (Mat k r)} (hU : IsOpen U) {g X : Mat k r} (hg : g ∈ U)
    (hgG : g ∈ GV k r) (hX : inLie k r X) (he : ∀ x ∈ U, x ∈ GV k r → f₁ x = f₂ x) :
    RdV X f₁ g = RdV X f₂ g := by
  have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt g X 0
  have hγ0 : g * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = g := by simp
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), g * NormedSpace.exp ((t : ℂ) • X) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hg)
  show deriv (fun t : ℝ => f₁ (g * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f₂ (g * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hmem] with t ht
  exact he _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hgG hX t)
end Formalism.FourierDecayAlt.P.CapelliWordSumExpansion
