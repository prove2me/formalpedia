-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveOrbitOpen.rdV_local
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:24:53.013693+00:00
-- url     : https://prove2.me/submissions/e453ccb1-1801-46b6-929f-4aaa6982fdd0

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordIntegralScaling
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellZetaMinors
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositiveOrbitOpen
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PositiveOrbitOpen
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.PositiveOrbitOpen
theorem _root_.solution {f₁ f₂ : Mat k r → E} {V : Set (Mat k r)} (hV : IsOpen V)
    (h : ∀ x ∈ V, x ∈ GV k r → f₁ x = f₂ x) {X : Mat k r} (hX : inLie k r X) :
    ∀ x ∈ V, x ∈ GV k r → RdV X f₁ x = RdV X f₂ x := by
  intro x hx hxG
  have hγ := Formalism.FourierDecayAlt.P.B5.curve_hasDerivAt x X 0
  have hγ0 : x * NormedSpace.exp (((0 : ℝ) : ℂ) • X) = x := by simp
  have hmem : ∀ᶠ t : ℝ in 𝓝 (0 : ℝ), x * NormedSpace.exp ((t : ℂ) • X) ∈ V :=
    hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hV.mem_nhds hx)
  show deriv (fun t : ℝ => f₁ (x * NormedSpace.exp ((t : ℂ) • X))) 0 =
    deriv (fun t : ℝ => f₂ (x * NormedSpace.exp ((t : ℂ) • X))) 0
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hmem] with t ht
  exact h _ ht (Formalism.FourierDecayAlt.P.B5.curve_mem hxG hX t)
end Formalism.FourierDecayAlt.P.PositiveOrbitOpen
