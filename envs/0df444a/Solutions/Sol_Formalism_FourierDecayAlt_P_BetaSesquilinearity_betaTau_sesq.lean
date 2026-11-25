-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.betaTau_sesq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:22:34.693362+00:00
-- url     : https://prove2.me/submissions/145aefc5-7e5d-45e1-97a5-de4541e071f1

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_betaTau_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_int_inner
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Jv_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Jv_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
variable {D : RealPlaceData k r Wp Wq} {A : ℝ}
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (hJ : JCont D A) (hDD : DiagDom D A) {τ : ℝ × ℝ} (hτ : τ ∈ Quad) :
    SesqOn (InCC A 4) (betaTau D τ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x x' y hx hx' hy
    rw [betaTau_eq, betaTau_eq, betaTau_eq, ← integral_add (int_inner hJ hDD hx hy hτ) (int_inner hJ hDD hx' hy hτ)]
    refine integral_congr_ae ?_
    filter_upwards [Jv_add hJ hx hx' τ] with q h
    rw [h, inner_add_right]
  · intro x y y' hx hy hy'
    rw [betaTau_eq, betaTau_eq, betaTau_eq, ← integral_add (int_inner hJ hDD hx hy hτ) (int_inner hJ hDD hx hy' hτ)]
    refine integral_congr_ae ?_
    filter_upwards [Jv_add hJ hy hy' τ] with q h
    rw [h, inner_add_left]
  · intro a x y _ _
    rw [betaTau_eq, betaTau_eq, ← integral_const_mul]
    congr 1
    funext q
    rw [Jv_smul, inner_smul_right]
  · intro a x y _ _
    rw [betaTau_eq, betaTau_eq, ← integral_const_mul]
    congr 1
    funext q
    rw [Jv_smul, inner_smul_left]
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
