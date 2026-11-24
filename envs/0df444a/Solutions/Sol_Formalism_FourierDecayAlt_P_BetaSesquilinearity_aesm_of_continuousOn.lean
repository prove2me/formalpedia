-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BetaSesquilinearity.aesm_of_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:51:42.923926+00:00
-- url     : https://prove2.me/submissions/2854c533-1623-43e9-a1c3-9fe26d3d8e1b

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_gv_closed

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
theorem _root_.solution (D : RealPlaceData k r Wp Wq) {f : Mat k r → E} (hf : ContinuousOn f (GV k r)) :
    AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) D.μG := by
  have hcl : IsClosed (GV k r : Set (Mt k r)) := gv_closed
  have h1 : AEStronglyMeasurable (fun g : Mt k r => f (Matrix.of g)) (D.μG.restrict (GV k r : Set (Mt k r))) :=
    ContinuousOn.aestronglyMeasurable (α := Mt k r) (f := fun g : Mt k r => f (Matrix.of g))
      (s := (GV k r : Set (Mt k r))) hf (IsClosed.measurableSet (α := Mt k r) hcl)
  have h2 : D.μG.restrict (GV k r : Set (Mt k r)) = D.μG :=
    Measure.restrict_eq_self_of_ae_mem (by
      have := D.haarG.conc
      rw [ae_iff]
      exact this)
  rwa [h2] at h1
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
