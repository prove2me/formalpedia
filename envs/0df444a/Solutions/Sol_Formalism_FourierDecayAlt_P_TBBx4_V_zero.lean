-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx4.V_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:29.373664+00:00
-- url     : https://prove2.me/submissions/99c37478-99c1-461b-989a-20a23777fcff

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularityAtPlaceOfSubadditive

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx4
open MeasureTheory Filter Topology Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB
open scoped ENNReal ComplexConjugate
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
namespace Formalism.FourierDecayAlt.P.TBBx4
theorem _root_.solution (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) {γ : C.LPt}
    (hγ : ¬ (D.IsLocPt γ (P.r + 1) ∧ 0 < Gp p γ)) : p.V F γ = 0 := by
  unfold KB.Pl.V D.vecV
  exact dif_neg hγ
end Formalism.FourierDecayAlt.P.TBBx4
