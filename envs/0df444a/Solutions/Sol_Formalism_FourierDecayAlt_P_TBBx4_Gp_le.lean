-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx4.Gp_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:58:45.795121+00:00
-- url     : https://prove2.me/submissions/f2d3803d-00e5-484b-b73b-177fe5d90b7f

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
theorem _root_.solution (p : KB.Pl P Wp Wq) (γ : C.LPt) : Gp p γ ≤ ‖(D.ptMatN γ (P.r + 1)).det‖ ^ 2 := by
  have hT : 0 ≤ TTp p := (mul_pos p.T.base.T_pos p.T.base.T'_pos).le
  have e := Complex.normSq_eq_norm_sq (D.ptMatN γ (P.r + 1)).det
  have h0 := Complex.normSq_nonneg (D.ptMatN γ P.r).det
  unfold Gp D.ptG
  nlinarith [mul_nonneg hT h0]
end Formalism.FourierDecayAlt.P.TBBx4
