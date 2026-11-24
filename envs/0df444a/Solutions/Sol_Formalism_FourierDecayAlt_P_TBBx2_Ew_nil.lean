-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.Ew_nil
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:09:44.232926+00:00
-- url     : https://prove2.me/submissions/c9d02021-b910-4a20-b5dd-becc9555ed21

import Definitions.Def_Formalism_HermitianCurvature_StatementTBB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TriangleInequalityAtPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TBBx2
open MeasureTheory Filter Topology Formalism.QuantumDeterminants
open scoped ENNReal
noncomputable section
variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
namespace Formalism.FourierDecayAlt.P.TBBx2
theorem _root_.solution (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ) (γ : C.LPt) :
    TBB.Ew p nn G i [] γ = TBB.Ew p (fun _ => 1) G i [] γ := by
  simp only [TBB.Ew, TBB.NP, TBB.normC, List.map_nil, List.prod_nil]
end Formalism.FourierDecayAlt.P.TBBx2
