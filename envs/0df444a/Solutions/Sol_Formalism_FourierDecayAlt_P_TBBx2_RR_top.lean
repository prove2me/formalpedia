-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TBBx2.RR_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:56:19.068204+00:00
-- url     : https://prove2.me/submissions/108a3c1d-d339-4f63-a8ee-6580a4562e82

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
theorem _root_.solution (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (γ : C.LPt)
    (hγ : D.IsLocPt γ (P.r + 1)) :
    p.RR G (P.r + 1) [] γ γ = B.hsInner (p.V G γ) (p.V G γ) := by
  have h1 : ¬ (P.r + 1 ≤ P.r) := by omega
  unfold KB.Pl.RR KB.Pl.V D.RRplace
  rw [dif_pos (And.intro hγ hγ), dif_neg h1, if_pos rfl, if_pos rfl]
end Formalism.FourierDecayAlt.P.TBBx2
