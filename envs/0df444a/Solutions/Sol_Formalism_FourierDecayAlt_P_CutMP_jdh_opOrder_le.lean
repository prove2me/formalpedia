-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.jdh_opOrder_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:08:51.472833+00:00
-- url     : https://prove2.me/submissions/53cc1477-09d9-4445-a2da-9bcb249fa8ae

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatOpA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ZinvBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CutJDHatPolyOK

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP
noncomputable section
open scoped ContDiff
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.FourierDecayAlt.P.CutMP
theorem _root_.solution {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (o : ℕ) (Θ : B.DiffOp k r Wp Wq)
    (h : ∀ Tm ∈ Θ, Tm.word.length ≤ o) : B.opOrder Θ ≤ o := by
  unfold B.opOrder
  induction Θ with
  | nil => simp
  | cons T Θ ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h T (List.mem_cons_self ..)) (ih fun Tm hTm => h Tm (List.mem_cons_of_mem _ hTm))
end Formalism.FourierDecayAlt.P.CutMP
