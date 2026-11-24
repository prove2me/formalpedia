-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BigCellOpenDomain.c_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:12:59.870068+00:00
-- url     : https://prove2.me/submissions/8c7b046f-071a-432a-a014-d587d01ea218

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordKeyIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellOpenDomain

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BigCellOpenDomain
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
namespace Formalism.FourierDecayAlt.P.BigCellOpenDomain
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (n : ℕ) (a : Fin r) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => (star (q.1 a))⁻¹) (QDom k r z z') := by
  have h0 : ContDiff ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => q.1 a) :=
    (contDiff_apply ℝ ℂ a).comp contDiff_fst
  have hc : ContDiff ℝ (n : WithTop ℕ∞) (fun q : (Fin r → ℂ) × ℂ => star (q.1 a)) :=
    Complex.conjCLE.contDiff.comp h0
  exact hc.contDiffOn.inv (fun q hq => star_ne_zero.2 ((show (∀ a, q.1 a ≠ 0) ∧ _ from hq).1 a))
end Formalism.FourierDecayAlt.P.BigCellOpenDomain
