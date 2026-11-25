-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBL.rr_eq_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:14:30.481564+00:00
-- url     : https://prove2.me/submissions/ccd289f1-0dd8-4eb6-9c10-6ae7e3fd713a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormPos
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeNeZeroComplex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBL
open Formalism.FourierDecayAlt NumberField MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.PBD
open scoped ComplexConjugate
noncomputable section
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}
namespace Formalism.FourierDecayAlt.P.PBL
theorem _root_.solution (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (j : ℕ) (hj : j ≤ P.r)
    (w : List C.Letter) (a b : C.LPt) (ha : D.IsLocPt a j) (hb : D.IsLocPt b j) :
    p.RR F j w a b = p.form j hj w (KB.slv p.T F j hj w a ha.2) (KB.slv p.T F j hj w b hb.2) := by
  unfold KB.Pl.RR D.RRplace
  rw [dif_pos (⟨ha, hb⟩ : D.IsLocPt a j ∧ D.IsLocPt b j), dif_pos hj]
  rfl
end Formalism.FourierDecayAlt.P.PBL
