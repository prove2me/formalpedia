-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBL.rr_zero_of_not
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T06:13:23.143296+00:00
-- url     : https://prove2.me/submissions/aab7b874-c8c7-4136-9c8a-fd301f4fff4f

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
namespace Formalism.FourierDecayAlt.P.PBL
theorem _root_.solution {Wp' Wq' : Type} [NormedAddCommGroup Wp'] [InnerProductSpace ℂ Wp'] [NormedAddCommGroup Wq']
    [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wp'] [FiniteDimensional ℂ Wq'] {P : M.Par}
    (p : KB.Pl P Wp' Wq') (F : B.Mat P.k P.r → (Wq' →L[ℂ] Wp')) (i : ℕ) (w : List C.Letter) (a b : C.LPt)
    (hn : ¬ (D.IsLocPt a i ∧ D.IsLocPt b i)) : p.RR F i w a b = 0 := by
  unfold KB.Pl.RR D.RRplace
  rw [dif_neg hn]
end Formalism.FourierDecayAlt.P.PBL
