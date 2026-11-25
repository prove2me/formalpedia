-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBL.sizeAt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:51:23.986373+00:00
-- url     : https://prove2.me/submissions/be47e5a3-c238-4e76-ad06-927bb10815bb

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
theorem _root_.solution (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (w : List C.Letter) : 0 ≤ S.sizeAt v w := by
  unfold C.HidaSetting.sizeAt
  apply List.prod_nonneg
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _
end Formalism.FourierDecayAlt.P.PBL
