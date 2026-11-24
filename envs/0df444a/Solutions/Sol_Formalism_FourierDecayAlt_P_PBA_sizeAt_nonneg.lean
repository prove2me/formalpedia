-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBA.sizeAt_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:57:32.780941+00:00
-- url     : https://prove2.me/submissions/4d2ee187-0564-4d3c-88cc-a07c59fc88f5

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdmissibleOfPlaces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SizeAtNonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped ComplexConjugate ComplexOrder
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBA
open Formalism.FourierDecayAlt
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)] [∀ x, NormedAddCommGroup (Wq x)]
  [∀ x, InnerProductSpace ℂ (Wq x)] (S : C.HidaSetting E Wp Wq)
namespace Formalism.FourierDecayAlt.P.PBA
theorem _root_.solution (v : Fin S.f) (a : List C.Letter) : 0 ≤ S.sizeAt v a := by
  unfold C.HidaSetting.sizeAt
  apply List.prod_nonneg
  intro x hx
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  exact abs_nonneg _
end Formalism.FourierDecayAlt.P.PBA
