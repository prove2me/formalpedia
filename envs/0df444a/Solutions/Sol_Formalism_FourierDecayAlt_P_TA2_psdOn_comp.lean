-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA2.psdOn_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:42:31.187929+00:00
-- url     : https://prove2.me/submissions/1cb48072-7129-4e6b-b345-d92ed2a653ea

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OffDiagonalSchurComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA2
namespace Formalism.FourierDecayAlt.P.TA2
theorem _root_.solution {α β : Type} [DecidableEq β] (f : α → β) (g : β → α) (hg : ∀ x, g (f x) = x)
    (P : Finset α) (k : β → β → ℂ) (hk : PSDOn (P.image f) k) :
    PSDOn P (fun x y => k (f x) (f y)) := by
  have hinj : Function.Injective f := Function.LeftInverse.injective hg
  refine ⟨fun x hx y hy => hk.1 _ (mem_image_of_mem f hx) _ (mem_image_of_mem f hy), fun a => ?_⟩
  have := hk.2 (fun p => a (g p))
  rw [sum_image (fun x _ y _ h => hinj h)] at this
  refine this.trans_eq ?_
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [sum_image (fun x _ y _ h => hinj h)]
  simp only [hg]
end Formalism.FourierDecayAlt.P.TA2
