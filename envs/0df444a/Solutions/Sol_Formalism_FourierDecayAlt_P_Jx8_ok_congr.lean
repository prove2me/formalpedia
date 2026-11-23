-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx8.ok_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:21.910847+00:00
-- url     : https://prove2.me/submissions/10d02b35-d1c5-4552-bbef-f5739edd593b

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OutsideSystemsBound
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx8_psd_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open scoped ComplexOrder ComplexConjugate Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx8
namespace Formalism.FourierDecayAlt.P.Jx8
theorem _root_.solution {E α : Type} [Field E] {N : E → E → α → α → ℂ} {B : α → α → ℂ} {L L' : AddSubgroup E}
    {Th Th' : E → α → α → ℂ} {F : Finset α}
    (h : ∀ t, ∀ x ∈ F, ∀ y ∈ F, Th t x y = Th' t x y) (hS : (LocSys.mk N Th B L L').Ok F) :
    (LocSys.mk N Th' B L L').Ok F := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hS
  refine ⟨h1, h2, fun t t' htt x hx y hy => ?_, fun t => psd_congr (h t) (h4 t),
    fun t ht => psd_congr (fun x hx y hy => ?_) (h5 t ht),
    fun R hR => psd_congr (fun x hx y hy => ?_) (h6 R hR)⟩
  · show Th' t x y = Th' t' x y
    rw [← h t x hx y hy, ← h t' x hx y hy]; exact h3 t t' htt x hx y hy
  · show Th t x y - N t t x y = Th' t x y - N t t x y
    rw [h t x hx y hy]
  · show B x y - ∑ t ∈ R, Th t x y = B x y - ∑ t ∈ R, Th' t x y
    rw [Finset.sum_congr rfl fun t _ => h t x hx y hy]
end Formalism.FourierDecayAlt.P.Jx8
