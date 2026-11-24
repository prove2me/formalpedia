-- Prove2me | solution 1 for Formalism.NG.descent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:09:58.059664+00:00
-- url     : https://prove2.me/submissions/547ff161-348a-4597-915c-ae5ae1bef930

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_VccSpan

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.NG
namespace Formalism.NG
theorem _root_.solution : StatDescent := by
  intro O _ X X' T T' Z p q b hexp hind f' hf' hvan π'
  obtain ⟨a, haT, rfl⟩ := hexp f' hf'
  have hker : ∀ k, (⟨a k, haT k⟩ : T) ∈ ccIdeal T Z := by
    intro k
    rw [ccIdeal, RingHom.mem_ker]
    funext x
    have hx : x.1 ∉ Z := x.2
    have h0 := hind x.1 hx (fun k => a k x.1) (fun x' hx' => by
      have e := hvan x' (by rw [hx']; exact hx)
      simpa [hx', Finset.sum_apply, Pi.mul_apply, Function.comp] using e)
    have e2 := congrFun h0 k
    simpa [resOff] using e2
  rw [Finset.sum_apply]
  refine Ideal.sum_mem _ fun k _ => ?_
  simp only [Pi.mul_apply, Function.comp_apply]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨_, hker k, rfl⟩)
end Formalism.NG
