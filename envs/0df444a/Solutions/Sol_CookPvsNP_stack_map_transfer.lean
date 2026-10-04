-- Prove2me | solution 1 for CookPvsNP.stack_map_transfer
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:03:58.280326+00:00
-- url     : https://prove2.me/submissions/31e0a19d-d58b-4652-96d8-4318925c87e5

import Definitions.Def_CookPvsNP_StackMapTransfer

set_option autoImplicit false
open CookPvsNP

private theorem transfer {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool) (f : A → A)
    (w : List A) (s : K → List A) (hs : s src = w) :
    (mapTransferProg src targets f).Exec s (mapTransferStore src targets f s) (3 * w.length + 1) := by
  induction w generalizing s with
  | nil =>
    have hf : mapTransferStore src targets f s = s := by
      funext k
      by_cases hk : k = src <;> simp [mapTransferStore, hk, hs]
    rw [hf]
    exact .loopFalse (by simp [hs])
  | cons a w ih =>
    let s' := StackProg.applyAct (mapTransferAct src targets f) s
    have hs' : s' src = w := by simp [s', StackProg.applyAct, mapTransferAct, hs, StackAct.apply]
    have hout : mapTransferStore src targets f s' = mapTransferStore src targets f s := by
      funext k
      by_cases hk : k = src
      · simp [mapTransferStore, hk]
      · cases ht : targets k <;>
          simp [mapTransferStore, hk, ht, hs', s', StackProg.applyAct, mapTransferAct, hs,
            StackAct.apply, List.reverse_cons, List.map_append, List.append_assoc]
    have h := StackProg.Exec.loopTrue (by simp [hs])
      (StackProg.Exec.act (mapTransferAct src targets f) s) (ih s' hs')
    rw [hout] at h
    convert h using 1 <;> simp [mapTransferProg] <;> omega

theorem solution {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool) (f : A → A)
    (s : K → List A) :
    (mapTransferProg src targets f).Exec s (mapTransferStore src targets f s) (3 * (s src).length + 1) := by
  exact transfer src targets f (s src) s rfl

#print axioms solution
