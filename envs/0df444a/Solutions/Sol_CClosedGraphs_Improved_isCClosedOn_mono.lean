-- Prove2me | solution 1 for CClosedGraphs.Improved.isCClosedOn_mono
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T16:55:04.09263+00:00
-- url     : https://prove2.me/submissions/af067c07-3f19-4ad9-9cff-f6c2e36563e2

import Mathlib
import Definitions.Def_CClosedGraphs_Improved_Setting

open CClosedGraphs.Improved

theorem solution {V : Type*} [Fintype V] [DecidableEq V] {c : ℕ}
    {G : SimpleGraph V} {W W' : Set V} (hW : IsCClosedOn c G W) (hsub : W' ⊆ W) :
    IsCClosedOn c G W' := by
  intro u hu v hv huv hc
  apply hW u (hsub hu) v (hsub hv) huv
  refine hc.trans ?_
  apply Set.ncard_le_ncard _ (Set.toFinite _)
  exact Set.inter_subset_inter_left _ hsub
