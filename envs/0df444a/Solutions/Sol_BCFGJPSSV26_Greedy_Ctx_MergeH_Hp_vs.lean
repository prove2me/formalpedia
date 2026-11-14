-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Ctx.MergeH.Hp_vs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:00:45.967029+00:00
-- url     : https://prove2.me/submissions/3b9a26d1-b8d0-4c76-a0d0-e0b7d4877882

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeWalk
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeWalk
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_vs_completeSeq

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

variable {C : Ctx}

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

variable {p b : ℕ} {pre : List (List AAtom)} {Hp H'p : List AAtom}

section Hp

variable (hlen : pre.length = p) (hokp : C.SolOK pre)
  (hHp : Hp = C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten [])

include hokp hHp in
theorem Hp_vs : VS hX p b pre Hp := by
  rw [hHp]
  exact vs_completeSeq hX hokp atomsValid_nil (by simp)

end Hp

end BCFGJPSSV26.Greedy.Ctx.MergeH

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Ctx.MergeH.Hp_vs := @BCFGJPSSV26.Greedy.Ctx.MergeH.Hp_vs
