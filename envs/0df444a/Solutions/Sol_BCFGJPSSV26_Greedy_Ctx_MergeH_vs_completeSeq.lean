-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Ctx.MergeH.vs_completeSeq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:59:07.220215+00:00
-- url     : https://prove2.me/submissions/d82cf56b-2ab4-4941-8f0b-fbdf8d0b8b16

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_completeSeq_validSeq

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

section AtomsValid

variable {n m : ℕ} {P : Par} {d : Fin n → Fin m → ℚ} {f η : ℚ} {p : ℕ}

end AtomsValid

variable {C : Ctx}

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

variable {p b : ℕ} {pre : List (List AAtom)}

/-- The completion of a sequence of valid atoms is valid. -/
theorem vs_completeSeq (hokp : C.SolOK pre) {cur : List AAtom}
    (hcur : AtomsValid C.par X.d (C.fhat b) C.ip.η p (decS hX pre.flatten) (decS hX cur))
    (hok : ∀ a ∈ cur, C.AtomOK a) :
    VS hX p b pre (C.completeSeq (typ1 p) (C.fhat b) (C.θseq p) pre.flatten cur) :=
  completeSeq_validSeq hX (nη_lt_fhat hX b) hX.good.η_nonneg
    (fun a ha ↦ (List.mem_append.1 ha).elim (hokp a) (hok a)) (atomsValid_dec hX hcur)

end BCFGJPSSV26.Greedy.Ctx.MergeH

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Ctx.MergeH.vs_completeSeq := @BCFGJPSSV26.Greedy.Ctx.MergeH.vs_completeSeq
