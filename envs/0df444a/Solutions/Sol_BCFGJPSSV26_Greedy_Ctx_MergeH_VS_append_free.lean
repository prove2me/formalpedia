-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Ctx.MergeH.VS.append_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:59:36.988145+00:00
-- url     : https://prove2.me/submissions/9bd30a36-86f7-401c-823c-e0b6f5ed72e9

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_noOver_pre
public import Theorems.Thm_BCFGJPSSV26_Greedy_ValidSeq_append_free

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

section AtomsValid

variable {n m : ℕ} {P : Par} {d : Fin n → Fin m → ℚ} {f η : ℚ} {p : ℕ}

end AtomsValid

variable {C : Ctx}

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

variable {p b : ℕ} {pre : List (List AAtom)}

theorem VS.append_free (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) {W : List AAtom}
    (hW : VS hX p b pre W) (z g : ℕ) : VS hX p b pre (W ++ [(z, g + 1)]) := by
  unfold VS at hW ⊢
  rw [decS_append]
  exact ValidSeq.append_free hX.good (fun j i ↦ X.d_nonneg j i) hW (noOver_pre hX hlen hv _)
    (decA_free hX z g)

end BCFGJPSSV26.Greedy.Ctx.MergeH

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Ctx.MergeH.VS.append_free := @BCFGJPSSV26.Greedy.Ctx.MergeH.VS.append_free
