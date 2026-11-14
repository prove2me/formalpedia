-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Ctx.MergeH.VS.of_pairs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:59:37.834586+00:00
-- url     : https://prove2.me/submissions/6ebb9790-5595-46ba-8d8c-e3b48d0b293e

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_MergeH_noOver_pre
public import Theorems.Thm_BCFGJPSSV26_Greedy_ValidSeq_of_profile_le

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

section AtomsValid

variable {n m : ℕ} {P : Par} {d : Fin n → Fin m → ℚ} {f η : ℚ} {p : ℕ}

end AtomsValid

variable {C : Ctx}

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

variable {p b : ℕ} {pre : List (List AAtom)}

/-- Valid atoms whose pairs contain those of a valid sequence form a valid sequence. -/
theorem VS.of_pairs (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) {H H' : List AAtom}
    (hH : VS hX p b pre H)
    (hat : AtomsValid C.par X.d (C.fhat b) C.ip.η p (decS hX pre.flatten) (decS hX H'))
    (hsub : pairs (decS hX pre.flatten ++ decS hX H) ⊆ pairs (decS hX pre.flatten ++ decS hX H')) :
    VS hX p b pre H' :=
  ValidSeq.of_profile_le hX.good (fun j i ↦ X.d_nonneg j i) hH (noOver_pre hX hlen hv _) hat
    fun j ↦ profL_anti _ _ hsub j

end BCFGJPSSV26.Greedy.Ctx.MergeH

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Ctx.MergeH.VS.of_pairs := @BCFGJPSSV26.Greedy.Ctx.MergeH.VS.of_pairs
