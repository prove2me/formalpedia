-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Ctx.MergeH.noOver_pre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:58:16.369302+00:00
-- url     : https://prove2.me/submissions/f5f6d649-e2fd-429b-9dfa-d55ee2609753

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
public import Theorems.Thm_BCFGJPSSV26_Greedy_noOver_partial

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

section AtomsValid

variable {n m : ℕ} {P : Par} {d : Fin n → Fin m → ℚ} {f η : ℚ} {p : ℕ}

end AtomsValid

variable {C : Ctx}

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

variable {p b : ℕ} {pre : List (List AAtom)}

/-- No overbidding after a valid prefix and any atoms. -/
theorem noOver_pre (hlen : pre.length = p)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (S : List (Atom C.ip.m)) :
    NoOver C.par X.d (C.fhat b) (C.par.θseq p) (profL C.par.K X.d (decS hX pre.flatten ++ S)) := by
  have h := noOver_partial hX.good hX.d1 (fhat_nonneg' hX b) hv S
  rwa [decH_length, hlen, decH_flatten] at h

end BCFGJPSSV26.Greedy.Ctx.MergeH

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Ctx.MergeH.noOver_pre := @BCFGJPSSV26.Greedy.Ctx.MergeH.noOver_pre
