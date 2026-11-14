-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Ctx.MergeH.complete_sol_pre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:00:35.481199+00:00
-- url     : https://prove2.me/submissions/7f94ba2c-349d-4c60-8fb3-3d9d7121dc6b

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_complete_sol

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

section AtomsValid

variable {n m : ℕ} {P : Par} {d : Fin n → Fin m → ℚ} {f η : ℚ} {p : ℕ}

end AtomsValid

variable {C : Ctx}

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

variable {p b : ℕ} {pre : List (List AAtom)}

/-- **The completion of a valid sequence after a valid prefix is a solution.** -/
theorem complete_sol_pre (hlen : pre.length = p) (hp : p < 2 * C.ip.R) (hb : b ≤ 2 ^ C.ip.Pf)
    (hv : EtaValid C.par X.d (C.fhat b) C.ip.η (decH hX pre)) (hokp : C.SolOK pre)
    {W : List AAtom} (hW : VS hX p b pre W) (hok : ∀ a ∈ W, C.AtomOK a) :
    Sol C.par X.d (C.fhat b) C.ip.η (decH hX (C.complete (C.fhat b) (pre ++ [W]))) ∧
      C.SolOK (C.complete (C.fhat b) (pre ++ [W])) := by
  refine complete_sol hX (nη_lt_fhat hX b) (fhat_le_fmax hX hb) hX.good.η_nonneg
    (by simp; omega) (SolOK.append hokp hok) ?_
  rw [decH_append]
  refine etaValid_append.2 ⟨hv, ?_⟩
  rw [decH_length, hlen, decH_flatten]
  exact hW

end BCFGJPSSV26.Greedy.Ctx.MergeH

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Ctx.MergeH.complete_sol_pre := @BCFGJPSSV26.Greedy.Ctx.MergeH.complete_sol_pre
