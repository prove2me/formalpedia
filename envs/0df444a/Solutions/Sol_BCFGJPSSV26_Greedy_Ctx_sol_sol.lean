-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Ctx.sol_sol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:00:34.290059+00:00
-- url     : https://prove2.me/submissions/58e65908-ce24-410a-9516-6a19d284ba5c

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Bridge
public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
import all Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete
public import Theorems.Thm_BCFGJPSSV26_Greedy_Ctx_complete_sol

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

namespace Ctx

variable (C : Ctx)

variable {C} {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)
include hX

section Iter

variable {b : Bool} {f θ : ℚ} {pre cur : List AAtom}

end Iter

/-- The solution of the greedy algorithm at a grid point is a `0`-valid solution with atoms in
range and no free atoms. -/
theorem sol_sol {b : ℕ} (hb : b ≤ 2 ^ C.ip.Pf) :
    Sol C.par X.d (C.fhat b) 0 (decH hX (C.sol b)) ∧ C.SolOK (C.sol b) ∧
      ∀ q, nFreeSeqA ((C.sol b).getD q []) = 0 := by
  obtain ⟨h1, h2⟩ := complete_sol hX (nη_lt_fhat hX b) (fhat_le_fmax hX hb) le_rfl (H := [])
    (by simp) (by simp [SolOK]) (fun p hp ↦ by simp [decH] at hp)
  refine ⟨h1, h2, fun q ↦ ?_⟩
  have hreg : ∀ a ∈ (C.sol b).flatten, a.2 = 0 := fun a ha ↦
    ((C.complete_atoms _ [] a ha).resolve_left (by simp)).1
  unfold nFreeSeqA
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro a ha
  simp [hreg a (mem_flatten_of_mem_getD ha)]

end Ctx

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Ctx.sol_sol := @BCFGJPSSV26.Greedy.Ctx.sol_sol
