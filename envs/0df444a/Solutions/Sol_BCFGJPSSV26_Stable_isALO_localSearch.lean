-- Prove2me | solution 1 for BCFGJPSSV26.Stable.isALO_localSearch
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:56:22.104808+00:00
-- url     : https://prove2.me/submissions/b94cda99-ecdd-4a3a-a3d7-91f90676b648

module

public import Definitions.Def_BCFGJPSSV26_Stable_Params
public import Definitions.Def_BCFGJPSSV26_Stable_LocalSearch_ThreeApprox
public import Definitions.Def_BuhaiPapers_Background_Tuples
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_LocalSearch

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Tuples Encoding

variable {I : Instance}

/-- **The output of the local search is an approximate local optimum**, when the budget is large
enough. -/
theorem isALO_localSearch (hv : I.Valid) (hk : I.k ≤ I.m) {N B : ℕ} (hN : 1 ≤ N)
    (hB₁ : (I.k * I.m) ^ Par.p N ≤ B) (hB₂ : 2 * N * I.k * (encInstance I).length + 2 ≤ B) :
    IsALO I (Par.p N) (1 / (N * I.k)) (I.centers (localSearch N (toRaw I) B)) := by
  classical
  obtain ⟨hnd, hlen, hm⟩ := localSearch_spec hk N B
  have hfix := lsStep_iterate_fixed hv hk hN hB₂
  have hk1 := hv.one_le_k
  have hinv : LSInv I.m I.k (localSearch N (toRaw I) B) := ⟨hnd, hlen, hm⟩
  have hc0 := cost_nonneg_of_lsInv hv hinv
  refine isALO_of_card_eq hv (by rw [Instance.card_centers hnd hm, hlen]) fun T hT hST ↦ ?_
  obtain ⟨w, hw, hwT⟩ := exists_lsApply_eq hk1 hB₁ hnd hlen hm hT hST
  by_contra hlt
  push Not at hlt
  have hinv' := lsInv_lsApply (m := I.m) (k := I.k) w hinv
  have hne : ∀ {S : List ℕ}, LSInv I.m I.k S → S ≠ [] := by
    intro S h h'
    have := h.2.1
    rw [h', List.length_nil] at this
    omega
  -- the swap `w` improves
  have himp : lsImproves N (toRaw I) (localSearch N (toRaw I) B)
      (lsApply (toRaw I).m w (localSearch N (toRaw I) B)) = true := by
    unfold lsImproves
    refine decide_eq_true ?_
    have h1 := Raw.cost_toRaw (hne hinv') hinv'.2.2
    have h2 := Raw.cost_toRaw (hne hinv) hm
    rw [hwT] at h1
    have : (((toRaw I).cost (lsApply I.m w (localSearch N (toRaw I) B)) : ℚ) : ℝ) <
        (((1 - 1 / ((N : ℚ) * I.k)) * (toRaw I).cost (localSearch N (toRaw I) B) : ℚ) : ℝ) := by
      push_cast
      rw [h1, h2]
      exact hlt
    exact_mod_cast this
  -- so the step moves, a contradiction
  obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.1 ((List.find?_isSome
    (xs := tuples B ((toRaw I).k * (toRaw I).m) (Par.p N)) (p := fun w ↦ lsImproves N (toRaw I)
      (localSearch N (toRaw I) B) (lsApply (toRaw I).m w (localSearch N (toRaw I) B)))).2
    ⟨w, hw, himp⟩)
  have himp' := List.find?_some hw'
  have hstep : lsStep N (toRaw I) B (localSearch N (toRaw I) B) =
      lsApply (toRaw I).m w' (localSearch N (toRaw I) B) := by
    unfold lsStep
    rw [hw']
  rw [hstep] at hfix
  unfold lsImproves at himp'
  rw [hfix] at himp'
  have h := of_decide_eq_true himp'
  have hδ : (0 : ℚ) ≤ 1 / ((N : ℚ) * (toRaw I).k) := by positivity
  nlinarith

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.isALO_localSearch := @BCFGJPSSV26.Stable.isALO_localSearch
