-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.Run.rstar_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:00:23.957696+00:00
-- url     : https://prove2.me/submissions/c16e5da8-a35a-44e9-8eae-3b8d80a3d37a

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Trace
public import Definitions.Def_BCFGJPSSV26_Greedy_FRP
public import Definitions.Def_BCFGJPSSV26_Greedy_Embed
import all Definitions.Def_BCFGJPSSV26_Greedy_Embed
public import Theorems.Thm_BCFGJPSSV26_Greedy_Run_Zv_ge_third

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

namespace Embed

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

end Embed

namespace Run

variable {n m : ℕ} (R : Run n m)

variable (Dg : Finset (Fin n))

variable {Dg}

variable (hne : Dg.Nonempty)
include hne

section

variable {istar : Fin m}

theorem rstar_nonneg_of_kf_le (hF : R.Freezing hne istar) {k : R.DgT Dg} (hk : R.kf hne ≤ k)
    (j : R.DgT Dg) : 0 ≤ R.rstar hne istar j k := by
  rw [R.rstar_of_kf_le hne hF hk]
  split_ifs with h
  · have := R.Zv_ge_third hne hF j h
    have := R.θl_pos hne
    linarith
  · exact le_min (R.Xv_nonneg _ _) ((R.X.d_nonneg _ _).trans (le_max_right _ _))

end

variable {istar : Fin m} (hD : ∀ j ∈ Dg, ρ * R.X.d j istar ≤ R.αs j)
include hD

set_option linter.unusedSectionVars false in
theorem rstar_nonneg (j : R.DgT Dg) (k : WithTop (R.DgT Dg)) : 0 ≤ R.rstar hne istar j k := by
  by_cases hF : R.Freezing hne istar
  · induction k using WithTop.recTopCoe with
    | top => rw [R.rstar_top_of hne hF]
    | coe k =>
      by_cases hk : R.kf hne ≤ k
      · exact R.rstar_nonneg_of_kf_le hne hF hk j
      · rw [R.rstar_coe_of_not hne (fun h' ↦ hk (WithTop.coe_le_coe.1 h'.2))]
        exact R.Xv_nonneg _ _
  · rw [R.rstar_of_not_freezing hne hF]
    exact R.Xv_nonneg _ _

end Run

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.Run.rstar_nonneg := @BCFGJPSSV26.Greedy.Run.rstar_nonneg
