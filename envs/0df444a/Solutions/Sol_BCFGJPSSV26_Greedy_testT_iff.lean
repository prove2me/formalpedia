-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.testT_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:56:50.276522+00:00
-- url     : https://prove2.me/submissions/074f0253-8c49-43b9-8e3c-21a1985b54db

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Space
import Mathlib.Data.Finset.Max
public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
import all Definitions.Def_BCFGJPSSV26_Greedy_Openable
public import Theorems.Thm_BCFGJPSSV26_Greedy_test2_iff

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

section Mono

variable {θ T T' f η : ℚ} {D D' : Fin n → ℚ} {i i₀ : Fin m}

end Mono

theorem testT_iff (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) (b : Bool) {f θ : ℚ}
    {D : Fin n → ℚ} {i : Fin m} (hθ : 0 < θ) :
    testT P d b f θ D i = true ↔ OpenT P d b f 0 θ D i := by
  cases b
  · exact test2_iff hP hd hθ
  · exact test1_iff

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.testT_iff := @BCFGJPSSV26.Greedy.testT_iff
