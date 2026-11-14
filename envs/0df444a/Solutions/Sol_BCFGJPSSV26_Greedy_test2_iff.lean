-- Prove2me | solution 1 for BCFGJPSSV26.Greedy.test2_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T17:56:17.604755+00:00
-- url     : https://prove2.me/submissions/1ab24e0f-9cd8-499f-ac96-7b0643d32044

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Space
import Mathlib.Data.Finset.Max
public import Definitions.Def_BCFGJPSSV26_Greedy_Openable
import all Definitions.Def_BCFGJPSSV26_Greedy_Openable

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Greedy

open Finset

variable {n m : ℕ} (P : Par) (d : Fin n → Fin m → ℚ)

variable {P d}

section Mono

variable {θ T T' f η : ℚ} {D D' : Fin n → ℚ} {i i₀ : Fin m}

end Mono

/-- **The test of type 2 is exact.** -/
theorem test2_iff (hP : P.Good n) (hd : ∀ j i, 0 ≤ d j i) {f θ : ℚ} {D : Fin n → ℚ}
    {i : Fin m} (hθ : 0 < θ) : test2 P d f θ D i = true ↔ Open2 P d f 0 θ D i := by
  rw [test2, decide_eq_true_iff, Open2]
  simp only [mul_zero, sub_zero]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨_, θ_le_tstar f θ D i, h1, h2, h3⟩
  · rintro ⟨T, hT, hT', h3, h4⟩
    have ht := tstar_le hP hd hθ hT h3
    exact ⟨ht.trans hT', le_lhs3_tstar hP hd hθ ht h3,
      fun i₀ ↦ (lhs4_mono_T ht).trans (h4 i₀)⟩

end BCFGJPSSV26.Greedy

end

public section

theorem solution : type_of% @BCFGJPSSV26.Greedy.test2_iff := @BCFGJPSSV26.Greedy.test2_iff
