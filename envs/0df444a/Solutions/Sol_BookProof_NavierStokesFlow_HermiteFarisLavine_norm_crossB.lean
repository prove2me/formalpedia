-- Prove2me | solution 1 for BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossB
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T07:32:41.884947+00:00
-- url     : https://prove2.me/submissions/33d9a648-aff4-4abf-b688-ce077cc3db75

-- Generated from ChapterNavierStokesHermiteFarisLavine.lean — solution of BookProof.NavierStokesFlow.HermiteFarisLavine.norm_crossB
import Mathlib
import Definitions.Def_ChapterNavierStokesHermiteFarisLavine
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.HermiteFarisLavine



open scoped ENNReal



open LpNat BookProof.FarisLavine IkebeKato

variable {κ : ℝ}
variable {x : maxDom (oscSymbol κ)}

set_option maxHeartbeats 1000000 in
theorem solution (hκ : 0 ≤ κ) (X Y : ℕ → ℂ) (n : ℕ) :
    ‖crossB κ X Y n‖ = amp κ n * ‖X (n + 2)‖ * ‖Y n‖ := by

  simp only [crossB, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (amp_nonneg hκ n), RCLike.norm_conj]
