-- Prove2me | solution 1 for BookProof.FockQuadratic.norm_hopT
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:43:53.940874+00:00
-- url     : https://prove2.me/submissions/22111132-a633-4848-a818-329c31208c3a

-- Generated from ChapterFockQuadraticEsa.lean — solution of BookProof.FockQuadratic.norm_hopT
import Mathlib
import Definitions.Def_ChapterFockQuadraticEsa
open BookProof.FockQuadratic



open scoped ENNReal


open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.NavierStokesFlow.LpNat BookProof.OperatorSeries

noncomputable section

variable {ι : Type*}

variable {ι : Type*}
variable {ω : ι → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (P Q : Idx ι) (x : Idx ι → ℂ) (b : Idx ι) :
    ‖hopT P Q x b‖ = amp P Q b * ‖x (tgt P Q b)‖ * ‖x b‖ := by

  simp [hopT, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (amp_nonneg P Q b)]
