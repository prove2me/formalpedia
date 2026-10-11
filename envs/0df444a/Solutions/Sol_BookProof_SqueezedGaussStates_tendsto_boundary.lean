-- Prove2me | solution 1 for BookProof.SqueezedGaussStates.tendsto_boundary
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:57:58.221977+00:00
-- url     : https://prove2.me/submissions/6a7e0f34-e618-4637-a76b-8b97f24c2acb

-- Generated from ChapterSqueezedGaussStates.lean — solution of BookProof.SqueezedGaussStates.tendsto_boundary
import Mathlib
import Definitions.Def_ChapterSqueezedGaussStates
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterGaussCoordCombo
open BookProof.SqueezedGaussStates




open MvPolynomial BookProof.HermiteProductCore BookProof.GaussCoordCombo

noncomputable section

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Filter.Tendsto (fun M : ℕ => (2 * (M : ℝ) + 1) * ρ ^ M) Filter.atTop (nhds 0) := by

  have h1' : Filter.Tendsto (fun M : ℕ => (M : ℝ) * ρ ^ M) Filter.atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one h0 h1
  have h2' : Filter.Tendsto (fun M : ℕ => ρ ^ M) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1
  have := ((h1'.const_mul (2 : ℝ)).add h2')
  simpa using this.congr (fun M => by ring)
