-- Prove2me | solution 1 for BookProof.NsBrstDerivativeGauge.nsHamAlg_one_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-21T12:28:44.938422+00:00
-- url     : https://prove2.me/submissions/2f7fa2e8-e973-44f6-aca9-822530449ab0

-- Generated from ChapterNsBrstDerivativeGauge.lean — solution of BookProof.NsBrstDerivativeGauge.nsHamAlg_one_ne_zero
import Mathlib
import Definitions.Def_ChapterNsBrstDerivativeGauge
import Theorems.Thm_BookProof_NsBrstDerivativeGauge_nsHamAlg_one
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Definitions.Def_ChapterNavierStokesGaugeY2
import Definitions.Def_ChapterNavierStokesGaugeY
open BookProof.NsBrstDerivativeGauge




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge
open BookProof.NavierStokesGaugeY BookProof.NavierStokesGaugeY2
open BookProof.NavierStokesGaugeY

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (nu : ℂ) : nsHamAlg nu 1 ≠ 0 := by

  rw [nsHamAlg_one]
  intro h
  have hc := congrArg (MvPolynomial.coeff (Finsupp.single (NSVar.uD 0 0) 1)) h
  rw [MvPolynomial.coeff_sum] at hc
  rw [Finset.sum_eq_single (0 : Fin 3), MvPolynomial.coeff_X] at hc
  simp at hc
  · intro b _ hb
    rw [MvPolynomial.coeff_X']
    exact if_neg fun hh => hb (by
      have := (Finsupp.single_left_injective (by norm_num) hh)
      simpa using this)
  · intro h0
    exact absurd (Finset.mem_univ (0 : Fin 3)) h0
