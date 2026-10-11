-- Prove2me | solution 1 for BookProof.NsLagrangianDet.det_eq_one_of_volPot_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:30.20515+00:00
-- url     : https://prove2.me/submissions/495618c1-42fa-4938-953f-1cc65337e930

-- Generated from ChapterNsLagrangianDetConvolution.lean — solution of BookProof.NsLagrangianDet.det_eq_one_of_volPot_eq_zero
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
import Theorems.Thm_BookProof_NsLagrangianDet_volume_residual_eq
import Theorems.Thm_BookProof_NsLagrangianDet_ev_volPot
open BookProof.NsLagrangianDet




open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

variable {K : Type*} [Fintype K]

set_option maxHeartbeats 1000000 in
theorem solution {kappa : ℝ} (hk : 0 < kappa) (kv : K → Fin 3 → ℝ)
    (y : DIdx K → ℝ) (h : ev y (volPot kappa kv) = 0) (a : Fin 3 → ℝ) :
    (1 + dispGrad kv y a).det = 1 := by

  rw [ev_volPot, Complex.ofReal_eq_zero] at h
  have hsum : ∑ q ∈ waveSet kv, Complex.normSq (ev y (volCoef kv q)) = 0 := by
    rcases mul_eq_zero.mp h with h1 | h1
    · linarith
    · exact h1
  have hzero : ∀ q ∈ waveSet kv, ev y (volCoef kv q) = 0 := fun q hq =>
    Complex.normSq_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg
      (fun q _ => Complex.normSq_nonneg _)).mp hsum q hq)
  have := volume_residual_eq kv y a
  rw [Finset.sum_eq_zero fun q hq => by rw [hzero q hq, zero_mul]] at this
  exact sub_eq_zero.mp this
