-- Prove2me | solution 1 for BookProof.NsLagrangianDet.det_deformation_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:55:22.96298+00:00
-- url     : https://prove2.me/submissions/cde2a768-a82a-4cd9-ab08-172f2156eddf

-- Generated from ChapterNsLagrangianDetConvolution.lean — solution of BookProof.NsLagrangianDet.det_deformation_eq
import Mathlib
import Definitions.Def_ChapterNsLagrangianDetConvolution
import Theorems.Thm_BookProof_NsLagrangianDet_phase_sum
import Theorems.Thm_BookProof_NsLagrangianDet_det_rows_sum
import Theorems.Thm_BookProof_NsLagrangianDet_one_add_dispGrad
open BookProof.NsLagrangianDet




open MvPolynomial Matrix

noncomputable section

variable {K : Type*} [Fintype K]

variable {K : Type*} [Fintype K]

set_option maxHeartbeats 1000000 in
theorem solution (kv : K → Fin 3 → ℝ) (y : DIdx K → ℝ) (a : Fin 3 → ℝ) :
    (1 + dispGrad kv y a).det = ∑ q ∈ waveSet kv, ev y (detCoef kv q) * phase q a := by

  classical
  rw [one_add_dispGrad, det_rows_sum]
  have hterm : ∀ τ : Fin 3 → Option (SMode K),
      (Matrix.of fun r c => ev y (rowCoef kv (τ r) r c) * ophase kv a (τ r)).det
        = ev y ((Matrix.of fun r c => rowCoef kv (τ r) r c).det) * phase (tupleWave kv τ) a := by
    intro τ
    have e1 : (Matrix.of fun r c => ev y (rowCoef kv (τ r) r c) * ophase kv a (τ r))
        = Matrix.of fun r c => ophase kv a (τ r) * ((ev y).mapMatrix
            (Matrix.of fun r c => rowCoef kv (τ r) r c)) r c := by
      ext r c; simp [mul_comm]
    rw [e1, det_mul_column, RingHom.map_det, mul_comm]
    congr 1
    rw [tupleWave, ← phase_sum]
    rfl
  rw [Finset.sum_congr rfl fun τ _ => hterm τ]
  simp only [detCoef, map_sum, Finset.sum_mul]
  symm
  calc ∑ q ∈ waveSet kv, ∑ τ ∈ Finset.univ.filter (fun τ => tupleWave kv τ = q),
        ev y ((Matrix.of fun r c => rowCoef kv (τ r) r c).det) * phase q a
      = ∑ q ∈ waveSet kv, ∑ τ ∈ Finset.univ.filter (fun τ => tupleWave kv τ = q),
        ev y ((Matrix.of fun r c => rowCoef kv (τ r) r c).det) * phase (tupleWave kv τ) a :=
        Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun τ hτ => by
          rw [(Finset.mem_filter.mp hτ).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun τ _ => by simp [waveSet]) _
