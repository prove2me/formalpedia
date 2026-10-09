-- Prove2me | solution 1 for BookProof.BookBrstYangMills.gaussDer_vecComb
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:40:34.61353+00:00
-- url     : https://prove2.me/submissions/a71fcf90-b21a-4ce6-9493-befd2c43dc52

-- Generated from ChapterBookBrstYangMills.lean — solution of BookProof.BookBrstYangMills.gaussDer_vecComb
import Mathlib
import Definitions.Def_ChapterBookBrstYangMills
import Theorems.Thm_BookProof_BookBrstYangMills_vecComb_sum
open BookProof.BookBrstYangMills




open MvPolynomial BookProof.BRSTNilpotent BookProof.QuantumGravityBrstCharge

noncomputable section

variable {N : ℕ} (G : GaugeAlgebra N)

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin N) (α : ℝ) (β : Fin N → ℝ) (μ : Fin 4) :
    gaussDer G c (vecComb α β μ)
      = vecComb (∑ b, β b * (-(G.D μ c b))) (fun g => ∑ b, β b * G.f b g c) μ := by

  have h1 : gaussDer G c (((α : ℝ) : ℂ) • (1 : FieldPoly N)) = 0 := by
    rw [Derivation.map_smul_of_tower, Derivation.map_one_eq_zero, smul_zero]
  have h2 : gaussDer G c (∑ g, ((β g : ℝ) : ℂ) • X (μ, g))
      = ∑ g, ((β g : ℝ) : ℂ) • gaussVec G c (μ, g) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun g _ => by
      rw [Derivation.map_smul_of_tower, gaussDer_X]
  rw [vecComb, map_add, h1, h2, zero_add]
  simpa [gaussVec] using vecComb_sum (N := N) β (fun b => -(G.D μ c b))
    (fun b g => G.f b g c) μ
