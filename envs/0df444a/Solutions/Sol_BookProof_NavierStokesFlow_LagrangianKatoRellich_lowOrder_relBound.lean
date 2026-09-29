-- Prove2me | solution 1 for BookProof.NavierStokesFlow.LagrangianKatoRellich.lowOrder_relBound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-13T13:21:03.88012+00:00
-- url     : https://prove2.me/submissions/15fbfb72-b9f1-4789-b3c7-9fee80b35963

-- Generated from ChapterNavierStokesLagrangianKatoRellich.lean — solution of BookProof.NavierStokesFlow.LagrangianKatoRellich.lowOrder_relBound
import Mathlib
import Definitions.Def_ChapterNavierStokesLagrangianKatoRellich
import Theorems.Thm_BookProof_NavierStokesFlow_LagrangianKatoRellich_norm_sum_P_le
import Definitions.Def_ChapterBandEnclosure
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesLagrangianEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LagrangianKatoRellich

















open Filter Topology



open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LagrangianEsa BookProof.FarisLavine
open BookProof.EsaClosure BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin



variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable (L : LagrangianFullData F)

set_option maxHeartbeats 1000000 in
theorem solution {kap kap' cc : ℝ} (hkap : 0 ≤ kap) (hkap' : 0 ≤ kap') (hcc : 0 ≤ cc)
    (hdrift : ∀ v : L.D,
      ‖(L.drift v : F)‖ ≤ kap * (∑ j : Fin 3, ‖(L.P j v : F)‖) + kap' * ‖(v : F)‖)
    (hC : ∀ v : L.D, ‖(L.constraintOp v : F)‖ ≤ cc * ‖(v : F)‖) {a : ℝ} (ha : 0 < a) :
    ∃ b : ℝ, 0 ≤ b ∧ ∀ v : L.D,
      ‖(lowOrder L v : F)‖ ≤ a * ‖(secondOrder L v : F)‖ + b * ‖(v : F)‖ := by

  set K : ℝ := 3 * kap with hK
  have hK0 : 0 ≤ K := by positivity
  have hK1 : (0 : ℝ) < K + 1 := by linarith
  set eps : ℝ := a / (K + 1) with heps
  have heps0 : 0 < eps := div_pos ha hK1
  have hKeps : K * eps ≤ a := by
    rw [heps, mul_div_assoc', div_le_iff₀ hK1]
    nlinarith
  refine ⟨K * (1 / (2 * eps)) + kap' + cc, by positivity, fun v => ?_⟩
  have hA0 : 0 ≤ ‖(v : F)‖ := norm_nonneg _
  have hB0 : 0 ≤ ‖(secondOrder L v : F)‖ := norm_nonneg _
  have hsum : kap * (∑ j : Fin 3, ‖(L.P j v : F)‖)
      ≤ K * (eps * ‖(secondOrder L v : F)‖ + (1 / (2 * eps)) * ‖(v : F)‖) := by
    have := mul_le_mul_of_nonneg_left (norm_sum_P_le L v heps0) hkap
    rw [hK]
    nlinarith
  have hlow : (lowOrder L v : F) = (L.drift v : F) + (L.constraintOp v : F) := by
    simp [lowOrder]
  calc ‖(lowOrder L v : F)‖ ≤ ‖(L.drift v : F)‖ + ‖(L.constraintOp v : F)‖ := by
        rw [hlow]; exact norm_add_le _ _
    _ ≤ (kap * (∑ j : Fin 3, ‖(L.P j v : F)‖) + kap' * ‖(v : F)‖) + cc * ‖(v : F)‖ :=
        add_le_add (hdrift v) (hC v)
    _ ≤ K * (eps * ‖(secondOrder L v : F)‖ + (1 / (2 * eps)) * ‖(v : F)‖)
        + kap' * ‖(v : F)‖ + cc * ‖(v : F)‖ := by linarith
    _ ≤ a * ‖(secondOrder L v : F)‖
        + (K * (1 / (2 * eps)) + kap' + cc) * ‖(v : F)‖ := by nlinarith
