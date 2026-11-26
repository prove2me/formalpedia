-- Prove2me | solution 1 for ClassicalComplexWPT.norm_lastCoefficientSeries_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:03:32.296829+00:00
-- url     : https://prove2.me/submissions/2d24b359-bc33-48be-a435-ae54b1f1eb16

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Theorems.Thm_ClassicalComplexWPT_norm_baseInclusion_le
import Theorems.Thm_ClassicalComplexWPT_norm_evalLast_le
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero



set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000
namespace ClassicalComplexWPT
theorem _root_.solution {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k l : ℕ) :
    ‖lastCoefficientSeries p k l‖ ≤ ‖p.changeOriginSeries k l‖ := by
  unfold lastCoefficientSeries
  rw [ContinuousLinearMap.compFormalMultilinearSeries_apply]
  have hpre :
      ‖((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n)) l‖ ≤
        ‖p.changeOriginSeries k l‖ := by
    calc
      _ ≤ ‖p.changeOriginSeries k l‖ * ‖baseInclusion n‖ ^ l :=
        (p.changeOriginSeries k).norm_compContinuousLinearMap_le (baseInclusion n) l
      _ ≤ ‖p.changeOriginSeries k l‖ * 1 ^ l := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg (baseInclusion n)) (norm_baseInclusion_le n) l)
          (norm_nonneg (p.changeOriginSeries k l))
      _ = ‖p.changeOriginSeries k l‖ := by simp
  calc
    ‖(evalLast n k).compContinuousMultilinearMap
        (((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n)) l)‖ ≤
        ‖evalLast n k‖ *
          ‖((p.changeOriginSeries k).compContinuousLinearMap (baseInclusion n)) l‖ :=
      ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * ‖p.changeOriginSeries k l‖ :=
      mul_le_mul (norm_evalLast_le n k) hpre
        (norm_nonneg (((p.changeOriginSeries k).compContinuousLinearMap
          (baseInclusion n)) l)) (by norm_num)
    _ = ‖p.changeOriginSeries k l‖ := one_mul _
end ClassicalComplexWPT
