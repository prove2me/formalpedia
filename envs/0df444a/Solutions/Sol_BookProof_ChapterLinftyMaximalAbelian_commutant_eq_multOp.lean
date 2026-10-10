-- Prove2me | solution 1 for BookProof.ChapterLinftyMaximalAbelian.commutant_eq_multOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T20:42:44.896986+00:00
-- url     : https://prove2.me/submissions/f9f626ad-bc8a-4cd5-8665-45606e4cc9be

-- Generated from ChapterLinftyMaximalAbelian.lean — solution of BookProof.ChapterLinftyMaximalAbelian.commutant_eq_multOp
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
import Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_oneLp_coeFn
import Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_symbol_mul
import Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_multOp_indicator_oneLp
import Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_memLp_top_symbol
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_coeFn
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMaximalAbelian



noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

set_option maxHeartbeats 1000000 in
theorem solution {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ} (hT : CommutesWithMultOps T) :
    T = multOp (symbol T) (memLp_top_symbol hT) := by

  have hψ := memLp_top_symbol hT
  refine ContinuousLinearMap.ext ?_
  refine Lp.induction (p := (2 : ℝ≥0∞)) (by norm_num)
    (motive := fun f => T f = multOp (symbol T) hψ f) ?_ ?_ ?_
  · intro c s hs hμs
    have hcoe : ((Lp.simpleFunc.indicatorConst 2 hs hμs.ne c : Lp.simpleFunc ℂ 2 μ) : Lp ℂ 2 μ)
        = indicatorConstLp 2 hs hμs.ne c := Lp.simpleFunc.coe_indicatorConst hs hμs.ne c
    rw [hcoe]
    have hind : indicatorConstLp 2 hs (measure_ne_top μ s) c
        = multOp (s.indicator fun _ => c) ((memLp_top_const c).indicator hs) (oneLp μ) :=
      (multOp_indicator_oneLp hs c).symm
    refine Lp.ext ?_
    rw [hind]
    filter_upwards [symbol_mul hT (s.indicator fun _ => c) ((memLp_top_const c).indicator hs),
      multOp_coeFn (symbol T) hψ
        (multOp (s.indicator fun _ => c) ((memLp_top_const c).indicator hs) (oneLp μ)),
      multOp_coeFn (s.indicator fun _ => c) ((memLp_top_const c).indicator hs) (oneLp μ),
      oneLp_coeFn (μ := μ)] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4, mul_one, mul_comm]
  · intro f g hf hg _ hfm hgm
    rw [map_add, map_add, hfm, hgm]
  · exact isClosed_eq T.continuous (multOp (symbol T) hψ).continuous
