-- Prove2me | solution 1 for FeinbergLiang.ACOE.liminf_eq_liminf_nhds_of_equicontinuous
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:32:14.151512+00:00
-- url     : https://prove2.me/submissions/a3da4cde-ebb6-4313-8c85-0d55a1070d92

import Mathlib
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace FeinbergLiang.ACOE

theorem aux_lelin_upper {Y : Type*} [MetricSpace Y] (f : ℕ → Y → ℝ) (x : Y) :
    liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 p.2)) (atTop ×ˢ 𝓝 x) ≤
      liminf (fun n => ENNReal.ofReal (f n x)) atTop := by
  have h1 : liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 p.2)) (atTop ×ˢ 𝓝 x) ≤
      liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 p.2)) (atTop ×ˢ pure x) :=
    liminf_le_liminf_of_le (Filter.prod_mono le_rfl (pure_le_nhds x))
  have h2 : Tendsto (fun n : ℕ => (n, x)) atTop (atTop ×ˢ pure x) :=
    tendsto_id.prodMk (tendsto_pure.2 (Eventually.of_forall fun _ => rfl))
  have h3 := h2.liminf_le_liminf_comp (u := fun p : ℕ × Y => ENNReal.ofReal (f p.1 p.2))
  exact h1.trans h3

theorem aux_lelin_lower {Y : Type*} [MetricSpace Y] (f : ℕ → Y → ℝ)
    (hf_nonneg : ∀ n y, 0 ≤ f n y) (hf_equi : Equicontinuous f) (x : Y) :
    liminf (fun n => ENNReal.ofReal (f n x)) atTop ≤
      liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 p.2)) (atTop ×ˢ 𝓝 x) := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hev : ∀ᶠ y in 𝓝 x, ∀ i, dist (f i x) (f i y) < ε :=
    Metric.equicontinuousAt_iff_right.1 (hf_equi x) ε hε
  have hev2 : ∀ᶠ p in atTop ×ˢ 𝓝 x,
      ENNReal.ofReal (f p.1 x) ≤ ENNReal.ofReal (f p.1 p.2) + (ε : ℝ≥0∞) := by
    filter_upwards [hev.prod_inr (atTop : Filter ℕ)] with p hp
    have h := hp p.1
    rw [Real.dist_eq] at h
    have hlt : f p.1 x ≤ f p.1 p.2 + ε := by
      have := (abs_lt.1 h).2
      linarith
    calc ENNReal.ofReal (f p.1 x) ≤ ENNReal.ofReal (f p.1 p.2 + ε) :=
          ENNReal.ofReal_le_ofReal hlt
      _ = ENNReal.ofReal (f p.1 p.2) + ENNReal.ofReal (ε : ℝ) :=
          ENNReal.ofReal_add (hf_nonneg _ _) ε.2
      _ = ENNReal.ofReal (f p.1 p.2) + (ε : ℝ≥0∞) := by rw [ENNReal.ofReal_coe_nnreal]
  have hA : liminf (fun n => ENNReal.ofReal (f n x)) atTop ≤
      liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 x)) (atTop ×ˢ 𝓝 x) :=
    (tendsto_fst (f := atTop) (g := 𝓝 x)).liminf_le_liminf_comp
      (u := fun n => ENNReal.ofReal (f n x))
  have hB : liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 x)) (atTop ×ˢ 𝓝 x) ≤
      liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 p.2) + (ε : ℝ≥0∞)) (atTop ×ˢ 𝓝 x) :=
    liminf_le_liminf hev2
  have hC : liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 p.2) + (ε : ℝ≥0∞)) (atTop ×ˢ 𝓝 x) =
      liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 p.2)) (atTop ×ˢ 𝓝 x) + (ε : ℝ≥0∞) :=
    liminf_add_const _ _ _ (by isBoundedDefault) (by isBoundedDefault)
  exact hA.trans (hB.trans hC.le)

end FeinbergLiang.ACOE

open FeinbergLiang.ACOE
open MeasureTheory ProbabilityTheory Filter Topology TopologicalSpace
open scoped ENNReal NNReal

theorem solution {Y : Type*} [MetricSpace Y] (f : ℕ → Y → ℝ)
    (hf_nonneg : ∀ n y, 0 ≤ f n y) (hf_equi : Equicontinuous f)
    (hf_bdd : ∀ y, BddAbove (Set.range fun n => f n y)) (x : Y) :
    liminf (fun n => ENNReal.ofReal (f n x)) atTop =
      liminf (fun p : ℕ × Y => ENNReal.ofReal (f p.1 p.2)) (atTop ×ˢ 𝓝 x) :=
  le_antisymm (aux_lelin_lower f hf_nonneg hf_equi x) (aux_lelin_upper f x)
