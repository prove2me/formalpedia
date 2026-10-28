-- Prove2me | solution 1 for FunctionalInequalities.Analysis.expansion_secondDifference_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:34:42.610988+00:00
-- url     : https://prove2.me/submissions/93902588-ea27-4613-a3d4-4df50ab7e33d

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT12D8MollifiedLogdetBound
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
 lemma solution {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x g : EuclideanSpace ℝ (Fin n)}
    {B : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ ε > 0, ∀ᶠ y in 𝓝 x,
      |u y - FunctionalInequalities.Analysis.quadraticAt B x g (u x) y| ≤ ε * ‖y - x‖ ^ 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun t : ℝ =>
      (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2)
      (𝓝[>] 0) (𝓝 ⟪v, Matrix.toEuclideanLin B v⟫) := by
  let q := ⟪v, Matrix.toEuclideanLin B v⟫
  have hp (t : ℝ) :
      FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x + t • v) =
        u x + t * ⟪g, v⟫ + (1 / 2) * (t ^ 2 * q) := by
    have he : x + t • v - x = t • v := by abel
    simp only [FunctionalInequalities.Analysis.quadraticAt, he, map_smul, real_inner_smul_left,
      real_inner_smul_right, q]
    ring
  have hm (t : ℝ) :
      FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x - t • v) =
        u x - t * ⟪g, v⟫ + (1 / 2) * (t ^ 2 * q) := by
    simpa only [neg_smul, ← sub_eq_add_neg, neg_mul, neg_sq] using hp (-t)
  have htp : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x + t • v) :=
      continuous_const.add (continuous_id.smul continuous_const)
    simpa only [zero_smul, add_zero] using hc.tendsto 0
  have htm : Tendsto (fun t : ℝ => x - t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun t : ℝ => x - t • v) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    simpa only [zero_smul, sub_zero] using hc.tendsto 0
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η := ε / (4 * (‖v‖ ^ 2 + 1))
  have hd : 0 < 4 * (‖v‖ ^ 2 + 1) := by positivity
  have hη : 0 < η := div_pos hε hd
  have hηeq : η * (4 * (‖v‖ ^ 2 + 1)) = ε :=
    div_mul_cancel₀ _ (ne_of_gt hd)
  have hsmall : 2 * η * ‖v‖ ^ 2 < ε := by
    nlinarith [sq_nonneg ‖v‖]
  filter_upwards [(htp.eventually (h η hη)).filter_mono nhdsWithin_le_nhds,
    (htm.eventually (h η hη)).filter_mono nhdsWithin_le_nhds,
    eventually_mem_nhdsWithin] with t ht₁ ht₂ ht
  have htpos : 0 < t := ht
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
  have hnum :
      |(u (x + t • v) + u (x - t • v) - 2 * u x) - t ^ 2 * q| ≤
        2 * η * t ^ 2 * ‖v‖ ^ 2 := by
    calc
      _ = |(u (x + t • v) - FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x + t • v)) +
          (u (x - t • v) - FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x - t • v))| := by
        rw [hp, hm]
        congr 1
        ring
      _ ≤ |u (x + t • v) - FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x + t • v)| +
          |u (x - t • v) - FunctionalInequalities.Analysis.quadraticAt B x g (u x) (x - t • v)| :=
        abs_add_le _ _
      _ ≤ η * ‖x + t • v - x‖ ^ 2 + η * ‖x - t • v - x‖ ^ 2 :=
        add_le_add ht₁ ht₂
      _ = _ := by
        have he₁ : x + t • v - x = t • v := by abel
        have he₂ : x - t • v - x = -(t • v) := by abel
        rw [he₁, he₂, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        ring
  have heq :
      (u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2 - q =
        ((u (x + t • v) + u (x - t • v) - 2 * u x) - t ^ 2 * q) / t ^ 2 := by
    field_simp
  change dist ((u (x + t • v) + u (x - t • v) - 2 * u x) / t ^ 2) q < ε
  rw [Real.dist_eq, heq, abs_div, abs_of_pos ht2]
  apply (div_lt_iff₀ ht2).mpr
  have hh := mul_lt_mul_of_pos_right hsmall ht2
  nlinarith
