-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_pos_volume_convexHull_closedBall_union_singleton_ge_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:07:32.441707+00:00
-- url     : https://prove2.me/submissions/a49af706-350d-470f-8da2-e08718b793b1

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11C4ConeVolume
open MeasureTheory Set Metric
open scoped ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Volume of the cone over a ball** (weak Letwin route, Caffarelli's argument, Alexandrov maximum
principle): there is `c > 0`, depending only on `E`, such that the convex hull of the closed ball of
radius `r` and a point `q` with `‖q‖ ≥ r` has volume at least `c · r^(n−1) · ‖q‖`, `n = dim E`. -/
theorem solution {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
    [BorelSpace E] :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℝ, 0 < r → ∀ q : E, r ≤ ‖q‖ →
      ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
        (volume : Measure E) (convexHull ℝ (closedBall (0 : E) r ∪ {q})) := by
  classical
  by_cases hE : Nontrivial E
  · let v : ℝ := (volume (ball (0 : E) 1)).toReal
    let c : ℝ := v / (2 : ℝ) ^ (Module.finrank ℝ E + 2)
    have hn0 : Module.finrank ℝ E ≠ 0 := by
      intro hn
      have hs : Subsingleton E := Module.finrank_zero_iff.mp hn
      exact (not_nontrivial_iff_subsingleton.mpr hs) hE
    have hn : 1 ≤ Module.finrank ℝ E :=
      Nat.one_le_iff_ne_zero.mpr hn0
    have hv_top : volume (ball (0 : E) 1) ≠ ∞ :=
      ne_of_lt measure_ball_lt_top
    have hv_pos : 0 < v := by
      dsimp [v]
      exact ENNReal.toReal_pos
        (ne_of_gt (Metric.measure_ball_pos volume (0 : E) zero_lt_one)) hv_top
    have hc : 0 < c := by
      dsimp [c]
      positivity
    refine ⟨c, hc, ?_⟩
    intro r hr q hq
    have hqpos : 0 < ‖q‖ := lt_of_lt_of_le hr hq
    let e : E := ‖q‖⁻¹ • q
    have he : ‖e‖ = 1 := by
      dsimp [e]
      rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hqpos]
      exact inv_mul_cancel₀ hqpos.ne'
    have hqe : q = ‖q‖ • e := by
      calc
        q = (1 : ℝ) • q := (one_smul ℝ q).symm
        _ = (‖q‖ * ‖q‖⁻¹) • q := by
          rw [mul_inv_cancel₀ hqpos.ne', one_smul]
        _ = ‖q‖ • (‖q‖⁻¹ • q) := by rw [smul_smul]
        _ = ‖q‖ • e := by rfl
    let N : ℕ := ⌊‖q‖ / (4 * r)⌋₊
    let C : ℕ → E := fun k => ((k : ℝ) * (2 * r)) • e
    have hN : (N : ℝ) ≤ ‖q‖ / (4 * r) := by
      dsimp [N]
      exact Nat.floor_le (by positivity)
    have hball :
        ∀ k ∈ Finset.range (N + 1),
          closedBall (C k) (r / 2) ⊆
            convexHull ℝ (closedBall (0 : E) r ∪ {q}) := by
      intro k hk x hx
      have hkN : k ≤ N :=
        Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      have hkr : (k : ℝ) * (2 * r) ≤ ‖q‖ / 2 := by
        have hk' : (k : ℝ) ≤ (N : ℝ) := by
          exact_mod_cast hkN
        have h₁ : (k : ℝ) * (2 * r) ≤ (N : ℝ) * (2 * r) :=
          mul_le_mul_of_nonneg_right hk' (by positivity)
        have h₂ : (N : ℝ) * (2 * r) ≤ ‖q‖ / 2 := by
          calc
            (N : ℝ) * (2 * r) ≤ (‖q‖ / (4 * r)) * (2 * r) :=
              mul_le_mul_of_nonneg_right hN (by positivity)
            _ = ‖q‖ / 2 := by
              field_simp
              ring
        exact h₁.trans h₂
      have hx' : ‖x - C k‖ ≤ r / 2 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hx
      let s : ℝ := ((k : ℝ) * (2 * r)) / ‖q‖
      let b : E := (1 - s)⁻¹ • (x - C k)
      have hs0 : 0 ≤ s := by
        dsimp [s]
        positivity
      have hs_half : s ≤ 1 / 2 := by
        dsimp [s]
        apply (div_le_iff₀ hqpos).2
        nlinarith [hkr]
      have hs1 : s ≤ 1 := by
        linarith
      have hden : 0 < 1 - s := by
        linarith
      have hi : (1 - s)⁻¹ ≤ 2 := by
        have hmul :
            (1 / 2 : ℝ) * (1 - s)⁻¹ ≤ (1 - s) * (1 - s)⁻¹ :=
          mul_le_mul_of_nonneg_right
            (by linarith [hs_half]) (inv_nonneg.mpr hden.le)
        rw [mul_inv_cancel₀ hden.ne'] at hmul
        nlinarith
      have hb : b ∈ closedBall (0 : E) r := by
        rw [Metric.mem_closedBall, dist_zero_right]
        dsimp [b]
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hden.le)]
        calc
          (1 - s)⁻¹ * ‖x - C k‖ ≤ 2 * ‖x - C k‖ :=
            mul_le_mul_of_nonneg_right hi (norm_nonneg _)
          _ ≤ 2 * (r / 2) := by
            exact mul_le_mul_of_nonneg_left hx' (by norm_num)
          _ = r := by ring
      have hsQ : s * ‖q‖ = (k : ℝ) * (2 * r) := by
        dsimp [s]
        field_simp
      have hs_q : s • q = (s * ‖q‖) • e := by
        calc
          s • q = s • (‖q‖ • e) := congrArg (fun z : E => s • z) hqe
          _ = (s * ‖q‖) • e := by rw [smul_smul]
      have hrep : (1 - s) • b + s • q = x := by
        calc
          (1 - s) • b + s • q =
              (1 - s) • b + (s * ‖q‖) • e := by rw [hs_q]
          _ = (x - C k) + (s * ‖q‖) • e := by
            dsimp [b]
            rw [smul_smul, mul_inv_cancel₀ hden.ne', one_smul]
          _ = (x - C k) + ((k : ℝ) * (2 * r)) • e := by rw [hsQ]
          _ = x := by
            dsimp [C]
            abel
      have hxseg : x ∈ segment ℝ b q := by
        rw [segment_eq_image]
        refine ⟨s, ⟨hs0, hs1⟩, ?_⟩
        simpa using hrep
      exact
        segment_subset_convexHull
          (Set.mem_union_left {q} hb)
          (Set.mem_union_right (closedBall (0 : E) r) (by simp))
          hxseg
    have hdisj :
        (Finset.range (N + 1) : Set ℕ).PairwiseDisjoint
          (fun k => closedBall (C k) (r / 2)) := by
      rw [Set.pairwiseDisjoint_iff]
      intro i hi j hj hne
      rcases hne with ⟨x, hxi, hxj⟩
      by_contra hneq
      rcases lt_or_gt_of_ne hneq with hlt | hgt
      · have hij : i + 1 ≤ j := Nat.succ_le_iff.mp hlt
        have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by
          exact_mod_cast hij
        have hscalar :
            (i : ℝ) * (2 * r) - (j : ℝ) * (2 * r) ≤ 0 := by
          nlinarith [hij', hr.le]
        have hdist : 2 * r ≤ dist (C i) (C j) := by
          rw [dist_eq_norm]
          dsimp [C]
          rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs,
            abs_of_nonpos hscalar]
          nlinarith [hij', hr]
        have hxi' : dist (C i) x ≤ r / 2 := by
          rw [dist_comm]
          exact Metric.mem_closedBall.mp hxi
        have hxj' : dist x (C j) ≤ r / 2 :=
          Metric.mem_closedBall.mp hxj
        have hlt' : dist (C i) (C j) ≤ r := by
          calc
            dist (C i) (C j) ≤ dist (C i) x + dist x (C j) :=
              dist_triangle _ _ _
            _ ≤ r := by linarith
        linarith
      · have hji : j + 1 ≤ i := Nat.succ_le_iff.mp hgt
        have hji' : (j : ℝ) + 1 ≤ (i : ℝ) := by
          exact_mod_cast hji
        have hscalar :
            (j : ℝ) * (2 * r) - (i : ℝ) * (2 * r) ≤ 0 := by
          nlinarith [hji', hr.le]
        have hdist : 2 * r ≤ dist (C j) (C i) := by
          rw [dist_eq_norm]
          dsimp [C]
          rw [← sub_smul, norm_smul, he, mul_one, Real.norm_eq_abs,
            abs_of_nonpos hscalar]
          nlinarith [hji', hr]
        have hxj' : dist (C j) x ≤ r / 2 := by
          rw [dist_comm]
          exact Metric.mem_closedBall.mp hxj
        have hxi' : dist x (C i) ≤ r / 2 :=
          Metric.mem_closedBall.mp hxi
        have hlt' : dist (C j) (C i) ≤ r := by
          calc
            dist (C j) (C i) ≤ dist (C j) x + dist x (C i) :=
              dist_triangle _ _ _
            _ ≤ r := by linarith
        linarith
    have hmeas :
        ∀ k ∈ Finset.range (N + 1),
          MeasurableSet (closedBall (C k) (r / 2)) := by
      intro k hk
      exact isClosed_closedBall.measurableSet
    have hunion :
        volume (⋃ k ∈ Finset.range (N + 1), closedBall (C k) (r / 2)) =
          ∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2)) :=
      measure_biUnion_finset hdisj hmeas
    have hsum :
        (∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2))) =
          ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) := by
      calc
        (∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2))) =
            ∑ k ∈ Finset.range (N + 1),
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [Measure.addHaar_closedBall volume (C k) (by positivity)]
        _ = ((N + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              simp [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have hsubset :
        (⋃ k ∈ Finset.range (N + 1), closedBall (C k) (r / 2)) ⊆
          convexHull ℝ (closedBall (0 : E) r ∪ {q}) := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨k, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hk, hx⟩
      exact hball k hk hx
    have hmeasure :
        ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) ≤
          volume (convexHull ℝ (closedBall (0 : E) r ∪ {q})) := by
      calc
        ((N + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) =
            ∑ k ∈ Finset.range (N + 1), volume (closedBall (C k) (r / 2)) := hsum.symm
        _ = volume (⋃ k ∈ Finset.range (N + 1), closedBall (C k) (r / 2)) :=
          hunion.symm
        _ ≤ volume (convexHull ℝ (closedBall (0 : E) r ∪ {q})) :=
          measure_mono hsubset
    have hcount : ‖q‖ / (4 * r) < (N + 1 : ℝ) := by
      dsimp [N]
      exact Nat.lt_floor_add_one _
    have hreal :
        c * r ^ (Module.finrank ℝ E - 1) * ‖q‖ ≤
          (N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v := by
      have hQ : ‖q‖ ≤ 4 * r * (N + 1 : ℝ) := by
        have h := (div_lt_iff₀ (by positivity : (0 : ℝ) < 4 * r)).mp hcount
        exact le_of_lt (by linarith)
      have hcoef :
          0 ≤ c * r ^ (Module.finrank ℝ E - 1) :=
        mul_nonneg hc.le (pow_nonneg hr.le _)
      have hp :
          r ^ (Module.finrank ℝ E - 1) * r =
            r ^ Module.finrank ℝ E := by
        rw [← pow_succ]
        congr 1
        exact Nat.sub_add_cancel hn
      calc
        c * r ^ (Module.finrank ℝ E - 1) * ‖q‖ =
            (c * r ^ (Module.finrank ℝ E - 1)) * ‖q‖ := by ring
        _ ≤ (c * r ^ (Module.finrank ℝ E - 1)) *
              (4 * r * (N + 1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hQ hcoef
        _ = ((N + 1 : ℝ) * v *
              (r ^ (Module.finrank ℝ E - 1) * r)) /
              (2 : ℝ) ^ Module.finrank ℝ E := by
          dsimp [c]
          field_simp [show (2 : ℝ) ≠ 0 by norm_num]
          ring
        _ = (N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v := by
          rw [hp, div_pow]
          ring
    have hv : ENNReal.ofReal v = volume (ball (0 : E) 1) :=
      ENNReal.ofReal_toReal hv_top
    have hcast :
        ENNReal.ofReal ((N : ℝ) + 1) =
          (N : ℝ≥0∞) + 1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (ENNReal.ofReal_natCast (N + 1))
    have hEq :
        ENNReal.ofReal
            ((N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v) =
          ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) := by
      calc
        ENNReal.ofReal
            ((N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v) =
            ENNReal.ofReal
              (((N : ℝ) + 1) *
                (((r / 2) ^ Module.finrank ℝ E) * v)) := by
                  congr 1
                  ring
        _ = ENNReal.ofReal ((N : ℝ) + 1) *
              ENNReal.ofReal (((r / 2) ^ Module.finrank ℝ E) * v) := by
              rw [ENNReal.ofReal_mul (by positivity)]
        _ = ((N : ℝ≥0∞) + 1) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              rw [hcast, ENNReal.ofReal_mul (by positivity), hv]
        _ = ((N + 1 : ℕ) : ℝ≥0∞) *
              (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
                volume (ball (0 : E) 1)) := by
              norm_num
    calc
      ENNReal.ofReal (c * r ^ (Module.finrank ℝ E - 1) * ‖q‖) ≤
          ENNReal.ofReal
            ((N + 1 : ℝ) * ((r / 2) ^ Module.finrank ℝ E) * v) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ((N + 1 : ℕ) : ℝ≥0∞) *
            (ENNReal.ofReal ((r / 2) ^ Module.finrank ℝ E) *
              volume (ball (0 : E) 1)) := hEq
      _ ≤ volume (convexHull ℝ (closedBall (0 : E) r ∪ {q})) := hmeasure
  · have hsub : Subsingleton E :=
      not_nontrivial_iff_subsingleton.mp hE
    refine ⟨1, zero_lt_one, ?_⟩
    intro r hr q hq
    have hq0 : q = 0 := hsub.elim q 0
    rw [hq0, norm_zero] at hq
    linarith
