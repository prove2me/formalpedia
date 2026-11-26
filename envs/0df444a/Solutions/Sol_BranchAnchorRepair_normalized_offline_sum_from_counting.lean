-- Prove2me | solution 1 for BranchAnchorRepair.normalized_offline_sum_from_counting
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-17T18:17:28.322072+00:00
-- url     : https://prove2.me/submissions/5eebb8a3-8ca2-45cd-948a-01f7f49a7e31

import Mathlib
import Theorems.Thm_BranchLargeScaleRepair_normalized_pole_subsequence_sum_tendsto_zero
set_option autoImplicit false
open Filter Topology

namespace BranchAnchorRepair

theorem shifted_inverse_square_summable {ι : Type*}
    (a : ι → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (ha : ∀ i, 2*b+1 ≤ a i)
    (hs : Summable (fun i => 1/a i)) :
    Summable (fun i => 1/(a i-b)^2) := by
  apply (hs.mul_left 2).of_nonneg_of_le
  · intro i
    positivity
  · intro i
    have hd1 : 1 ≤ a i-b := by linarith [ha i]
    have hd : 0 < a i-b := by linarith
    have hap : 0 < a i := by linarith [ha i]
    calc
      1/(a i-b)^2 ≤ 1/(a i-b) :=
        one_div_le_one_div_of_le hd (by nlinarith)
      _ ≤ 2/a i := (div_le_div_iff₀ hd hap).2 (by linarith [ha i])
      _ = 2*(1/a i) := by ring

theorem anchor_shift_preserves_scale (k : ℕ → ℕ) (x : ℕ → ℝ)
    (hk : Tendsto k atTop atTop) (hx : ∀ n, 0 < x n)
    (b : ℝ) (hb : 0 ≤ b)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => (k n : ℝ)/(x n+b)) atTop atTop := by
  have hkr : Tendsto (fun (n : ℕ) => (k n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hk
  refine tendsto_atTop.2 ?_
  intro M
  filter_upwards [hscale.eventually (eventually_ge_atTop (2*M)),
    hkr.eventually (eventually_ge_atTop (2*M*b))] with n hn hn'
  apply (le_div_iff₀ (show 0 < x n+b by linarith [hx n])).2
  have hnx : 2*M*x n ≤ (k n : ℝ) := (le_div_iff₀ (hx n)).1 hn
  nlinarith

theorem offline_anchor_gap {ι : Type*} (gamma eps : ι → ℝ)
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100) :
    ∀ i : {i // eps i ≠ 0},
      2*(gamma anchor)^2+1 ≤ (gamma i)^2-(eps i)^2 := by
  intro i
  have hg : 1000 < gamma i := lt_of_not_ge (fun h => i.property (verified i h))
  have ha : 0 ≤ gamma anchor := by linarith [lower anchor]
  obtain ⟨he1,he2⟩ := abs_le.mp (strip i)
  have he : (eps i)^2 ≤ 1/4 := by nlinarith
  have ha2 : (gamma anchor)^2 ≤ 10000 := by nlinarith
  nlinarith

end BranchAnchorRepair

open Filter Topology

namespace BranchAnchorRepair

theorem normalized_offline_sum_after_anchor_tendsto_zero {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (hs : Summable (fun i => 1/(B i).re))
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i : {i // eps i ≠ 0},
      (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n))
      atTop (𝓝 0) := by
  let b : ℝ := (gamma anchor)^2
  have hb : 0 ≤ b := sq_nonneg _
  have hgap : ∀ i : {i // eps i ≠ 0}, 2*b+1 ≤ (B i).re := by
    intro i
    rw [hB]
    exact offline_anchor_gap gamma eps lower strip verified anchor anchor_low i
  have hss : Summable (fun i : {i // eps i ≠ 0} => 1/(B i).re) :=
    hs.subtype (fun i => eps i ≠ 0)
  have hshift := shifted_inverse_square_summable
    (fun i : {i // eps i ≠ 0} => (B i).re) b hb hgap hss
  have hz : ∀ i : {i // eps i ≠ 0}, 0 < (B i-(b : ℂ)).re := by
    intro i
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith [hgap i]
  have hzs : Summable (fun i : {i // eps i ≠ 0} => 1/((B i-(b : ℂ)).re)^2) := by
    simpa only [Complex.sub_re, Complex.ofReal_re] using hshift
  have hlarge := anchor_shift_preserves_scale k x hk hx b hb hscale
  have hlim := BranchLargeScaleRepair.normalized_pole_subsequence_sum_tendsto_zero
    (fun i : {i // eps i ≠ 0} => B i-(b : ℂ)) hz hzs k
    (hk.eventually (eventually_ge_atTop 2)) (fun n => x n+b)
    (fun n => by linarith [hx n]) hlarge
  have he : ∀ n, (∑' i : {i // eps i ≠ 0},
      (((x n+b : ℝ) : ℂ)/(((x n+b : ℝ) : ℂ)+(B i-(b : ℂ))))^(k n)) =
      ∑' i : {i // eps i ≠ 0},
      (((x n+b : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n) := by
    intro n
    apply tsum_congr
    intro i
    congr 2
    push_cast
    ring
  simp_rw [he] at hlim
  exact hlim

end BranchAnchorRepair

open MeasureTheory Set Filter Topology
open scoped BigOperators
noncomputable section
namespace BranchAnchorCounting

theorem indicator_integrable (a : ℝ) :
    IntegrableOn ((Ioi a).indicator (fun y : ℝ => y^(-2 : ℝ))) (Ioi 1) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (by norm_num : (0 : ℝ) < 1)).indicator measurableSet_Ioi

theorem indicator_integral (a : ℝ) (ha : 1 ≤ a) :
    (∫ y : ℝ in Ioi 1, (Ioi a).indicator (fun y : ℝ => y^(-2 : ℝ)) y) = a⁻¹ := by
  rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    inter_eq_left.mpr (Ioi_subset_Ioi ha)]
  have hh := integral_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
    (show 0 < a by linarith)
  simpa only [show (-2 : ℝ)+1 = -1 by norm_num, Real.rpow_neg_one,
    div_neg, div_one, neg_neg] using hh

theorem summable_inverse_from_sublinear_count {ι : Type*} (a : ι → ℝ) (ha : ∀ j, 1 ≤ a j)
    (C r : ℝ) (hr : r < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ j ∈ F, a j ≤ y) → (F.card : ℝ) ≤ C*y^r) :
    Summable (fun j => (a j)⁻¹) ∧ (∑' j, (a j)⁻¹) ≤ C/(1-r) := by
  classical
  have hi : IntegrableOn (fun y : ℝ => C*y^(r-2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : r-2 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul C
  have hb (F : Finset ι) : (∑ j ∈ F, (a j)⁻¹) ≤ C/(1-r) := by
    calc
      _ = ∑ j ∈ F, ∫ y : ℝ in Ioi 1,
          (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y := by
        apply Finset.sum_congr rfl
        intro j hj
        exact (indicator_integral (a j) (ha j)).symm
      _ = ∫ y : ℝ in Ioi 1, ∑ j ∈ F,
          (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y :=
        (integral_finsetSum F (fun j _ => indicator_integrable (a j))).symm
      _ ≤ ∫ y : ℝ in Ioi 1, C*y^(r-2) := by
        apply integral_mono_ae (integrable_finset_sum F (fun j _ => indicator_integrable (a j))) hi
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        have hy1 : 1 ≤ y := (mem_Ioi.mp hy).le
        have hy0 : 0 ≤ y := by linarith
        have he : (∑ j ∈ F, (Ioi (a j)).indicator (fun y : ℝ => y^(-2 : ℝ)) y) =
            ((F.filter (fun j => a j < y)).card : ℝ)*y^(-2 : ℝ) := by
          simp only [Set.indicator, mem_Ioi]
          rw [← Finset.sum_filter]
          simp
        rw [he]
        have hc := hcount y hy1 (F.filter (fun j => a j < y))
          (fun j hj => (Finset.mem_filter.mp hj).2.le)
        calc
          _ ≤ (C*y^r)*y^(-2 : ℝ) :=
            mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hy0 _)
          _ = C*y^(r-2) := by rw [mul_assoc, ← Real.rpow_add (show 0 < y by linarith)]; congr 2 <;> ring
      _ = C/(1-r) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by linarith : r-2 < -1) (by norm_num)]
        rw [show r-2+1 = -(1-r) by ring]
        simp only [Real.one_rpow, div_neg, neg_neg, one_div]
        ring
  have hs := summable_of_sum_le (fun j => inv_nonneg.mpr (by linarith [ha j])) hb
  exact ⟨hs, hs.tsum_le_of_sum_le hb⟩

end BranchAnchorCounting
end

namespace BranchAnchorRepair

theorem pole_reciprocal_summable_from_counting {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p) :
    Summable (fun i => 1/(B i).re) := by
  have hs := (BranchAnchorCounting.summable_inverse_from_sublinear_count
    (fun i => (gamma i)^2) (fun i => by nlinarith [lower i]) C p hp hcount).1
  apply (hs.mul_left 2).of_nonneg_of_le
  · intro i
    rw [hB]
    obtain ⟨he1,he2⟩ := abs_le.mp (strip i)
    have hpos : 0 < (gamma i)^2-(eps i)^2 := by nlinarith [lower i]
    positivity
  · intro i
    have hb : (gamma i)^2/2 ≤ (B i).re := by
      rw [hB]
      obtain ⟨he1,he2⟩ := abs_le.mp (strip i)
      nlinarith [lower i]
    have hg : 0 < (gamma i)^2/2 := by nlinarith [lower i]
    calc
      1/(B i).re ≤ 1/((gamma i)^2/2) := one_div_le_one_div_of_le hg hb
      _ = 2*((gamma i)^2)⁻¹ := by rw [one_div, inv_div]; ring

/-- The large-scale off-line estimate with shifted summability derived from
sublinear occurrence counting. The low-height verification remains explicit. -/
theorem normalized_offline_sum_from_counting {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i : {i // eps i ≠ 0},
      (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n))
      atTop (𝓝 0) := by
  exact normalized_offline_sum_after_anchor_tendsto_zero gamma eps B hB lower strip
    verified anchor anchor_low
    (pole_reciprocal_summable_from_counting gamma eps B hB lower strip C p hp hcount)
    k hk x hx hscale

end BranchAnchorRepair

theorem solution {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    Tendsto (fun (n : ℕ) => ∑' i : {i // eps i ≠ 0},
      (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n))
      atTop (𝓝 0) :=
  BranchAnchorRepair.normalized_offline_sum_from_counting gamma eps B hB lower strip
    verified anchor anchor_low C p hp hcount k hk x hx hscale
