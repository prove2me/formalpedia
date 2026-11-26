-- Prove2me | solution 1 for BranchAnchorRepair.spectral_sum_eventually_positive_from_counting
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-17T18:19:58.367872+00:00
-- url     : https://prove2.me/submissions/0fa22e39-1204-4eee-9c8a-4c0c8fa9a3c5

import Mathlib
import Theorems.Thm_BranchAnchorRepair_normalized_offline_sum_from_counting
set_option autoImplicit false
open Filter Topology
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


end BranchAnchorRepair
namespace BranchAnchorRepair

theorem normalized_power_summable {ι : Type*} (B : ι → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => 1/(B i).re))
    (x X : ℝ) (hx : 0 < x) (hX : 0 < X) (k : ℕ) (hk : 1 ≤ k) :
    Summable (fun i => ((X : ℂ)/((x : ℂ)+B i))^k) := by
  apply (hs.mul_left (X^k)).of_norm_bounded
  intro i
  have hp : 0 < (B i).re := by linarith [hB i]
  have hnorm : (B i).re ≤ ‖(x : ℂ)+B i‖ := by
    have hh := Complex.re_le_norm ((x : ℂ)+B i)
    simp only [Complex.add_re, Complex.ofReal_re] at hh
    linarith
  have hi : ‖((x : ℂ)+B i)⁻¹‖ ≤ 1/(B i).re := by
    rw [norm_inv, one_div]
    exact inv_anti₀ hp hnorm
  have hi1 : ‖((x : ℂ)+B i)⁻¹‖ ≤ 1 := by
    exact hi.trans (by simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1) (hB i))
  have hpow : ‖((x : ℂ)+B i)⁻¹‖^k ≤ 1/(B i).re := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    calc
      _ = ‖((x : ℂ)+B i)⁻¹‖^m * ‖((x : ℂ)+B i)⁻¹‖ := pow_succ _ _
      _ ≤ 1 * ‖((x : ℂ)+B i)⁻¹‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ (norm_nonneg _) hi1) (norm_nonneg _)
      _ ≤ 1/(B i).re := by simpa using hi
  rw [div_eq_mul_inv, mul_pow, norm_mul, norm_pow, norm_pow]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX]
  exact mul_le_mul_of_nonneg_left hpow (by positivity)

theorem critical_normalized_sum_ge_one {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hcritical : ∀ i, eps i = 0 → B i = ((gamma i)^2 : ℝ))
    (anchor : ι) (hanchor : eps anchor = 0)
    (x : ℝ) (hx : 0 < x) (k : ℕ)
    (hs : Summable (fun i => (((x+(gamma anchor)^2 : ℝ) : ℂ)/((x : ℂ)+B i))^k)) :
    1 ≤ (∑' i : {i // eps i = 0},
      (((x+(gamma anchor)^2 : ℝ) : ℂ)/((x : ℂ)+B i))^k).re := by
  let f : ι → ℂ := fun i => (((x+(gamma anchor)^2 : ℝ) : ℂ)/((x : ℂ)+B i))^k
  have hc := hs.subtype (fun i => eps i = 0)
  have hcr := Complex.hasSum_re hc.hasSum
  have hnonneg : ∀ i : {i // eps i = 0}, 0 ≤ (f i).re := by
    intro i
    dsimp [f]
    rw [hcritical i i.property]
    rw [← Complex.ofReal_add, ← Complex.ofReal_div, ← Complex.ofReal_pow,
      Complex.ofReal_re]
    positivity
  have ha : (f anchor).re = 1 := by
    dsimp [f]
    rw [hcritical anchor hanchor, ← Complex.ofReal_add, div_self]
    · simp
    · exact_mod_cast (show x+(gamma anchor)^2 ≠ 0 by positivity)
  have hle := hcr.summable.le_tsum (⟨anchor,hanchor⟩ : {i // eps i = 0})
    (fun i _ => hnonneg i)
  rw [hcr.tsum_eq] at hle
  change (f anchor).re ≤ _ at hle
  rw [ha] at hle
  exact hle

end BranchAnchorRepair

namespace BranchAnchorRepair

theorem normalized_spectral_sum_eventually_positive {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (hcritical : ∀ i, eps i = 0 → B i = ((gamma i)^2 : ℝ))
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    ∀ᶠ n : ℕ in atTop, 0 < (∑' i,
      (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n)).re := by
  let f : ℕ → ι → ℂ := fun n i =>
    (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n)
  have hs := pole_reciprocal_summable_from_counting gamma eps B hB lower strip C p hp hcount
  have hlower : ∀ i, 1 ≤ (B i).re := by
    intro i
    rw [hB]
    obtain ⟨he1,he2⟩ := abs_le.mp (strip i)
    nlinarith [lower i]
  have hanchor : eps anchor = 0 := verified anchor (by linarith)
  have hoff := normalized_offline_sum_from_counting gamma eps B hB lower strip
    verified anchor anchor_low C p hp hcount k hk x hx hscale
  have hoffr : Tendsto (fun n => (∑' i : {i // eps i ≠ 0}, f n i).re)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, Complex.zero_re] using
      (Complex.continuous_re.tendsto 0).comp hoff
  filter_upwards [hk.eventually (eventually_ge_atTop 1),
    hoffr.eventually (eventually_gt_nhds (show (-1:ℝ)<0 by norm_num))] with n hn hoffn
  have hsum : Summable (f n) := normalized_power_summable B hlower hs
    (x n) (x n+(gamma anchor)^2) (hx n) (by have := hx n; positivity) (k n) hn
  have hcrit := critical_normalized_sum_ge_one gamma eps B hcritical anchor hanchor
    (x n) (hx n) (k n) hsum
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl {i | eps i = 0}
  have hsplitre := congrArg Complex.re hsplit
  simp only [Complex.add_re] at hsplitre
  change (∑' i : {i // eps i = 0}, f n i).re +
    (∑' i : {i // eps i ≠ 0}, f n i).re = (∑' i, f n i).re at hsplitre
  change 0 < (∑' i, f n i).re
  change 1 ≤ (∑' i : {i // eps i = 0}, f n i).re at hcrit
  linarith

end BranchAnchorRepair

namespace BranchAnchorRepair

/-- Large-scale escape forces eventual strict positivity of the original,
unnormalized real spectral power sum. -/
theorem spectral_sum_eventually_positive_from_counting {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (hcritical : ∀ i, eps i = 0 → B i = ((gamma i)^2 : ℝ))
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      0 < ∑' i, ((((x n : ℂ)+B i)⁻¹)^(k n)).re := by
  have hnpos := normalized_spectral_sum_eventually_positive gamma eps B hB hcritical
    lower strip verified anchor anchor_low C p hp hcount k hk x hx hscale
  have hs := pole_reciprocal_summable_from_counting gamma eps B hB lower strip C p hp hcount
  have hlower : ∀ i, 1 ≤ (B i).re := by
    intro i
    rw [hB]
    obtain ⟨he1,he2⟩ := abs_le.mp (strip i)
    nlinarith [lower i]
  filter_upwards [hnpos, hk.eventually (eventually_ge_atTop 1)] with n hn hn1
  have hsum : Summable (fun i => (((x n : ℂ)+B i)⁻¹)^(k n)) := by
    simpa only [Complex.ofReal_one, one_div] using
      normalized_power_summable B hlower hs (x n) 1 (hx n) (by norm_num) (k n) hn1
  have he : (∑' i, (((x n+(gamma anchor)^2 : ℝ) : ℂ)/((x n : ℂ)+B i))^(k n)) =
      ((x n+(gamma anchor)^2 : ℝ) : ℂ)^(k n) *
        ∑' i, (((x n : ℂ)+B i)⁻¹)^(k n) := by
    simp only [div_eq_mul_inv, mul_pow, tsum_mul_left]
  rw [he, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at hn
  have hreal : 0 < (∑' i, (((x n : ℂ)+B i)⁻¹)^(k n)).re :=
    pos_of_mul_pos_right hn (by have := hx n; positivity)
  rw [← (Complex.hasSum_re hsum.hasSum).tsum_eq] at hreal
  exact hreal

end BranchAnchorRepair

theorem solution {ι : Type*}
    (gamma eps : ι → ℝ) (B : ι → ℂ)
    (hB : ∀ i, (B i).re = (gamma i)^2-(eps i)^2)
    (hcritical : ∀ i, eps i = 0 → B i = ((gamma i)^2 : ℝ))
    (lower : ∀ i, 2 ≤ gamma i) (strip : ∀ i, |eps i| ≤ 1/2)
    (verified : ∀ i, gamma i ≤ 1000 → eps i = 0)
    (anchor : ι) (anchor_low : gamma anchor ≤ 100)
    (C p : ℝ) (hp : p < 1)
    (hcount : ∀ y ≥ (1 : ℝ), ∀ F : Finset ι,
      (∀ i ∈ F, (gamma i)^2 ≤ y) → (F.card : ℝ) ≤ C*y^p)
    (k : ℕ → ℕ) (hk : Tendsto k atTop atTop)
    (x : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hscale : Tendsto (fun (n : ℕ) => (k n : ℝ)/x n) atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      0 < ∑' i, ((((x n : ℂ)+B i)⁻¹)^(k n)).re :=
  BranchAnchorRepair.spectral_sum_eventually_positive_from_counting gamma eps B hB hcritical
    lower strip verified anchor anchor_low C p hp hcount k hk x hx hscale
