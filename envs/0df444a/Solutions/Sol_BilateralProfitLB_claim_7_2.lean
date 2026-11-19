-- Prove2me | solution 1 for BilateralProfitLB.claim_7_2
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T13:07:36.865056+00:00
-- url     : https://prove2.me/submissions/fb2da941-e9bb-4eb5-a031-6829a9812337

import Mathlib
import Definitions.Def_BilateralProfitLB_Construction


section BundlePart000


open Set Filter
open scoped Topology

namespace BilateralProfitLB

private theorem hasDerivAt_glue_le {f g h : ℝ → ℝ} {c d : ℝ}
    (hf : HasDerivAt f d c) (hg : HasDerivAt g d c)
    (h_left : h =ᶠ[𝓝[Iic c] c] f) (h_right : h =ᶠ[𝓝[Ici c] c] g) :
    HasDerivAt h d c := by
  have hl : HasDerivWithinAt h d (Iic c) c :=
    hf.hasDerivWithinAt.congr_of_eventuallyEq_of_mem h_left (le_refl c)
  have hr : HasDerivWithinAt h d (Ici c) c :=
    hg.hasDerivWithinAt.congr_of_eventuallyEq_of_mem h_right (le_refl c)
  rw [← hasDerivWithinAt_univ, ← Iic_union_Ici]
  exact hl.union hr

private theorem continuousAt_glue_le {f g h : ℝ → ℝ} {c : ℝ}
    (hf : ContinuousAt f c) (hg : ContinuousAt g c)
    (h_left : h =ᶠ[𝓝[Iic c] c] f) (h_right : h =ᶠ[𝓝[Ici c] c] g) :
    ContinuousAt h c := by
  have hl : ContinuousWithinAt h (Iic c) c :=
    hf.continuousWithinAt.congr_of_eventuallyEq_of_mem h_left (le_refl c)
  have hr : ContinuousWithinAt h (Ici c) c :=
    hg.continuousWithinAt.congr_of_eventuallyEq_of_mem h_right (le_refl c)
  rw [← continuousWithinAt_univ, ← Iic_union_Ici]
  exact hl.union hr

private def rhoPoly (u : ℝ) : ℝ := 16 * u ^ 2 * (1 - u) ^ 2
private def rhoPolyD (u : ℝ) : ℝ := 32 * u * (1 - u) * (1 - 2 * u)
private def rhoPolyDD (u : ℝ) : ℝ := 32 - 192 * u * (1 - u)

private theorem rho_eq_poly {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    rho u = 16 * u ^ 2 * (1 - u) ^ 2 := by
  simp [rho, hu]

private theorem rho_eq_zero_of_le_zero {u : ℝ} (hu : u ≤ 0) : rho u = 0 := by
  rcases hu.lt_or_eq with hu | rfl
  · have h : u ∉ Icc (0 : ℝ) 1 := fun ⟨h, _⟩ => (not_le_of_gt hu) h
    simp [rho, h]
  · norm_num [rho]

private theorem rho_eq_zero_of_one_le {u : ℝ} (hu : 1 ≤ u) : rho u = 0 := by
  rcases hu.lt_or_eq with hu | rfl
  · have h : u ∉ Icc (0 : ℝ) 1 := fun ⟨_, h⟩ => (not_le_of_gt hu) h
    simp [rho, h]
  · norm_num [rho]

private theorem rho_nonneg (u : ℝ) : 0 ≤ rho u := by
  by_cases hu : u ∈ Icc (0 : ℝ) 1
  · rw [rho_eq_poly hu]
    positivity
  · simp [rho, hu]

private theorem u_mul_one_sub_le {u : ℝ} : u * (1 - u) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (u - 1 / 2)]

private theorem rho_le_one (u : ℝ) : rho u ≤ 1 := by
  by_cases hu : u ∈ Icc (0 : ℝ) 1
  · rw [rho_eq_poly hu]
    have hn : 0 ≤ u * (1 - u) := mul_nonneg hu.1 (sub_nonneg.mpr hu.2)
    have hm : u * (1 - u) ≤ 1 / 4 := u_mul_one_sub_le
    have hs := mul_le_mul hm hm hn (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith only [hs]
  · simp [rho, hu]

private theorem rho_half : rho (1 / 2) = 1 := by
  rw [rho_eq_poly (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)]
  norm_num

private theorem hasDerivAt_rhoPoly (u : ℝ) : HasDerivAt rhoPoly (rhoPolyD u) u := by
  unfold rhoPoly rhoPolyD
  convert
    ((hasDerivAt_const u (16 : ℝ)).mul ((hasDerivAt_id u).pow 2)).mul
      (((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)).pow 2) using 1
  all_goals first | rfl | simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.neg_apply, Pi.add_apply, id_eq] <;> ring

private theorem hasDerivAt_rhoPolyD (u : ℝ) : HasDerivAt rhoPolyD (rhoPolyDD u) u := by
  unfold rhoPolyD rhoPolyDD
  convert
    (((hasDerivAt_const u (32 : ℝ)).mul (hasDerivAt_id u)).mul
      ((hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u))).mul
      ((hasDerivAt_const u (1 : ℝ)).sub
        ((hasDerivAt_const u (2 : ℝ)).mul (hasDerivAt_id u))) using 1
  all_goals first | rfl | simp only [Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, Pi.neg_apply, Pi.add_apply, id_eq] <;> ring

private theorem hasDerivAt_rho (u : ℝ) : HasDerivAt rho
    (if u ∈ Icc (0 : ℝ) 1 then 32 * u * (1 - u) * (1 - 2 * u) else 0) u := by
  by_cases hu0 : u < 0
  · have hn : u ∉ Icc (0 : ℝ) 1 := fun ⟨h, _⟩ => (not_le_of_gt hu0) h
    rw [if_neg hn]
    apply (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hu0] with x hx using rho_eq_zero_of_le_zero hx.le
  by_cases hu1 : 1 < u
  · have hn : u ∉ Icc (0 : ℝ) 1 := fun ⟨_, h⟩ => (not_le_of_gt hu1) h
    rw [if_neg hn]
    apply (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hu1] with x hx using rho_eq_zero_of_one_le hx.le
  rw [if_pos (show u ∈ Icc (0 : ℝ) 1 from ⟨le_of_not_gt hu0, le_of_not_gt hu1⟩)]
  rcases (le_of_not_gt hu0).eq_or_lt with rfl | hu0'
  · norm_num
    refine hasDerivAt_glue_le (g := rhoPoly) (hasDerivAt_const 0 0) ?_ ?_ ?_
    · simpa [rhoPolyD] using hasDerivAt_rhoPoly 0
    · filter_upwards [self_mem_nhdsWithin] with x hx using rho_eq_zero_of_le_zero hx
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with x hx hx1
      exact rho_eq_poly ⟨hx, hx1.le⟩
  rcases (le_of_not_gt hu1).eq_or_lt with rfl | hu1'
  · norm_num
    refine hasDerivAt_glue_le (f := rhoPoly) ?_ (hasDerivAt_const 1 0) ?_ ?_
    · simpa [rhoPolyD] using hasDerivAt_rhoPoly 1
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)] with x hx hx0
      exact rho_eq_poly ⟨hx0.le, hx⟩
    · filter_upwards [self_mem_nhdsWithin] with x hx using rho_eq_zero_of_one_le hx
  · apply (hasDerivAt_rhoPoly u).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hu0', gt_mem_nhds hu1'] with x hx0 hx1 using
      rho_eq_poly ⟨hx0.le, hx1.le⟩

private theorem rho_deriv_formula (u : ℝ) :
    deriv rho u =
      if u ∈ Icc (0 : ℝ) 1 then 32 * u * (1 - u) * (1 - 2 * u) else 0 :=
  (hasDerivAt_rho u).deriv

private theorem rho_deriv_eq_poly {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    deriv rho u = 32 * u * (1 - u) * (1 - 2 * u) := by
  rw [rho_deriv_formula, if_pos hu]

private theorem rho_deriv_eq_zero_of_le_zero {u : ℝ} (hu : u ≤ 0) : deriv rho u = 0 := by
  rcases hu.lt_or_eq with hu | rfl
  · have h : u ∉ Icc (0 : ℝ) 1 := fun ⟨h, _⟩ => (not_le_of_gt hu) h
    simp [rho_deriv_formula, h]
  · norm_num [rho_deriv_formula]

private theorem rho_deriv_eq_zero_of_one_le {u : ℝ} (hu : 1 ≤ u) : deriv rho u = 0 := by
  rcases hu.lt_or_eq with hu | rfl
  · have h : u ∉ Icc (0 : ℝ) 1 := fun ⟨_, h⟩ => (not_le_of_gt hu) h
    simp [rho_deriv_formula, h]
  · norm_num [rho_deriv_formula]

private theorem hasDerivAt_rho_deriv {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (deriv rho) (32 - 192 * u * (1 - u)) u := by
  apply (hasDerivAt_rhoPolyD u).congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hu.1, gt_mem_nhds hu.2] with x hx0 hx1 using
    rho_deriv_eq_poly ⟨hx0.le, hx1.le⟩

private theorem continuous_rho_deriv : Continuous (deriv rho) := by
  refine continuous_iff_continuousAt.mpr fun u => ?_
  have hc : Continuous rhoPolyD := by unfold rhoPolyD; fun_prop
  by_cases hu0 : u < 0
  · apply (continuousAt_const (y := (0 : ℝ))).congr
    filter_upwards [gt_mem_nhds hu0] with x hx using (rho_deriv_eq_zero_of_le_zero hx.le).symm
  by_cases hu1 : 1 < u
  · apply (continuousAt_const (y := (0 : ℝ))).congr
    filter_upwards [lt_mem_nhds hu1] with x hx using (rho_deriv_eq_zero_of_one_le hx.le).symm
  rcases (le_of_not_gt hu0).eq_or_lt with rfl | hu0'
  · refine continuousAt_glue_le (continuousAt_const (y := (0 : ℝ))) hc.continuousAt ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with x hx using rho_deriv_eq_zero_of_le_zero hx
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with x hx hx1
      exact rho_deriv_eq_poly ⟨hx, hx1.le⟩
  rcases (le_of_not_gt hu1).eq_or_lt with rfl | hu1'
  · refine continuousAt_glue_le hc.continuousAt (continuousAt_const (y := (0 : ℝ))) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)] with x hx hx0
      exact rho_deriv_eq_poly ⟨hx0.le, hx⟩
    · filter_upwards [self_mem_nhdsWithin] with x hx using rho_deriv_eq_zero_of_one_le hx
  · apply hc.continuousAt.congr
    filter_upwards [lt_mem_nhds hu0', gt_mem_nhds hu1'] with x hx0 hx1 using
      (rho_deriv_eq_poly ⟨hx0.le, hx1.le⟩).symm

private theorem continuous_rho : Continuous rho :=
  continuous_iff_continuousAt.mpr fun u => (hasDerivAt_rho u).continuousAt

private theorem abs_deriv_rho_le (u : ℝ) : |deriv rho u| ≤ 4 := by
  by_cases hu : u ∈ Icc (0 : ℝ) 1
  · rw [rho_deriv_eq_poly hu]
    let s := |1 - 2 * u|
    have hs0 : 0 ≤ s := abs_nonneg _
    have hs1 : s ≤ 1 := abs_le.mpr ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hs2 : s ^ 2 = (1 - 2 * u) ^ 2 := sq_abs _
    have h_eq : 32 * u * (1 - u) = 8 * (1 - s ^ 2) := by rw [hs2]; ring
    rw [abs_mul, h_eq, abs_of_nonneg (by nlinarith [hs0, hs1, mul_nonneg hs0 (sub_nonneg.mpr hs1)])]
    change 8 * (1 - s ^ 2) * s ≤ 4
    have hh : s * (1 - s) ≤ 1 / 4 := u_mul_one_sub_le
    have hn : 0 ≤ s * (1 - s) := mul_nonneg hs0 (sub_nonneg.mpr hs1)
    have h := mul_le_mul hh (show 1 + s ≤ 2 by linarith) (by linarith : 0 ≤ 1 + s)
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith only [h]
  · simp [rho_deriv_formula, hu]

private theorem abs_deriv_deriv_rho_le {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    |deriv (deriv rho) u| ≤ 32 := by
  rw [(hasDerivAt_rho_deriv hu).deriv, abs_le]
  have hu0 : 0 ≤ u * (1 - u) := mul_nonneg hu.1.le (sub_nonneg.mpr hu.2.le)
  have hu1 : u * (1 - u) ≤ 1 / 4 := u_mul_one_sub_le
  constructor <;> linarith

private theorem rho_eq_one_iff (u : ℝ) : rho u = 1 ↔ u = 1 / 2 := by
  refine ⟨fun h => ?_, fun h => h ▸ rho_half⟩
  by_cases hu : u ∈ Icc (0 : ℝ) 1
  · rw [rho_eq_poly hu] at h
    have hu0 : 0 ≤ u * (1 - u) := mul_nonneg hu.1 (sub_nonneg.mpr hu.2)
    have heq : u * (1 - u) = 1 / 4 := by
      have hm : (u * (1 - u) - 1 / 4) * (u * (1 - u) + 1 / 4) = 0 := by
        nlinarith only [h]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right (by linarith))
    have hz : (u - 1 / 2) ^ 2 = 0 := by nlinarith only [heq]
    by_contra hne
    exact (sq_pos_of_ne_zero (sub_ne_zero.mpr hne)).ne' hz
  · simp [rho, hu] at h

private theorem rho_contDiffOn : ContDiffOn ℝ 2 rho (Ioo (0 : ℝ) 1) := by
  have hc : ContDiff ℝ 2 rhoPoly := by unfold rhoPoly; fun_prop
  exact hc.contDiffOn.congr fun u hu => rho_eq_poly ⟨hu.1.le, hu.2.le⟩

private theorem claim_7_2_proof :
    ContDiffOn ℝ 2 rho (Set.Ioo 0 1) ∧
      ((∀ u, rho u ≤ 1) ∧ rho (1 / 2) = 1 ∧ ∀ u, rho u = 1 → u = 1 / 2) ∧
      (HasDerivAt rho 0 0 ∧ HasDerivAt rho 0 1) ∧
      (Differentiable ℝ rho ∧ ∀ u, |deriv rho u| ≤ 4) ∧
      (∀ u, u ≠ 0 → u ≠ 1 →
        DifferentiableAt ℝ (deriv rho) u ∧ |deriv (deriv rho) u| ≤ 32) := by
  refine ⟨rho_contDiffOn, ⟨rho_le_one, rho_half, fun u h => (rho_eq_one_iff u).mp h⟩,
      ⟨?_, ?_⟩, ⟨fun u => (hasDerivAt_rho u).differentiableAt, abs_deriv_rho_le⟩, ?_⟩
  · convert hasDerivAt_rho 0 using 1 <;> norm_num
  · convert hasDerivAt_rho 1 using 1 <;> norm_num
  intro u hu0 hu1
  by_cases hlo : u < 0
  · have hd := (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
        (f₁ := deriv rho) (by
          filter_upwards [gt_mem_nhds hlo] with x hx using rho_deriv_eq_zero_of_le_zero hx.le)
    exact ⟨hd.differentiableAt, by rw [hd.deriv]; norm_num⟩
  by_cases hhi : 1 < u
  · have hd := (hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq
        (f₁ := deriv rho) (by
          filter_upwards [lt_mem_nhds hhi] with x hx using rho_deriv_eq_zero_of_one_le hx.le)
    exact ⟨hd.differentiableAt, by rw [hd.deriv]; norm_num⟩
  have hu : u ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne (le_of_not_gt hlo) hu0.symm, lt_of_le_of_ne (le_of_not_gt hhi) hu1⟩
  exact ⟨(hasDerivAt_rho_deriv hu).differentiableAt, abs_deriv_deriv_rho_le hu⟩

end BilateralProfitLB
end BundlePart000

open BilateralProfitLB

theorem solution :
    ContDiffOn ℝ 2 rho (Set.Ioo 0 1) ∧
      ((∀ u, rho u ≤ 1) ∧ rho (1 / 2) = 1 ∧ ∀ u, rho u = 1 → u = 1 / 2) ∧
      (HasDerivAt rho 0 0 ∧ HasDerivAt rho 0 1) ∧
      (Differentiable ℝ rho ∧ ∀ u, |deriv rho u| ≤ 4) ∧
      (∀ u, u ≠ 0 → u ≠ 1 →
        DifferentiableAt ℝ (deriv rho) u ∧ |deriv (deriv rho) u| ≤ 32) := by
  exact BilateralProfitLB.claim_7_2_proof
