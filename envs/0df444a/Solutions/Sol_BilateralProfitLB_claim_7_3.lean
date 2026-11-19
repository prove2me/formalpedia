-- Prove2me | solution 1 for BilateralProfitLB.claim_7_3
-- status  : ACCEPTED   (prove)
-- author  : @sim2000dg
-- created : 2026-11-18T13:12:23.090802+00:00
-- url     : https://prove2.me/submissions/8a380b6d-371e-4005-b239-da4d5f6c419d

import Mathlib
import Theorems.Thm_BilateralProfitLB_claim_7_2
import Definitions.Def_BilateralProfitLB_Construction
import Definitions.Def_BilateralProfitLB_Stochastic


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

private theorem abs_deriv_rho_le (u : ℝ) : |deriv rho u| ≤ 4 :=
  claim_7_2.2.2.2.1.2 u

end BilateralProfitLB
end BundlePart000


section BundlePart001


open Set Filter
open scoped Topology

namespace BilateralProfitLB

private theorem S0_eq_left {x : ℝ} (hx : x ≤ 1 / 4) : S0 x = 1 - 8 / 3 * x := by
  rw [S0, if_pos hx]

private theorem S0_eq_plateau {x : ℝ} (hx : x ∈ Icc (1/4 : ℝ) (1/2)) :
    S0 x = 1 / (48 * x ^ 2) := by
  rcases hx.1.eq_or_lt with rfl | h
  · norm_num [S0]
  · rw [S0, if_neg (not_le_of_gt h), if_pos hx.2]

private theorem S0_eq_right {x : ℝ} (hx : 1 / 2 ≤ x) : S0 x = (1 - x) / (12 * x) := by
  rcases hx.eq_or_lt with rfl | h
  · norm_num [S0]
  · rw [S0, if_neg (show ¬ x ≤ 1 / 4 by linarith), if_neg (not_le_of_gt h)]

private theorem S0_zero : S0 0 = 1 := by norm_num [S0]
private theorem S0_one : S0 1 = 0 := by norm_num [S0]

private theorem Y0_eq_plateau {x : ℝ} (hx : x ∈ Icc (1/4 : ℝ) (1/2)) :
    Y0 x = 48 * x ^ 2 := by
  simp only [Y0, S0_eq_plateau hx, one_div, inv_inv]

private theorem S0_nonneg {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ S0 x := by
  rcases le_or_gt x (1/4) with h | h
  · rw [S0_eq_left h]
    linarith
  rcases le_or_gt x (1/2) with h' | h'
  · rw [S0_eq_plateau ⟨h.le, h'⟩]
    positivity
  · rw [S0_eq_right h'.le]
    exact div_nonneg (sub_nonneg.mpr hx.2) (by positivity)

private theorem S0_pos {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) : 0 < S0 x := by
  rcases le_or_gt x (1/4) with h | h
  · rw [S0_eq_left h]
    linarith
  rcases le_or_gt x (1/2) with h' | h'
  · rw [S0_eq_plateau ⟨h.le, h'⟩]
    positivity
  · rw [S0_eq_right h'.le]
    exact div_pos (sub_pos.mpr hx.2) (by positivity)

private theorem hasDerivAt_S0_left (x : ℝ) :
    HasDerivAt (fun b : ℝ => 1 - 8 / 3 * b) (-(8/3)) x := by
  convert (hasDerivAt_const x (1 : ℝ)).sub ((hasDerivAt_id x).const_mul (8/3)) using 1
  all_goals first | rfl | (funext y; rfl) | norm_num

private theorem hasDerivAt_S0_middle {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun b : ℝ => 1 / (48 * b ^ 2)) (-1 / (24 * x ^ 3)) x := by
  have hd := ((hasDerivAt_id x).pow 2).const_mul (48 : ℝ)
  have hn : (48 : ℝ) * id x ^ 2 ≠ 0 := by simpa using hx
  convert (hasDerivAt_const x (1 : ℝ)).div hd hn using 1
  all_goals first | rfl | (funext y; rfl) | (norm_num [Pi.pow_apply, Pi.sub_apply, id_eq]; field_simp [hx]; ring)

private theorem hasDerivAt_S0_right {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun b : ℝ => (1 - b) / (12 * b)) (-1 / (12 * x ^ 2)) x := by
  have hd := (hasDerivAt_id x).const_mul (12 : ℝ)
  have hn : (12 : ℝ) * id x ≠ 0 := by simpa using hx
  convert ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).div hd hn using 1
  all_goals first | rfl | (funext y; rfl) | (norm_num [Pi.pow_apply, Pi.sub_apply, id_eq]; field_simp [hx]; ring)

private noncomputable def S0D (x : ℝ) : ℝ :=
  if x ≤ 1 / 4 then -(8/3) else if x ≤ 1 / 2 then -1 / (24 * x ^ 3) else -1 / (12 * x ^ 2)

private theorem S0D_eq_left {x : ℝ} (hx : x ≤ 1 / 4) : S0D x = -(8/3) := by
  rw [S0D, if_pos hx]

private theorem S0D_eq_middle {x : ℝ} (hx : x ∈ Icc (1/4 : ℝ) (1/2)) :
    S0D x = -1 / (24 * x ^ 3) := by
  rcases hx.1.eq_or_lt with rfl | h
  · norm_num [S0D]
  · rw [S0D, if_neg (not_le_of_gt h), if_pos hx.2]

private theorem S0D_eq_right {x : ℝ} (hx : 1 / 2 ≤ x) :
    S0D x = -1 / (12 * x ^ 2) := by
  rcases hx.eq_or_lt with rfl | h
  · norm_num [S0D]
  · rw [S0D, if_neg (show ¬ x ≤ 1 / 4 by linarith), if_neg (not_le_of_gt h)]

private theorem hasDerivAt_S0D (x : ℝ) : HasDerivAt S0 (S0D x) x := by
  rcases lt_trichotomy x (1/4) with hx | rfl | hx
  · rw [S0D_eq_left hx.le]
    apply (hasDerivAt_S0_left x).congr_of_eventuallyEq
    filter_upwards [gt_mem_nhds hx] with b hb using S0_eq_left hb.le
  · rw [S0D_eq_left le_rfl]
    refine hasDerivAt_glue_le (hasDerivAt_S0_left (1/4))
      (g := fun b : ℝ => 1 / (48 * b ^ 2)) ?_ ?_ ?_
    · convert hasDerivAt_S0_middle (x := 1/4) (by norm_num) using 1 <;> norm_num
    · filter_upwards [self_mem_nhdsWithin] with b hb using S0_eq_left hb
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (1/4 : ℝ) < 1/2))] with b hb hb'
      exact S0_eq_plateau ⟨hb, hb'.le⟩
  rcases lt_trichotomy x (1/2) with hy | rfl | hy
  · rw [S0D_eq_middle ⟨hx.le, hy.le⟩]
    apply (hasDerivAt_S0_middle (show x ≠ 0 by linarith)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx, gt_mem_nhds hy] with b hb hb' using
      S0_eq_plateau ⟨hb.le, hb'.le⟩
  · rw [S0D_eq_right le_rfl]
    refine hasDerivAt_glue_le (f := fun b : ℝ => 1 / (48 * b ^ 2)) ?_
      (hasDerivAt_S0_right (x := 1/2) (by norm_num)) ?_ ?_
    · convert hasDerivAt_S0_middle (x := 1/2) (by norm_num) using 1 <;> norm_num
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (1/4 : ℝ) < 1/2))] with b hb hb'
      exact S0_eq_plateau ⟨hb'.le, hb⟩
    · filter_upwards [self_mem_nhdsWithin] with b hb using S0_eq_right hb
  · rw [S0D_eq_right hy.le]
    apply (hasDerivAt_S0_right (show x ≠ 0 by linarith)).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hy] with b hb using S0_eq_right hb.le

private theorem S0_deriv_left {x : ℝ} (hx : x ≤ 1 / 4) : deriv S0 x = -(8/3) := by
  rw [(hasDerivAt_S0D x).deriv, S0D_eq_left hx]

private theorem S0_deriv_middle {x : ℝ} (hx : x ∈ Icc (1/4 : ℝ) (1/2)) :
    deriv S0 x = -1 / (24 * x ^ 3) := by
  rw [(hasDerivAt_S0D x).deriv, S0D_eq_middle hx]

private theorem S0_deriv_right {x : ℝ} (hx : 1 / 2 ≤ x) : deriv S0 x = -1 / (12 * x ^ 2) := by
  rw [(hasDerivAt_S0D x).deriv, S0D_eq_right hx]

private theorem S0_hasDerivAt (x : ℝ) : HasDerivAt S0 (deriv S0 x) x := by
  rw [(hasDerivAt_S0D x).deriv]
  exact hasDerivAt_S0D x

private theorem S0_continuous : Continuous S0 :=
  continuous_iff_continuousAt.mpr fun x => (S0_hasDerivAt x).continuousAt

private theorem S0_deriv_neg (x : ℝ) : deriv S0 x < 0 := by
  rcases le_or_gt x (1/4) with h | h
  · rw [S0_deriv_left h]
    norm_num
  have hx0 : 0 < x := by linarith
  rcases le_or_gt x (1/2) with h' | h'
  · rw [S0_deriv_middle ⟨h.le, h'⟩]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  · rw [S0_deriv_right h'.le]
    exact div_neg_of_neg_of_pos (by norm_num) (by positivity)

private theorem S0_deriv_continuous : Continuous (deriv S0) := by
  refine continuous_iff_continuousAt.mpr fun x => ?_
  have hm (b : ℝ) (hb : 0 < b) :
      ContinuousAt (fun y : ℝ => -1 / (24 * y ^ 3)) b := by fun_prop (disch := positivity)
  have hr (b : ℝ) (hb : 0 < b) :
      ContinuousAt (fun y : ℝ => -1 / (12 * y ^ 2)) b := by fun_prop (disch := positivity)
  rcases lt_trichotomy x (1/4) with hx | rfl | hx
  · apply (continuousAt_const (y := (-(8/3) : ℝ))).congr
    filter_upwards [gt_mem_nhds hx] with b hb using (S0_deriv_left hb.le).symm
  · refine continuousAt_glue_le (continuousAt_const (y := (-(8/3) : ℝ)))
      (hm (1/4) (by norm_num)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with b hb using S0_deriv_left hb
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (1/4 : ℝ) < 1/2))] with b hb hb'
      exact S0_deriv_middle ⟨hb, hb'.le⟩
  rcases lt_trichotomy x (1/2) with hy | rfl | hy
  · apply (hm x (by linarith)).congr
    filter_upwards [lt_mem_nhds hx, gt_mem_nhds hy] with b hb hb' using
      (S0_deriv_middle ⟨hb.le, hb'.le⟩).symm
  · refine continuousAt_glue_le (hm (1/2) (by norm_num)) (hr (1/2) (by norm_num)) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (lt_mem_nhds (by norm_num : (1/4 : ℝ) < 1/2))] with b hb hb'
      exact S0_deriv_middle ⟨hb'.le, hb⟩
    · filter_upwards [self_mem_nhdsWithin] with b hb using S0_deriv_right hb
  · apply (hr x (by linarith)).congr
    filter_upwards [lt_mem_nhds hy] with b hb using (S0_deriv_right hb.le).symm

end BilateralProfitLB
end BundlePart001


section BundlePart002


namespace BilateralProfitLB

private theorem w_pos {K : ℕ} (hK : 0 < K) : 0 < w K := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold w
  positivity

private theorem w_le_quarter {K : ℕ} (hK : 0 < K) : w K ≤ 1 / 4 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  unfold w
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

private theorem cast_mul_w {K : ℕ} (hK : 0 < K) : (K : ℝ) * w K = 1 / 4 := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold w
  field_simp

private theorem a_ge_quarter {K j : ℕ} (hj : 1 ≤ j) : 1 / 4 ≤ a K j := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hw : 0 ≤ w K := by unfold w; positivity
  unfold a
  linarith [mul_nonneg (sub_nonneg.mpr hjr) hw]

private theorem endpoint_le_half {K j : ℕ} (hK : 0 < K) (hj : j ≤ K) :
    a K j + w K ≤ 1 / 2 := by
  have hjr : (j : ℝ) ≤ K := by exact_mod_cast hj
  have hmul := mul_le_mul_of_nonneg_right hjr (w_pos hK).le
  unfold a
  linarith [cast_mul_w hK]

private theorem I_subset {K j : ℕ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) :
    I K j ⊆ Set.Ioo (1 / 4 : ℝ) (1 / 2) := by
  have hK : 0 < K := lt_of_lt_of_le (by decide : 0 < 1) (hj₁.trans hj₂)
  intro q hq
  exact ⟨(a_ge_quarter hj₁).trans_lt hq.1, hq.2.trans_le (endpoint_le_half hK hj₂)⟩

private theorem qstar_mem {K j : ℕ} (hK : 0 < K) : qstar K j ∈ I K j := by
  have hw := w_pos hK
  change a K j < a K j + w K / 2 ∧ a K j + w K / 2 < a K j + w K
  exact ⟨by linarith, by linarith⟩

private theorem normalized_qstar {K j : ℕ} (hK : 0 < K) : (qstar K j - a K j) / w K = 1 / 2 := by
  unfold qstar
  apply (div_eq_iff (w_pos hK).ne').mpr
  ring

private theorem I_pairwiseDisjoint (K : ℕ) : Pairwise (fun i j => Disjoint (I K i) (I K j)) := by
  intro i j hij
  have hw : 0 ≤ w K := by unfold w; positivity
  suffices ordered : ∀ {k l : ℕ}, k < l → Disjoint (I K k) (I K l) by
    rcases lt_or_gt_of_ne hij with h | h
    · exact ordered h
    · exact (ordered h).symm
  intro k l hkl
  have hcast : (k : ℝ) + 1 ≤ l := by exact_mod_cast hkl
  have hmul := mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ l - 1 by linarith) hw
  apply Set.disjoint_left.mpr
  intro q hk hl
  have hkq : q < a K k + w K := hk.2
  have hql : a K l < q := hl.1
  unfold a at hkq hql
  nlinarith

open Classical in
private theorem sum_interval_visits_le (K T : ℕ) (s : Finset ℕ) (q : Fin T → ℝ) :
    ∑ j ∈ s, (Finset.univ.filter fun t => q t ∈ I K j).card ≤ T := by
  let visits (j : ℕ) := Finset.univ.filter fun t => q t ∈ I K j
  have hd : (s : Set ℕ).PairwiseDisjoint visits := by
    intro i _ j _ hij
    refine Finset.disjoint_left.mpr fun t hi hj => ?_
    exact Set.disjoint_left.mp (I_pairwiseDisjoint K hij)
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
  change ∑ j ∈ s, (visits j).card ≤ T
  rw [← Finset.card_biUnion hd]
  simpa using Finset.card_le_univ (s.biUnion visits)

private theorem Delta_eq {K : ℕ} (hK : 0 < K) : Delta K = 1 / (73728 * (K : ℝ) ^ 2) := by
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  unfold Delta w
  field_simp
  ring

private theorem Delta_pos {K : ℕ} (hK : 0 < K) : 0 < Delta K := by
  have hw := w_pos hK
  unfold Delta
  positivity

open Classical in
private theorem sum_outside_interval_gap (K j T : ℕ) (q : Fin T → ℝ) :
    (∑ t : Fin T, Set.indicator (I K j)ᶜ (fun _ => Delta K) (q t)) =
      ((T : ℝ) - ((Finset.univ.filter fun t => q t ∈ I K j).card : ℝ)) * Delta K := by
  have hi (t : Fin T) : Set.indicator (I K j)ᶜ (fun _ => Delta K) (q t) =
      Delta K - if q t ∈ I K j then Delta K else 0 := by
    by_cases ht : q t ∈ I K j
    · simp [Set.indicator, ht]
    · simp [Set.indicator, ht]
  simp_rw [hi]
  rw [Finset.sum_sub_distrib, ← Finset.sum_filter]
  simp [nsmul_eq_mul, sub_mul]

end BilateralProfitLB
end BundlePart002


section BundlePart003



open Set Filter
open scoped Topology

namespace BilateralProfitLB

private theorem S_eq_outside {K j : ℕ} {x : ℝ} (hx : x ∉ I K j) : S K j x = S0 x := by
  simp [S, hx]

private theorem S_eq_inside {K j : ℕ} {x : ℝ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) (hx : x ∈ I K j) :
    S K j x = 1 / Y K j x := by
  simp [S, hj₁, hj₂, hx]

private theorem S_eq_baseline_of_invalid {K j : ℕ} (hj : ¬ (1 ≤ j ∧ j ≤ K)) : S K j = S0 := by
  funext x
  have h : ¬ (1 ≤ j ∧ j ≤ K ∧ x ∈ I K j) := fun h => hj ⟨h.1, h.2.1⟩
  simp [S, h]

private theorem Y_bounds {K j : ℕ} {x : ℝ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) (hx : x ∈ I K j) :
    2 ≤ Y K j x ∧ Y K j x ≤ 12 := by
  have hp := I_subset hj₁ hj₂ hx
  have hK : 0 < K := by omega
  have hw := w_pos hK
  have hw' := w_le_quarter hK
  have hp0 : 0 < x := by linarith [hp.1]
  have hw2 : w K ^ 2 ≤ 1 / 16 := by
    have hh := mul_le_mul hw' hw' hw.le (by norm_num : (0 : ℝ) ≤ 1 / 4)
    nlinarith only [hh]
  have hl : 3 ≤ 48 * x ^ 2 := by
    have hh := mul_le_mul hp.1.le hp.1.le (by norm_num : (0 : ℝ) ≤ 1 / 4) hp0.le
    nlinarith only [hh]
  have hu : 48 * x ^ 2 ≤ 12 := by
    have hh := mul_le_mul hp.2.le hp.2.le hp0.le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    nlinarith only [hh]
  unfold Y
  rw [Y0_eq_plateau ⟨hp.1.le, hp.2.le⟩]
  have hr0 := rho_nonneg ((x - a K j) / w K)
  have hr1 := rho_le_one ((x - a K j) / w K)
  have hprod₀ := mul_nonneg (sq_nonneg (w K)) hr0
  have hprod₁ := mul_le_mul_of_nonneg_left hr1 (sq_nonneg (w K))
  constructor <;> linarith

private theorem Y_pos {K j : ℕ} {x : ℝ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) (hx : x ∈ I K j) :
    0 < Y K j x :=
  (by norm_num : (0 : ℝ) < 2).trans_le (Y_bounds hj₁ hj₂ hx).1

private noncomputable def bump (K j : ℕ) (x : ℝ) : ℝ :=
  if 1 ≤ j ∧ j ≤ K then 1 / 2 * w K ^ 2 * rho ((x - a K j) / w K) else 0

private noncomputable def bumpD (K j : ℕ) (x : ℝ) : ℝ :=
  if 1 ≤ j ∧ j ≤ K then 1 / 2 * w K * deriv rho ((x - a K j) / w K) else 0

private theorem hasDerivAt_normalized (K j : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (y - a K j) / w K) (1 / w K) x := by
  have hd := ((hasDerivAt_id x).sub (hasDerivAt_const x (a K j))).div_const (w K)
  convert hd using 1
  all_goals first | rfl | simp

private theorem hasDerivAt_bump (K j : ℕ) (x : ℝ) :
    HasDerivAt (bump K j) (bumpD K j x) x := by
  change HasDerivAt
    (fun y => if 1 ≤ j ∧ j ≤ K then 1 / 2 * w K ^ 2 * rho ((y - a K j) / w K) else 0)
    (if 1 ≤ j ∧ j ≤ K then 1 / 2 * w K * deriv rho ((x - a K j) / w K) else 0) x
  by_cases hj : 1 ≤ j ∧ j ≤ K
  · have hw : w K ≠ 0 := (w_pos (by omega : 0 < K)).ne'
    simp only [if_pos hj]
    have hd := (hasDerivAt_rho ((x - a K j) / w K)).differentiableAt.hasDerivAt
    convert (hd.comp x (hasDerivAt_normalized K j x)).const_mul (1 / 2 * w K ^ 2) using 1
    all_goals first | rfl | (field_simp [hw] <;> ring)
  · simpa only [if_neg hj] using hasDerivAt_const x (0 : ℝ)

private theorem bumpD_continuous (K j : ℕ) : Continuous (bumpD K j) := by
  change Continuous (fun x : ℝ => if 1 ≤ j ∧ j ≤ K then
     1 / 2 * w K * deriv rho ((x - a K j) / w K) else 0)
  by_cases hj : 1 ≤ j ∧ j ≤ K
  · simp only [if_pos hj]
    apply continuous_const.mul
    apply continuous_rho_deriv.comp
    fun_prop
  · simpa only [if_neg hj] using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

private theorem normalized_not_mem {K j : ℕ} {x : ℝ} (hK : 0 < K) (hx : x ∉ I K j) :
    (x - a K j) / w K ≤ 0 ∨ 1 ≤ (x - a K j) / w K := by
  have hw := w_pos hK
  by_cases h : x ≤ a K j
  · exact Or.inl (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) hw.le)
  · right
    apply (le_div_iff₀ hw).mpr
    have hu : a K j + w K ≤ x := by
      by_contra ht
      exact hx ⟨lt_of_not_ge h, lt_of_not_ge ht⟩
    linarith

private theorem bump_zero_pair {K j : ℕ} {x : ℝ} (hx : ¬ (1 ≤ j ∧ j ≤ K ∧ x ∈ I K j)) :
    bump K j x = 0 ∧ bumpD K j x = 0 := by
  by_cases hj : 1 ≤ j ∧ j ≤ K
  · have hI : x ∉ I K j := fun h => hx ⟨hj.1, hj.2, h⟩
    rcases normalized_not_mem (by omega : 0 < K) hI with hl | hr
    · simp [bump, bumpD, hj, rho_eq_zero_of_le_zero hl, rho_deriv_eq_zero_of_le_zero hl]
    · simp [bump, bumpD, hj, rho_eq_zero_of_one_le hr, rho_deriv_eq_zero_of_one_le hr]
  · simp [bump, bumpD, hj]

private theorem survival_denom_eq {K j : ℕ} {x : ℝ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K)
    (hx : x ∈ I K j) : 1 - S0 x * bump K j x = S0 x * Y K j x := by
  have hp := I_subset hj₁ hj₂ hx
  have hs : S0 x ≠ 0 := (S0_pos ⟨by linarith [hp.1], by linarith [hp.2]⟩).ne'
  simp only [bump, if_pos (show 1 ≤ j ∧ j ≤ K from ⟨hj₁, hj₂⟩), Y, Y0, mul_sub, one_div, mul_inv_cancel₀ hs]

private theorem survival_denom_pos (K j : ℕ) (x : ℝ) : 0 < 1 - S0 x * bump K j x := by
  by_cases hx : 1 ≤ j ∧ j ≤ K ∧ x ∈ I K j
  · have hp := I_subset hx.1 hx.2.1 hx.2.2
    rw [survival_denom_eq hx.1 hx.2.1 hx.2.2]
    exact mul_pos (S0_pos ⟨by linarith [hp.1], by linarith [hp.2]⟩) (Y_pos hx.1 hx.2.1 hx.2.2)
  · simp [(bump_zero_pair hx).1]

-- This quotient agrees with the two survival branches and is smooth across the bump endpoints.
private theorem S_eq_quotient (K j : ℕ) :
    S K j = fun x => S0 x / (1 - S0 x * bump K j x) := by
  funext x
  by_cases hx : 1 ≤ j ∧ j ≤ K ∧ x ∈ I K j
  · have hp := I_subset hx.1 hx.2.1 hx.2.2
    have hs : S0 x ≠ 0 := (S0_pos ⟨by linarith [hp.1], by linarith [hp.2]⟩).ne'
    have hy := (Y_pos hx.1 hx.2.1 hx.2.2).ne'
    rw [S_eq_inside hx.1 hx.2.1 hx.2.2, survival_denom_eq hx.1 hx.2.1 hx.2.2]
    field_simp
  · simp only [S, if_neg hx, (bump_zero_pair hx).1, mul_zero, sub_zero, div_one]

private theorem S_hasDerivAt_formula (K j : ℕ) (x : ℝ) :
    HasDerivAt (S K j)
      ((deriv S0 x + S0 x ^ 2 * bumpD K j x) / (1 - S0 x * bump K j x) ^ 2) x := by
  rw [S_eq_quotient]
  have hd := (hasDerivAt_const x (1 : ℝ)).sub ((S0_hasDerivAt x).mul (hasDerivAt_bump K j x))
  convert (S0_hasDerivAt x).div hd (survival_denom_pos K j x).ne' using 1
  all_goals first | rfl | (simp only [Pi.sub_apply, Pi.mul_apply]; congr 1; ring)

private theorem S_hasDerivAt (K j : ℕ) (x : ℝ) : HasDerivAt (S K j) (deriv (S K j) x) x :=
  (S_hasDerivAt_formula K j x).differentiableAt.hasDerivAt

private theorem S_continuous (K j : ℕ) : Continuous (S K j) :=
  continuous_iff_continuousAt.mpr fun x => (S_hasDerivAt K j x).continuousAt

private theorem S_nonneg (K j : ℕ) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) : 0 ≤ S K j x := by
  rw [S_eq_quotient]
  exact div_nonneg (S0_nonneg hx) (survival_denom_pos K j x).le

private theorem S_pos (K j : ℕ) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) : 0 < S K j x := by
  rw [S_eq_quotient]
  exact div_pos (S0_pos hx) (survival_denom_pos K j x)

private theorem S_zero (K j : ℕ) : S K j 0 = 1 := by
  by_cases hx : 1 ≤ j ∧ j ≤ K ∧ (0 : ℝ) ∈ I K j
  · have hp := (I_subset hx.1 hx.2.1 hx.2.2).1
    norm_num at hp
  · simp [S, hx, S0_zero]

private theorem S_one (K j : ℕ) : S K j 1 = 0 := by
  simp only [S_eq_quotient, S0_one, zero_div]

private theorem fB_continuous (K j : ℕ) : Continuous (fB K j) := by
  have hfun : fB K j = fun x =>
      -((deriv S0 x + S0 x ^ 2 * bumpD K j x) / (1 - S0 x * bump K j x) ^ 2) := by
    funext x
    rw [fB, (S_hasDerivAt_formula K j x).deriv]
  rw [hfun]
  have hD : Continuous (bump K j) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_bump K j x).continuousAt
  have hn : Continuous fun x => deriv S0 x + S0 x ^ 2 * bumpD K j x :=
    S0_deriv_continuous.add ((S0_continuous.pow 2).mul (bumpD_continuous K j))
  have hd : Continuous fun x => (1 - S0 x * bump K j x) ^ 2 :=
    (continuous_const.sub (S0_continuous.mul hD)).pow 2
  exact (hn.div hd fun x => pow_ne_zero 2 (survival_denom_pos K j x).ne').neg

private theorem fB_eq_baseline_of_outside {K j : ℕ} {x : ℝ}
    (hx : ¬ (1 ≤ j ∧ j ≤ K ∧ x ∈ I K j)) : fB K j x = -deriv S0 x := by
  unfold fB
  rw [(S_hasDerivAt_formula K j x).deriv]
  simp [(bump_zero_pair hx).1, (bump_zero_pair hx).2]

private theorem hasDerivAt_Y_inside {K j : ℕ} {x : ℝ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K)
    (hx : x ∈ I K j) :
    HasDerivAt (Y K j)
      (96 * x - 1 / 2 * w K * deriv rho ((x - a K j) / w K)) x := by
  have hp := I_subset hj₁ hj₂ hx
  have hbase : HasDerivAt Y0 (96 * x) x := by
    have hd := ((hasDerivAt_id x).pow 2).const_mul (48 : ℝ)
    have hb : HasDerivAt (fun y : ℝ => 48 * y ^ 2) (96 * x) x := by
      convert hd using 1
      all_goals first | rfl | (norm_num [id_eq]; ring)
    apply hb.congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hp.1, gt_mem_nhds hp.2] with y hy hy'
    exact Y0_eq_plateau ⟨hy.le, hy'.le⟩
  have hh := hbase.sub (hasDerivAt_bump K j x)
  have he : Y K j = Y0 - bump K j := by
    funext y
    simp only [Y, bump, if_pos (show 1 ≤ j ∧ j ≤ K from ⟨hj₁, hj₂⟩), Pi.sub_apply]
  rwa [← he, bumpD, if_pos (show 1 ≤ j ∧ j ≤ K from ⟨hj₁, hj₂⟩)] at hh

private theorem Y_deriv_pos {K j : ℕ} {x : ℝ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) (hx : x ∈ I K j) :
    0 < deriv (Y K j) x := by
  rw [(hasDerivAt_Y_inside hj₁ hj₂ hx).deriv]
  have hK : 0 < K := by omega
  have hp := I_subset hj₁ hj₂ hx
  have hh := mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (abs_deriv_rho_le ((x - a K j) / w K)))
    (show 0 ≤ 1 / 2 * w K by positivity [w_pos hK])
  linarith [hp.1, w_le_quarter hK]

private theorem fB_eq_inside {K j : ℕ} {x : ℝ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) (hx : x ∈ I K j) :
    fB K j x = deriv (Y K j) x / Y K j x ^ 2 := by
  have hd := (hasDerivAt_Y_inside hj₁ hj₂ hx).differentiableAt.hasDerivAt
  have hinv := (hasDerivAt_const x (1 : ℝ)).div hd (Y_pos hj₁ hj₂ hx).ne'
  have hs :
      HasDerivAt (S K j) (-(deriv (Y K j) x / Y K j x ^ 2)) x := by
    apply (show HasDerivAt (fun y => 1 / Y K j y) (-(deriv (Y K j) x / Y K j x ^ 2)) x by
      convert hinv using 1
      all_goals first | rfl | simp [neg_div]).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds hx.1, gt_mem_nhds hx.2] with y hy hy'
    exact S_eq_inside hj₁ hj₂ ⟨hy, hy'⟩
  rw [fB, hs.deriv, neg_neg]

private theorem fB_pos (K j : ℕ) (x : ℝ) : 0 < fB K j x := by
  by_cases hx : 1 ≤ j ∧ j ≤ K ∧ x ∈ I K j
  · rw [fB_eq_inside hx.1 hx.2.1 hx.2.2]
    exact div_pos (Y_deriv_pos hx.1 hx.2.1 hx.2.2) (pow_pos (Y_pos hx.1 hx.2.1 hx.2.2) 2)
  · rw [fB_eq_baseline_of_outside hx]
    exact neg_pos.mpr (S0_deriv_neg x)

end BilateralProfitLB
end BundlePart003


section BundlePart004



open Set MeasureTheory
open scoped ENNReal

namespace BilateralProfitLB

private theorem fB_intervalIntegrable (K j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fB K j) volume a b :=
  (fB_continuous K j).intervalIntegrable _ _

private theorem integral_fB_eq (K j : ℕ) (a b : ℝ) :
    ∫ x in a..b, fB K j x = S K j a - S K j b := by
  have hd (x : ℝ) : HasDerivAt (fun y => -S K j y) (fB K j x) x :=
    (S_hasDerivAt K j x).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (fB_intervalIntegrable K j a b)]
  ring

private theorem lintegral_fB_Icc (K j : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ∫⁻ x in Icc a b, ENNReal.ofReal (fB K j x) =
      ENNReal.ofReal (S K j a - S K j b) := by
  have hi : Integrable (fB K j) (volume.restrict (Icc a b)) :=
    (fB_continuous K j).continuousOn.integrableOn_compact isCompact_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => (fB_pos K j x).le),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, integral_fB_eq]

private theorem buyerMeasure_Ici (K j : ℕ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ((volume.restrict (Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b))
      (Ici q) = ENNReal.ofReal (S K j q) := by
  have hh : Ici q ∩ Icc (0 : ℝ) 1 = Icc q 1 := by
    ext b
    exact ⟨fun ⟨h, _, h₁⟩ => ⟨h, h₁⟩, fun ⟨h, h₁⟩ => ⟨h, hq.1.trans h, h₁⟩⟩
  rw [withDensity_apply _ measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    hh, lintegral_fB_Icc K j hq.2, S_one, sub_zero]

private theorem buyerMeasure_Ici_real (K j : ℕ) {q : ℝ} (hq : q ∈ Icc (0 : ℝ) 1) :
    ((volume.restrict (Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b)).real
      (Ici q) = S K j q := by
  rw [Measure.real, buyerMeasure_Ici K j hq, ENNReal.toReal_ofReal (S_nonneg K j hq)]

private theorem buyerMeasure_isProbabilityMeasure (K j : ℕ) :
    IsProbabilityMeasure
      ((volume.restrict (Icc (0 : ℝ) 1)).withDensity fun b => ENNReal.ofReal (fB K j b)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_fB_Icc K j zero_le_one, S_zero, S_one, sub_zero, ENNReal.ofReal_one]

private theorem sellerMeasure_isProbabilityMeasure :
    IsProbabilityMeasure (volume.restrict (Icc (0 : ℝ) 1)) := by
  constructor
  simp

private theorem law_isProbabilityMeasure (K j : ℕ) : IsProbabilityMeasure (law K j) := by
  letI := sellerMeasure_isProbabilityMeasure
  letI := buyerMeasure_isProbabilityMeasure K j
  unfold law
  infer_instance

private theorem law_supported (K j : ℕ) :
    law K j ((Icc (0 : ℝ) 1) ×ˢ Icc (0 : ℝ) 1) = 1 := by
  letI := sellerMeasure_isProbabilityMeasure
  letI := buyerMeasure_isProbabilityMeasure K j
  rw [law, Measure.prod_prod]
  have hs : (volume.restrict (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) = 1 := by
    simp [Measure.restrict_apply, measurableSet_Icc]
  have hb : ((volume.restrict (Icc (0 : ℝ) 1)).withDensity
          fun b => ENNReal.ofReal (fB K j b)) (Icc (0 : ℝ) 1) = 1 := by
    rw [withDensity_apply _ measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
      inter_self, lintegral_fB_Icc K j zero_le_one, S_zero, S_one, sub_zero, ENNReal.ofReal_one]
  rw [hs, hb, one_mul]

end BilateralProfitLB
end BundlePart004


section BundlePart005


open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace BilateralProfitLB

open MechanismDesign.BilateralTrade

private theorem monotoneOn_Icc_join {f : ℝ → ℝ} {c d e : ℝ}
    (hf₁ : MonotoneOn f (Icc c d)) (hf₂ : MonotoneOn f (Icc d e)) :
    MonotoneOn f (Icc c e) := by
  intro x hx y hy hxy
  by_cases hxd : d ≤ x
  · exact hf₂ ⟨hxd, hx.2⟩ ⟨hxd.trans hxy, hy.2⟩ hxy
  by_cases hyd : y ≤ d
  · exact hf₁ ⟨hx.1, hxy.trans hyd⟩ ⟨hy.1, hyd⟩ hxy
  have hxl := (lt_of_not_ge hxd).le
  have hyl := (lt_of_not_ge hyd).le
  calc
    f x ≤ f d := hf₁ ⟨hx.1, hxl⟩ ⟨hx.1.trans hxl, le_rfl⟩ hxl
    _ ≤ f y := hf₂ ⟨le_rfl, hyl.trans hy.2⟩ ⟨hyl, hy.2⟩ hyl

private theorem monotoneOn_Icc_patch {f g : ℝ → ℝ} {l a b r : ℝ}
    (hla : l ≤ a) (hab : a ≤ b) (hbr : b ≤ r)
    (hg : MonotoneOn g (Icc l r)) (hf : MonotoneOn f (Icc a b))
    (heq : ∀ x ∉ Ioo a b, f x = g x) : MonotoneOn f (Icc l r) := by
  apply monotoneOn_Icc_join (d := a)
  · intro x hx y hy hxy
    rw [heq x (fun h => (not_lt_of_ge hx.2) h.1), heq y (fun h => (not_lt_of_ge hy.2) h.1)]
    exact hg ⟨hx.1, hx.2.trans (hab.trans hbr)⟩ ⟨hy.1, hy.2.trans (hab.trans hbr)⟩ hxy
  · apply monotoneOn_Icc_join (d := b) hf
    intro x hx y hy hxy
    rw [heq x (fun h => (not_lt_of_ge hx.1) h.2), heq y (fun h => (not_lt_of_ge hy.1) h.2)]
    exact hg ⟨hla.trans (hab.trans hx.1), hx.2⟩ ⟨hla.trans (hab.trans hy.1), hy.2⟩ hxy

private noncomputable def phi0 (x : ℝ) : ℝ := x - S0 x / (-deriv S0 x)

private theorem phi0_left {x : ℝ} (hx : x ≤ 1 / 4) : phi0 x = 2 * x - 3 / 8 := by
  rw [phi0, S0_eq_left hx, S0_deriv_left hx]
  ring

private theorem phi0_middle {x : ℝ} (hx : x ∈ Icc (1/4 : ℝ) (1/2)) :
    phi0 x = x / 2 := by
  have hn : x ≠ 0 := by linarith [hx.1]
  rw [phi0, S0_eq_plateau hx, S0_deriv_middle hx]
  field_simp [hn]
  <;> ring

private theorem phi0_right {x : ℝ} (hx : 1 / 2 ≤ x) : phi0 x = x ^ 2 := by
  have hn : x ≠ 0 := by linarith
  rw [phi0, S0_eq_right hx, S0_deriv_right hx]
  field_simp [hn]
  <;> ring

private theorem phi0_monotone : MonotoneOn phi0 (Icc (0 : ℝ) 1) := by
  apply monotoneOn_Icc_join (d := 1/4)
  · intro x hx y hy hxy
    rw [phi0_left hx.2, phi0_left hy.2]
    linarith
  apply monotoneOn_Icc_join (d := 1/2)
  · intro x hx y hy hxy
    rw [phi0_middle hx, phi0_middle hy]
    linarith
  · intro x hx y hy hxy
    rw [phi0_right hx.1, phi0_right hy.1]
    have h₀ : 0 ≤ x := by linarith [hx.1]
    have h₁ : 0 ≤ y := by linarith [hy.1]
    exact pow_le_pow_left₀ h₀ hxy 2

private theorem normalized_mem {K j : ℕ} {x : ℝ} (hK : 0 < K) (hx : x ∈ I K j) :
    (x - a K j) / w K ∈ Ioo (0 : ℝ) 1 := by
  have hw := w_pos hK
  exact ⟨div_pos (sub_pos.mpr hx.1) hw, (div_lt_iff₀ hw).mpr (by linarith [hx.2])⟩

private theorem hasDerivAt_Y_deriv_inside {K j : ℕ} {x : ℝ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K)
    (hx : x ∈ I K j) :
    HasDerivAt (deriv (Y K j))
      (96 - (32 - 192 * ((x - a K j) / w K) * (1 - (x - a K j) / w K)) / 2) x := by
  have hK : 0 < K := by omega
  have hn := normalized_mem hK hx
  have hd := (hasDerivAt_rho_deriv hn).comp x (hasDerivAt_normalized K j x)
  have hpoly :=
    ((hasDerivAt_id x).const_mul (96 : ℝ)).sub (hd.const_mul (1 / 2 * w K))
  have hp : HasDerivAt
      (fun y => 96 * y - 1 / 2 * w K * deriv rho ((y - a K j) / w K))
      (96 - (32 - 192 * ((x - a K j) / w K) * (1 - (x - a K j) / w K)) / 2) x := by
    convert hpoly using 1
    all_goals first | rfl | (field_simp [(w_pos hK).ne'] <;> ring)
  apply hp.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hx.1, gt_mem_nhds hx.2] with y hy hy'
  exact (hasDerivAt_Y_inside hj₁ hj₂ ⟨hy, hy'⟩).deriv

private theorem Y_curvature_pos {K j : ℕ} {x : ℝ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) (hx : x ∈ I K j) :
    0 < deriv (deriv (Y K j)) x := by
  have hK : 0 < K := by omega
  have hn := normalized_mem hK hx
  rw [(hasDerivAt_Y_deriv_inside hj₁ hj₂ hx).deriv]
  have hh := mul_nonneg hn.1.le (sub_nonneg.mpr hn.2.le)
  linarith

private noncomputable def phi (K j : ℕ) (x : ℝ) : ℝ := x - S K j x / fB K j x

private theorem phi_continuous (K j : ℕ) : Continuous (phi K j) :=
  continuous_id.sub ((S_continuous K j).div (fB_continuous K j) (fun x => (fB_pos K j x).ne'))

private theorem phi_eq_phi0_of_outside {K j : ℕ} {x : ℝ}
    (hx : ¬ (1 ≤ j ∧ j ≤ K ∧ x ∈ I K j)) : phi K j x = phi0 x := by
  rw [phi, phi0, fB_eq_baseline_of_outside hx]
  simp [S, hx]

private theorem phi_eq_inside {K j : ℕ} {x : ℝ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K) (hx : x ∈ I K j) :
    phi K j x = x - Y K j x / deriv (Y K j) x := by
  rw [phi, S_eq_inside hj₁ hj₂ hx, fB_eq_inside hj₁ hj₂ hx]
  field_simp [(Y_pos hj₁ hj₂ hx).ne', (Y_deriv_pos hj₁ hj₂ hx).ne']

private theorem phi_hasDerivAt_inside {K j : ℕ} {x : ℝ} (hj₁ : 1 ≤ j) (hj₂ : j ≤ K)
    (hx : x ∈ I K j) :
    HasDerivAt (phi K j)
      (Y K j x * deriv (deriv (Y K j)) x / deriv (Y K j) x ^ 2) x := by
  have hd := (hasDerivAt_Y_inside hj₁ hj₂ hx).differentiableAt.hasDerivAt
  have hdd := (hasDerivAt_Y_deriv_inside hj₁ hj₂ hx).differentiableAt.hasDerivAt
  have hquot := hd.div hdd (Y_deriv_pos hj₁ hj₂ hx).ne'
  have hp : HasDerivAt (fun y => y - Y K j y / deriv (Y K j) y)
      (Y K j x * deriv (deriv (Y K j)) x / deriv (Y K j) x ^ 2) x := by
    convert (hasDerivAt_id x).sub hquot using 1
    all_goals first | rfl | (field_simp [(Y_deriv_pos hj₁ hj₂ hx).ne'] <;> ring)
  apply hp.congr_of_eventuallyEq
  filter_upwards [lt_mem_nhds hx.1, gt_mem_nhds hx.2] with y hy hy'
  exact phi_eq_inside hj₁ hj₂ ⟨hy, hy'⟩

private theorem phi_monotone (K j : ℕ) : MonotoneOn (phi K j) (Icc (0 : ℝ) 1) := by
  by_cases hj : 1 ≤ j ∧ j ≤ K
  · have hK : 0 < K := by omega
    have hw := w_pos hK
    have hla : (0 : ℝ) ≤ a K j := by linarith [a_ge_quarter (K := K) hj.1]
    have hbr : a K j + w K ≤ (1 : ℝ) := by linarith [endpoint_le_half hK hj.2]
    apply monotoneOn_Icc_patch (a := a K j) (b := a K j + w K)
      hla (by linarith : a K j ≤ a K j + w K) hbr phi0_monotone
    · apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) (phi_continuous K j).continuousOn
      · rw [interior_Icc]
        intro x hx
        exact (phi_hasDerivAt_inside hj.1 hj.2 hx).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro x hx
        rw [(phi_hasDerivAt_inside hj.1 hj.2 hx).deriv]
        exact (div_nonneg (mul_nonneg (Y_pos hj.1 hj.2 hx).le (Y_curvature_pos hj.1 hj.2 hx).le)
          (sq_nonneg _))
    · exact fun x hx => phi_eq_phi0_of_outside fun h => hx h.2.2
  · intro x hx y hy hxy
    rw [phi_eq_phi0_of_outside (fun h => hj ⟨h.1, h.2.1⟩),
      phi_eq_phi0_of_outside (fun h => hj ⟨h.1, h.2.1⟩)]
    exact phi0_monotone hx hy hxy

private noncomputable def hardEnv (K j : ℕ) : Environment :=
  { uniformEnv with
    fB := fB K j
    fB_measurable := (fB_continuous K j).measurable
    fB_pos := fun x _ => fB_pos K j x
    fB_intervalIntegrable := fB_intervalIntegrable K j 0 1
    fB_integral := by
      change (∫ x in (0 : ℝ)..(1 : ℝ), fB K j x) = 1
      rw [integral_fB_eq, S_zero, S_one, sub_zero] }

private theorem hardEnv_survival (K j : ℕ) (x : ℝ) :
    1 - (hardEnv K j).cdfB x = S K j x := by
  change 1 - (∫ t in (0 : ℝ)..x, fB K j t) = _
  rw [integral_fB_eq, S_zero]
  ring

private theorem hardEnv_prior (K j : ℕ) : (hardEnv K j).prior = law K j := by
  change (volume.restrict (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)).withDensity
      (fun z => ENNReal.ofReal (1 * fB K j z.2)) = law K j
  unfold law
  rw [prod_withDensity_right ((fB_continuous K j).measurable.ennreal_ofReal),
    Measure.prod_restrict, ← Measure.volume_eq_prod]
  simp

private theorem hardEnv_regular (K j : ℕ) : (hardEnv K j).Regular := by
  constructor
  · intro x hx y hy hxy
    change x + (∫ _ : ℝ in (0 : ℝ)..x, (1 : ℝ)) / 1 ≤
      y + (∫ _ : ℝ in (0 : ℝ)..y, (1 : ℝ)) / 1
    simp
    linarith
  · have hphi : (hardEnv K j).psiB = phi K j := by
      funext x
      rw [Environment.psiB, hardEnv_survival]
      rfl
    rw [hphi]
    exact phi_monotone K j

private theorem claim_7_3_proof (K : ℕ) (_hK : 1 ≤ K) (j : ℕ) (_hj : j ≤ K) :
    ∃ E : Environment, UnitSupport E ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, E.fS x = 1) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, E.fB b = fB K j b) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, 1 - E.cdfB b = S K j b) ∧
      E.prior = law K j ∧ E.Regular := by
  refine ⟨hardEnv K j, ⟨rfl, rfl, rfl, rfl⟩, fun x hx => rfl, fun b hb => rfl,
    fun x hx => hardEnv_survival K j x, hardEnv_prior K j, hardEnv_regular K j⟩

end BilateralProfitLB
end BundlePart005

open BilateralProfitLB
open MechanismDesign.BilateralTrade

theorem solution (K : ℕ) (hK : 1 ≤ K) (j : ℕ) (hj : j ≤ K) :
    ∃ E : Environment, UnitSupport E ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1, E.fS x = 1) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, E.fB b = fB K j b) ∧
      (∀ b ∈ Set.Icc (0 : ℝ) 1, 1 - E.cdfB b = S K j b) ∧
      E.prior = law K j ∧ E.Regular := by
  exact BilateralProfitLB.claim_7_3_proof K hK j hj
