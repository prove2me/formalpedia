-- Prove2me | solution 1 for GRH.dirichlet_rectangle_nonzero_iff_finite_grid
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T15:07:06.967995+00:00
-- url     : https://prove2.me/submissions/c607b389-c984-46c7-a162-cde6b35777c5

import Definitions.Def_GRH_DirichletGrid
import Theorems.Thm_GRH_dirichlet_rectangle_tail_and_derivative_bounds
import Theorems.Thm_GRH_conductors_three_four_low_height_nonzero
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

open Complex Set Metric GRH.DirichletGrid

private lemma grid_mem {a b H : ℝ} (hab : a ≤ b) (hH : 0 ≤ H)
    {m i j : ℕ} (hm : 0 < m) (hi : i ≤ m) (hj : j ≤ m) :
    point a b H m i j ∈ reProdIm (Icc a b) (Icc (-H) H) := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  have unit (k : ℕ) (hk : k ≤ m) : 0 ≤ (k:ℝ)/m ∧ (k:ℝ)/m ≤ 1 :=
    ⟨by positivity, (div_le_one hm').2 (by exact_mod_cast hk)⟩
  obtain ⟨ui,vi⟩ := unit i hi
  obtain ⟨uj,vj⟩ := unit j hj
  change (a ≤ a+(b-a)*_ ∧ a+(b-a)*_ ≤ b) ∧ (-H ≤ -H+2*H*_ ∧ -H+2*H*_ ≤ H)
  constructor <;> constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hab) ui]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr vi)]
  · nlinarith [mul_nonneg hH uj]
  · nlinarith [mul_nonneg hH (sub_nonneg.mpr vj)]

private lemma round_interval {a b x : ℝ} (hx : x ∈ Icc a b) {m : ℕ} (hm : 0 < m) :
    ∃ i ≤ m, |x - (a + (b-a)*((i:ℝ)/m))| ≤ (b-a)/m := by
  have hm' : 0 < (m:ℝ) := by exact_mod_cast hm
  rcases eq_or_lt_of_le (hx.1.trans hx.2) with h | h
  · have e := le_antisymm hx.2 (h ▸ hx.1)
    subst b
    exact ⟨0, Nat.zero_le _, by simp_all⟩
  let v := (x-a)/(b-a)
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr h.le)
  have hv' : v ≤ 1 := (div_le_one (sub_pos.mpr h)).2 (by linarith [hx.2])
  have eqv : x-a = (b-a)*v := by dsimp [v]; field_simp
  let i := ⌊v*(m:ℝ)⌋₊
  have hi : (i:ℝ) ≤ v*m := Nat.floor_le (mul_nonneg hv hm'.le)
  have hi' : v*m < (i:ℝ)+1 := Nat.lt_floor_add_one _
  have im : i ≤ m := by exact_mod_cast hi.trans (by nlinarith : v*m ≤ (m:ℝ))
  have hlo : (i:ℝ)/m ≤ v := (div_le_iff₀ hm').2 hi
  have hhi : v-(i:ℝ)/m ≤ 1/m := by
    apply (le_div_iff₀ hm').2
    rw [sub_mul, div_mul_cancel₀ _ hm'.ne']
    linarith
  refine ⟨i,im, ?_⟩
  have hr : x-(a+(b-a)*((i:ℝ)/m)) = (b-a)*(v-(i:ℝ)/m) := by
    linear_combination eqv
  rw [hr, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr h.le) (sub_nonneg.mpr hlo))]
  simpa only [one_div, div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hhi (sub_nonneg.mpr h.le)

private lemma nearest {a b H : ℝ} (ha : (1/2:ℝ) ≤ a) (hb : b ≤ 1)
    {m : ℕ} (hm : 0 < m) {z : ℂ} (hz : z ∈ reProdIm (Icc a b) (Icc (-H) H)) :
    ∃ i ≤ m, ∃ j ≤ m, ‖z - point a b H m i j‖ ≤ (1+2*H)/m := by
  obtain ⟨i,hi,hx⟩ := round_interval hz.1 hm
  obtain ⟨j,hj,hy⟩ := round_interval hz.2 hm
  rw [show H- -H=2*H by ring] at hy
  refine ⟨i,hi,j,hj, (norm_le_abs_re_add_abs_im _).trans ?_⟩
  change |z.re - (a + (b-a)*((i:ℝ)/m))| + |z.im - (-H + 2*H*((j:ℝ)/m))| ≤ _
  apply (add_le_add hx hy).trans
  rw [← add_div]
  exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg m)

/-- Necessity uses the positive minimum on the closed rectangle. Sufficiency
uses a grid point, the Dirichlet tail, and Cauchy's estimate on radius 1/4. -/
theorem solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (a b H : ℝ) (ha : (1/2:ℝ) ≤ a) (hab : a ≤ b) (hb : b ≤ 1) (hH : 0 ≤ H) :
    (∀ z : ℂ, z ∈ reProdIm (Icc a b) (Icc (-H) H) → χ.LFunction z ≠ 0) ↔
      ∃ m : ℕ, GRH.DirichletGrid.Passes χ a b H m := by
  let K := reProdIm (Icc a b) (Icc (-H) H)
  have posT : 0 ≤ tailBudget q H := by unfold tailBudget; positivity
  have posD : 0 ≤ slopeBudget q H := by unfold slopeBudget; positivity
  constructor
  · intro hn
    have hc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
    have hx : (⟨a,0⟩ : ℂ) ∈ K := ⟨⟨le_rfl,hab⟩,⟨by simpa using neg_nonpos.mpr hH,hH⟩⟩
    obtain ⟨z,hz,hmin⟩ := hc.exists_isMinOn ⟨_,hx⟩
      (χ.differentiable_LFunction hχ).continuous.norm.continuousOn
    have hδ : 0 < ‖χ.LFunction z‖ := norm_pos_iff.mpr (hn z hz)
    obtain ⟨m,hm⟩ := exists_nat_gt (max 0 ((budget q H + tailBudget q H)/‖χ.LFunction z‖))
    have mpos : 0 < (m:ℝ) := (le_max_left ..).trans_lt hm
    have hmNat : 0 < m := by exact_mod_cast mpos
    have margin := (div_lt_iff₀ hδ).1 ((le_max_right ..).trans_lt hm)
    refine ⟨m,hmNat,fun i hi j hj => Or.inr ?_⟩
    let c := point a b H m i j
    have hcm := grid_mem hab hH hmNat hi hj
    have ht := (GRH.dirichlet_rectangle_tail_and_derivative_bounds q χ hχ ha hb hH hmNat hcm).1
    have tri := norm_add_le (χ.LFunction c - sample χ m c) (sample χ m c)
    rw [sub_add_cancel] at tri
    have hmin' : ‖χ.LFunction z‖ ≤ ‖χ.LFunction c‖ := hmin hcm
    have hd : (budget q H + tailBudget q H)/(m:ℝ) < ‖χ.LFunction z‖ :=
      (div_lt_iff₀ mpos).2 (by linarith)
    rw [add_div] at hd
    change budget q H / m < ‖sample χ m c‖
    change ‖χ.LFunction c - sample χ m c‖ ≤ _ at ht
    linarith
  · rintro ⟨m,hm,hpass⟩ z hz zero
    obtain ⟨i,hi,j,hj,hd⟩ := nearest ha hb hm hz
    let c := point a b H m i j
    have hc := grid_mem hab hH hm hi hj
    rcases hpass i hi j hj with ⟨hsmall,hsafe⟩ | hp
    · have him := Complex.abs_im_le_norm (z-c)
      have tri := abs_add_le (z.im-c.im) c.im
      rw [sub_add_cancel] at tri
      change |c.im| + (1+2*H)/m ≤ _ at hsafe
      change |z.im-c.im| ≤ ‖z-c‖ at him
      change ‖z-c‖ ≤ _ at hd
      exact GRH.conductors_three_four_low_height_nonzero q hsmall χ hχ z
        (ha.trans hz.1.1) (hz.1.2.trans hb) (by linarith) zero
    have conv : Convex ℝ K := ((convex_Icc a b).linear_preimage Complex.reLm).inter
      ((convex_Icc (-H) H).linear_preimage Complex.imLm)
    have hv : ‖χ.LFunction z - χ.LFunction c‖ ≤ slopeBudget q H * ‖z-c‖ :=
      conv.norm_image_sub_le_of_norm_deriv_le (fun w _ => χ.differentiableAt_LFunction w (.inr hχ))
        (fun _ hw => (GRH.dirichlet_rectangle_tail_and_derivative_bounds q χ hχ ha hb hH (m := 1) Nat.zero_lt_one hw).2) hc hz
    rw [zero, zero_sub, norm_neg] at hv
    have ht := (GRH.dirichlet_rectangle_tail_and_derivative_bounds q χ hχ ha hb hH hm hc).1
    have htri := norm_add_le (sample χ m c - χ.LFunction c) (χ.LFunction c)
    rw [sub_add_cancel, norm_sub_rev (sample χ m c)] at htri
    have hg := mul_le_mul_of_nonneg_left hd posD
    change budget q H / m < ‖sample χ m c‖ at hp
    change ‖χ.LFunction c - sample χ m c‖ ≤ _ at ht
    change slopeBudget q H * ‖z-c‖ ≤ _ at hg
    rw [budget, add_div, mul_div_assoc] at hp
    linarith
