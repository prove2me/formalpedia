-- Prove2me | solution 1 for ErrBoundQG.Structured.theorem_4_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T01:30:20.826954+00:00
-- url     : https://prove2.me/submissions/3868db58-7448-4eae-b69a-8b53cfbde007

import Mathlib
import Definitions.Def_ErrBoundQG_Structured_Setting

set_option autoImplicit false

open scoped InnerProductSpace

namespace PE093

lemma ereal_step (e1 e2 : EReal) (s a b : ℝ) (hgs : e1 + (s : EReal) ≤ e2)
    (hab : a ≤ s + b) : e1 + (a : EReal) ≤ e2 + (b : EReal) := by
  calc e1 + (a : EReal) ≤ e1 + ((s + b : ℝ) : EReal) := by
        gcongr
    _ = (e1 + (s : EReal)) + (b : EReal) := by rw [EReal.coe_add, add_assoc]
    _ ≤ e2 + (b : EReal) := by gcongr

lemma ereal_cancel (e : EReal) (he : e ≠ ⊤) (hb : e ≠ ⊥) (a b : ℝ)
    (h : e + (a : EReal) ≤ e + (b : EReal)) : a ≤ b := by
  rw [← EReal.coe_toReal he hb, ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h
  linarith

lemma ne_top_of_le (e1 e2 : EReal) (a b : ℝ) (h : e1 + (a : EReal) ≤ e2 + (b : EReal))
    (h2 : e2 ≠ ⊤) : e1 ≠ ⊤ := by
  intro h1
  rw [h1, EReal.top_add_coe] at h
  exact (ne_of_lt (EReal.add_lt_top h2 (EReal.coe_ne_top b))) (top_le_iff.mp h)


lemma gconv_real {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (g : V → EReal)
    (hgb : ∀ x, g x ≠ ⊥)
    (hgc : ∀ (x y : V) (t : ℝ), 0 < t → t < 1 →
      g ((1 - t) • x + t • y) ≤ ((1 - t : ℝ) : EReal) * g x + ((t : ℝ) : EReal) * g y)
    (y1 y2 : V) (r1 r2 α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (h1 : g y1 ≤ (r1 : EReal)) (h2 : g y2 ≤ (r2 : EReal)) :
    g (α • y1 + β • y2) ≤ ((α * r1 + β * r2 : ℝ) : EReal) := by
  rcases eq_or_lt_of_le hβ with hb0 | hbpos
  · have : α = 1 := by linarith
    subst this; rw [← hb0]; simpa using h1
  rcases eq_or_lt_of_le hα with ha0 | hapos
  · have : β = 1 := by linarith
    subst this; rw [← ha0]; simpa using h2
  have hβ1 : β < 1 := by linarith
  have e : α = 1 - β := by linarith
  have h1t : g y1 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r1) h1
  have h2t : g y2 ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r2) h2
  have hs1 := EReal.coe_toReal h1t (hgb y1)
  have hs2 := EReal.coe_toReal h2t (hgb y2)
  have hc := hgc y1 y2 β hbpos hβ1
  rw [← hs1, ← hs2] at hc
  rw [← hs1] at h1; rw [← hs2] at h2
  rw [EReal.coe_le_coe_iff] at h1 h2
  rw [e]
  refine hc.trans ?_
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have : 0 ≤ 1 - β := by linarith
  nlinarith


lemma cvx_norm_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) :
    ConvexOn ℝ Set.univ (fun y : V => ‖y - a‖) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ α β hα hβ hαβ
  have e : α • x + β • y - a = α • (x - a) + β • (y - a) := by
    have ha' : a = α • a + β • a := by rw [← add_smul, hαβ, one_smul]
    conv_lhs => rw [ha']
    simp only [smul_sub]; abel
  simp only [smul_eq_mul]
  rw [e]
  calc ‖α • (x - a) + β • (y - a)‖ ≤ ‖α • (x - a)‖ + ‖β • (y - a)‖ := norm_add_le _ _
    _ = α * ‖x - a‖ + β * ‖y - a‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg hα, Real.norm_of_nonneg hβ]

lemma cvx_sq_sub {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) :
    ConvexOn ℝ Set.univ (fun y : V => ‖y - a‖ ^ 2) :=
  (cvx_norm_sub a).pow (fun _ _ => norm_nonneg _) 2


lemma ereal_shift (e1 e2 : EReal) (a1 a2 b1 b2 : ℝ)
    (h : e1 + (a1 : EReal) ≤ e2 + (a2 : EReal)) (hb : b1 - a1 ≤ b2 - a2) :
    e1 + (b1 : EReal) ≤ e2 + (b2 : EReal) := by
  calc e1 + (b1 : EReal) = (e1 + (a1 : EReal)) + ((b1 - a1 : ℝ) : EReal) := by
        rw [add_assoc, ← EReal.coe_add]; congr 2; ring
    _ ≤ (e2 + (a2 : EReal)) + ((b1 - a1 : ℝ) : EReal) := by gcongr
    _ ≤ (e2 + (a2 : EReal)) + ((b2 - a2 : ℝ) : EReal) := by
        gcongr
    _ = e2 + (b2 : EReal) := by rw [add_assoc, ← EReal.coe_add]; congr 2; ring

lemma cvx_q {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (k : ℝ) (hk : 0 ≤ k) :
    ConvexOn ℝ Set.univ (fun y : V => k * ‖y - a‖ ^ 2) := by
  simpa [smul_eq_mul] using (cvx_sq_sub a).smul hk

lemma cvx_n {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a : V) (k : ℝ) (hk : 0 ≤ k) :
    ConvexOn ℝ Set.univ (fun y : V => k * ‖y - a‖) := by
  simpa [smul_eq_mul] using (cvx_norm_sub a).smul hk


lemma exists_global_min {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ProperSpace V] (F : V → EReal) (hF : LowerSemicontinuous F) (a : V) (R : ℝ) (hR : 0 ≤ R)
    (hout : ∀ y, R < ‖y - a‖ → F a ≤ F y) : ∃ p, ‖p - a‖ ≤ R ∧ ∀ y, F p ≤ F y := by
  obtain ⟨p, hp, hmin⟩ := (hF.lowerSemicontinuousOn (Metric.closedBall a R)).exists_isMinOn
    ⟨a, Metric.mem_closedBall_self hR⟩ (isCompact_closedBall a R)
  rw [isMinOn_iff] at hmin
  refine ⟨p, by simpa [dist_eq_norm] using hp, fun y => ?_⟩
  by_cases hy : y ∈ Metric.closedBall a R
  · exact hmin y hy
  · have : R < ‖y - a‖ := by simpa [dist_eq_norm] using hy
    exact (hmin a (Metric.mem_closedBall_self hR)).trans (hout y this)

lemma lsc_aux {V : Type*} [TopologicalSpace V] (g : V → EReal) (hgc : LowerSemicontinuous g)
    (f : V → ℝ) (hf : Continuous f) :
    LowerSemicontinuous (fun y => g y + ((f y : ℝ) : EReal)) :=
  LowerSemicontinuous.add' hgc (continuous_coe_real_ereal.comp hf).lowerSemicontinuous
    (fun _ => EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _)))

open ErrBoundQG.Structured

/-- L3: variational inequality at a minimizer of (smooth) + (proper convex). -/
lemma vi_of_min {n : ℕ} (H : E n → ℝ) (g : E n → EReal)
    (hg : RockafellarMaxMono.Shared.ProperConvex g) (x : E n)
    (hH : DifferentiableAt ℝ H x) (hgx : g x ≠ ⊤)
    (hmin : ∀ u, g x + (H x : EReal) ≤ g u + (H u : EReal)) (u : E n) :
    g x + ((⟪-gradient H x, u - x⟫_ℝ : ℝ) : EReal) ≤ g u := by
  by_cases hgu : g u = ⊤
  · rw [hgu]; exact le_top
  set a := (g x).toReal with ha_def
  set b := (g u).toReal with hb_def
  have ha : g x = (a : EReal) := (EReal.coe_toReal hgx (hg.1 x)).symm
  have hb : g u = (b : EReal) := (EReal.coe_toReal hgu (hg.1 u)).symm
  have key : ∀ s : ℝ, 0 < s → s < 1 → a - b ≤ s⁻¹ * (H (x + s • (u - x)) - H x) := by
    intro s hs0 hs1
    have hc := gconv_real g hg.1 hg.2.2 x u a b (1 - s) s (by linarith) hs0.le (by ring)
      ha.le hb.le
    have hm := hmin ((1 - s) • x + s • u)
    have e : (1 - s) • x + s • u = x + s • (u - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e] at hc hm
    have h3 : (a : EReal) + (H x : EReal) ≤
        (((1 - s) * a + s * b : ℝ) : EReal) + (H (x + s • (u - x)) : EReal) := by
      rw [← ha]; exact hm.trans (add_le_add hc le_rfl)
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    rw [← div_eq_inv_mul, le_div_iff₀ hs0]; nlinarith
  have h1 : HasDerivAt (fun s : ℝ => x + s • (u - x)) (u - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (u - x)).const_add x
  have h2 : HasFDerivAt H (fderiv ℝ H x) (x + (0 : ℝ) • (u - x)) := by
    simpa using hH.hasFDerivAt
  have hd := h2.comp_hasDerivAt (0 : ℝ) h1
  have e : fderiv ℝ H x (u - x) = ⟪gradient H x, u - x⟫_ℝ := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [e] at hd
  have ht := hd.tendsto_slope_zero_right
  have hle : a - b ≤ ⟪gradient H x, u - x⟫_ℝ := by
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    have := key s hs.1 hs.2
    simpa [Function.comp, smul_eq_mul] using this
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_neg_left]
  linarith

/-- L1: linear growth outside a ball containing the minimizer set. -/
lemma level_growth {n : ℕ} (φ : E n → EReal) (hlsc : LowerSemicontinuous φ)
    (hcvx : ∀ (x y : E n) (t : ℝ), 0 < t → t < 1 →
      φ ((1 - t) • x + t • y) ≤ ((1 - t : ℝ) : EReal) * φ x + ((t : ℝ) : EReal) * φ y)
    (hbot : ∀ x, φ x ≠ ⊥)
    (x0 : E n) (φs : ℝ) (hx0 : φ x0 = φs) (hmin : ∀ x, (φs : EReal) ≤ φ x)
    (R : ℝ) (hR : 0 < R) (hS : ∀ x, φ x ≤ φs → ‖x - x0‖ < R) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x, R ≤ ‖x - x0‖ → ((φs + δ * (‖x - x0‖ / R) : ℝ) : EReal) ≤ φ x := by
  by_cases hK : (Metric.sphere x0 R).Nonempty
  swap
  · refine ⟨1, one_pos, fun x hx => ?_⟩
    exfalso; apply hK
    have hpos : 0 < ‖x - x0‖ := lt_of_lt_of_le hR hx
    refine ⟨x0 + (R / ‖x - x0‖) • (x - x0), ?_⟩
    rw [mem_sphere_iff_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg
      (div_nonneg hR.le hpos.le), div_mul_cancel₀ _ hpos.ne']
  obtain ⟨y, hyK, hymin⟩ := (hlsc.lowerSemicontinuousOn (Metric.sphere x0 R)).exists_isMinOn
    hK (isCompact_sphere x0 R)
  rw [isMinOn_iff] at hymin
  have hyR : ‖y - x0‖ = R := by simpa [dist_eq_norm] using hyK
  have hlt : (φs : EReal) < φ y := by
    by_contra hc; push_neg at hc
    have := hS y hc; linarith
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  have hr1' : φs < r := EReal.coe_lt_coe_iff.mp hr1
  refine ⟨r - φs, by linarith, fun x hx => ?_⟩
  have hpos : 0 < ‖x - x0‖ := lt_of_lt_of_le hR hx
  set ρ := ‖x - x0‖ with hρ
  set s := R / ρ with hs
  have hs0 : 0 < s := div_pos hR hpos
  have hs1 : s ≤ 1 := (div_le_one hpos).mpr hx
  have hyx : ∀ z ∈ Metric.sphere x0 R, (r : EReal) ≤ φ z := fun z hz => hr2.le.trans (hymin z hz)
  by_cases hxt : φ x = ⊤
  · rw [hxt]; exact le_top
  set v := (φ x).toReal
  have hv : φ x = (v : EReal) := (EReal.coe_toReal hxt (hbot x)).symm
  rw [hv, EReal.coe_le_coe_iff]
  rcases eq_or_lt_of_le hs1 with he | hlt1
  · have hxK : x ∈ Metric.sphere x0 R := by
      rw [mem_sphere_iff_norm]
      have : R = ρ := by
        have := he; rw [hs, div_eq_one_iff_eq hpos.ne'] at this; exact this
      rw [this]
    have := hyx x hxK
    rw [hv, EReal.coe_le_coe_iff] at this
    have : ρ / R = 1 := by
      rw [hs, div_eq_one_iff_eq hpos.ne'] at he; rw [he, div_self hpos.ne']
    rw [this]; linarith
  · set z := (1 - s) • x0 + s • x
    have hzK : z ∈ Metric.sphere x0 R := by
      rw [mem_sphere_iff_norm]
      have : z - x0 = s • (x - x0) := by
        simp only [z, sub_smul, one_smul, smul_sub]; abel
      rw [this, norm_smul, Real.norm_of_nonneg hs0.le, hs, div_mul_cancel₀ _ hpos.ne']
    have h1 := hyx z hzK
    have h2 := hcvx x0 x s hs0 hlt1
    have h3 : (r : EReal) ≤ (((1 - s) * φs + s * v : ℝ) : EReal) := by
      refine h1.trans (h2.trans ?_)
      rw [hv, hx0, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    rw [EReal.coe_le_coe_iff] at h3
    have e2 : ρ / R = s⁻¹ := by rw [hs, inv_div]
    rw [e2]
    have : (r - φs) * s⁻¹ ≤ v - φs := by
      rw [← div_eq_mul_inv, div_le_iff₀ hs0]; nlinarith
    linarith

/-- derivative of `s ↦ H (x + s • d)` at 0 for differentiable `H`. -/
lemma line_deriv {n : ℕ} (H : E n → ℝ) (x : E n) (hH : DifferentiableAt ℝ H x) (d : E n) :
    HasDerivAt (fun s : ℝ => H (x + s • d)) ⟪gradient H x, d⟫_ℝ 0 := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • d) d 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add x
  have h2 : HasFDerivAt H (fderiv ℝ H x) (x + (0 : ℝ) • d) := by
    simpa using hH.hasFDerivAt
  have hd := h2.comp_hasDerivAt (0 : ℝ) h1
  have e : fderiv ℝ H x d = ⟪gradient H x, d⟫_ℝ := by
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [e] at hd
  exact hd

/-- derivative of the prox quadratic along a line. -/
lemma line_deriv_sq {n : ℕ} (z x d : E n) (t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun s : ℝ => ‖x + s • d - z‖ ^ 2 / (2 * t)) ⟪t⁻¹ • (x - z), d⟫_ℝ 0 := by
  have e : (fun s : ℝ => ‖x + s • d - z‖ ^ 2 / (2 * t)) =
      fun s : ℝ => (‖x - z‖ ^ 2 + 2 * ⟪x - z, d⟫_ℝ * s + s ^ 2 * ‖d‖ ^ 2) / (2 * t) := by
    funext s
    rw [show x + s • d - z = (x - z) + s • d by abel, norm_add_sq_real, inner_smul_right,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [e]
  have h := ((((hasDerivAt_const (0 : ℝ) (‖x - z‖ ^ 2)).add
    ((hasDerivAt_id' (0 : ℝ)).const_mul (2 * ⟪x - z, d⟫_ℝ))).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (‖d‖ ^ 2))).div_const (2 * t))
  refine h.congr_deriv ?_
  rw [real_inner_smul_left]; field_simp; ring

/-- L3 (line form): variational inequality at a minimizer of H + g. -/
lemma vi_line {n : ℕ} (H : E n → ℝ) (g : E n → EReal)
    (hg : RockafellarMaxMono.Shared.ProperConvex g) (x v : E n)
    (hH : ∀ d, HasDerivAt (fun s : ℝ => H (x + s • d)) ⟪v, d⟫_ℝ 0) (hgx : g x ≠ ⊤)
    (hmin : ∀ u, g x + (H x : EReal) ≤ g u + (H u : EReal)) (u : E n) :
    g x + ((⟪-v, u - x⟫_ℝ : ℝ) : EReal) ≤ g u := by
  by_cases hgu : g u = ⊤
  · rw [hgu]; exact le_top
  set a := (g x).toReal with ha_def
  set b := (g u).toReal with hb_def
  have ha : g x = (a : EReal) := (EReal.coe_toReal hgx (hg.1 x)).symm
  have hb : g u = (b : EReal) := (EReal.coe_toReal hgu (hg.1 u)).symm
  have key : ∀ s : ℝ, 0 < s → s < 1 → a - b ≤ s⁻¹ * (H (x + s • (u - x)) - H x) := by
    intro s hs0 hs1
    have hc := gconv_real g hg.1 hg.2.2 x u a b (1 - s) s (by linarith) hs0.le (by ring)
      ha.le hb.le
    have hm := hmin ((1 - s) • x + s • u)
    have e : (1 - s) • x + s • u = x + s • (u - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e] at hc hm
    have h3 : (a : EReal) + (H x : EReal) ≤
        (((1 - s) * a + s * b : ℝ) : EReal) + (H (x + s • (u - x)) : EReal) := by
      rw [← ha]; exact hm.trans (add_le_add hc le_rfl)
    rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    rw [← div_eq_inv_mul, le_div_iff₀ hs0]; nlinarith
  have ht := (hH (u - x)).tendsto_slope_zero_right
  have hle : a - b ≤ ⟪v, u - x⟫_ℝ := by
    refine ge_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    have := key s hs.1 hs.2
    simpa [Function.comp, smul_eq_mul] using this
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_neg_left]
  linarith

/-- gradient inequality for a convex function with line derivatives. -/
lemma grad_ineq {n : ℕ} (F : E n → ℝ) (hF : ConvexOn ℝ Set.univ F) (x v : E n)
    (hH : ∀ d, HasDerivAt (fun s : ℝ => F (x + s • d)) ⟪v, d⟫_ℝ 0) (u : E n) :
    F x + ⟪v, u - x⟫_ℝ ≤ F u := by
  have key : ∀ s : ℝ, 0 < s → s < 1 → s⁻¹ * (F (x + s • (u - x)) - F x) ≤ F u - F x := by
    intro s hs0 hs1
    have hc := hF.2 (Set.mem_univ x) (Set.mem_univ u) (by linarith : (0:ℝ) ≤ 1 - s) hs0.le
      (by ring)
    have e : (1 - s) • x + s • u = x + s • (u - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [e, smul_eq_mul, smul_eq_mul] at hc
    rw [← div_eq_inv_mul, div_le_iff₀ hs0]; nlinarith
  have ht := (hH (u - x)).tendsto_slope_zero_right
  have hle : ⟪v, u - x⟫_ℝ ≤ F u - F x := by
    refine le_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with s hs
    have := key s hs.1 hs.2
    simpa [Function.comp, smul_eq_mul] using this
  linarith

lemma pos_mul_ne_bot (c : ℝ) (hc : 0 < c) (e : EReal) (he : e ≠ ⊥) : (c : EReal) * e ≠ ⊥ := by
  induction e using EReal.rec with
  | bot => exact absurd rfl he
  | top => rw [EReal.mul_top_of_pos (by exact_mod_cast hc)]; exact bot_lt_top.ne'
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _

section Prim
variable {m n : ℕ}

lemma phi_bot (f : E m → ℝ) (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (A : E n →L[ℝ] E m) (x : E n) : primalObj f g A x ≠ ⊥ := by
  unfold primalObj
  exact EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hg.1 x⟩

lemma phi_lsc (f : E m → ℝ) (hf : Continuous f) (g : E n → EReal) (hgc : LowerSemicontinuous g)
    (A : E n →L[ℝ] E m) : LowerSemicontinuous (primalObj f g A) := by
  have := lsc_aux g hgc (fun x => f (A x)) (hf.comp A.continuous)
  have e : primalObj f g A = fun y => g y + ((f (A y) : ℝ) : EReal) := by
    funext y; unfold primalObj; rw [add_comm]
  rw [e]; exact this

lemma phi_cvx (f : E m → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (g : E n → EReal)
    (hg : RockafellarMaxMono.Shared.ProperConvex g) (A : E n →L[ℝ] E m)
    (x y : E n) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    primalObj f g A ((1 - t) • x + t • y) ≤
      ((1 - t : ℝ) : EReal) * primalObj f g A x + ((t : ℝ) : EReal) * primalObj f g A y := by
  have h1t : (0 : ℝ) < 1 - t := by linarith
  by_cases hx : g x = ⊤
  · have : ((1 - t : ℝ) : EReal) * primalObj f g A x = ⊤ := by
      unfold primalObj
      rw [hx, EReal.coe_add_top, EReal.mul_top_of_pos (by exact_mod_cast h1t)]
    rw [this, EReal.top_add_of_ne_bot (pos_mul_ne_bot t ht0 _ (phi_bot f g hg A y))]
    exact le_top
  by_cases hy : g y = ⊤
  · have : ((t : ℝ) : EReal) * primalObj f g A y = ⊤ := by
      unfold primalObj
      rw [hy, EReal.coe_add_top, EReal.mul_top_of_pos (by exact_mod_cast ht0)]
    rw [this, EReal.add_top_of_ne_bot (pos_mul_ne_bot (1 - t) h1t _ (phi_bot f g hg A x))]
    exact le_top
  set a := (g x).toReal
  set b := (g y).toReal
  have ha : g x = (a : EReal) := (EReal.coe_toReal hx (hg.1 x)).symm
  have hb : g y = (b : EReal) := (EReal.coe_toReal hy (hg.1 y)).symm
  have hc := gconv_real g hg.1 hg.2.2 x y a b (1 - t) t h1t.le ht0.le (by ring) ha.le hb.le
  have hfc := hfconv.2 (Set.mem_univ (A x)) (Set.mem_univ (A y)) h1t.le ht0.le (by ring)
  rw [smul_eq_mul, smul_eq_mul] at hfc
  have eA : A ((1 - t) • x + t • y) = (1 - t) • A x + t • A y := by
    rw [map_add, map_smul, map_smul]
  unfold primalObj
  rw [ha, hb, eA, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul, ← EReal.coe_mul,
    ← EReal.coe_add]
  calc ((f ((1 - t) • A x + t • A y) : ℝ) : EReal) + g ((1 - t) • x + t • y)
      ≤ ((f ((1 - t) • A x + t • A y) : ℝ) : EReal) + (((1 - t) * a + t * b : ℝ) : EReal) :=
        add_le_add le_rfl hc
    _ ≤ (((1 - t) * (f (A x) + a) + t * (f (A y) + b) : ℝ) : EReal) := by
        rw [← EReal.coe_add, EReal.coe_le_coe_iff]; nlinarith

lemma grad_comp (f : E m → ℝ) (A : E n →L[ℝ] E m) (x : E n)
    (hf : DifferentiableAt ℝ f (A x)) :
    HasGradientAt (fun z => f (A z)) (ContinuousLinearMap.adjoint A (gradient f (A x))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 := hf.hasFDerivAt.comp x A.hasFDerivAt
  refine h1.congr_fderiv ?_
  ext u
  rw [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left, gradient,
    InnerProductSpace.toDual_symm_apply]
  rfl

/-- dividing the prox minimality by t. -/
lemma ereal_div_t (t : ℝ) (ht : 0 < t) (a b : EReal) (ha : a ≠ ⊥) (hb : b ≠ ⊥) (q1 q2 : ℝ)
    (h : (t : EReal) * a + (q1 : EReal) ≤ (t : EReal) * b + (q2 : EReal)) :
    a + ((q1 / t : ℝ) : EReal) ≤ b + ((q2 / t : ℝ) : EReal) := by
  by_cases hbt : b = ⊤
  · rw [hbt, EReal.top_add_coe]; exact le_top
  by_cases hat : a = ⊤
  · exfalso
    rw [hat, EReal.mul_top_of_pos (by exact_mod_cast ht), EReal.top_add_coe] at h
    have : (t : EReal) * b + (q2 : EReal) ≠ ⊤ := by
      rw [← EReal.coe_toReal hbt hb, ← EReal.coe_mul, ← EReal.coe_add]; exact EReal.coe_ne_top _
    exact this (top_le_iff.mp h)
  rw [← EReal.coe_toReal hat ha, ← EReal.coe_toReal hbt hb] at h ⊢
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff] at h
  rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have : a.toReal + q1 / t ≤ b.toReal + q2 / t := by
    have h2 : (t * a.toReal + q1) / t ≤ (t * b.toReal + q2) / t := div_le_div_of_nonneg_right h ht.le
    rw [add_div, add_div, mul_div_cancel_left₀ _ ht.ne', mul_div_cancel_left₀ _ ht.ne'] at h2
    exact h2
  exact this

/-- (c) the prox step: `g p` finite and the variational inequality. -/
lemma prox_vi (f : E m → ℝ) (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (A : E n →L[ℝ] E m) (t : ℝ) (ht : 0 < t) (x p : E n) (hp : IsProxGradStep f g A t x p) :
    g p ≠ ⊤ ∧ ∀ u, g p + ((⟪-(t⁻¹ • (p - (x - t • gradient (fun z => f (A z)) x))), u - p⟫_ℝ : ℝ)
      : EReal) ≤ g u := by
  set z := x - t • gradient (fun z => f (A z)) x
  obtain ⟨x1, hx1⟩ := hg.2.1
  have hgp : g p ≠ ⊤ := by
    intro hpt
    have h := hp x1
    beta_reduce at h
    rw [hpt, EReal.mul_top_of_pos (by exact_mod_cast ht), EReal.top_add_coe] at h
    have : (t : EReal) * g x1 + ((‖x1 - z‖ ^ 2 / 2 : ℝ) : EReal) ≠ ⊤ := by
      rw [← EReal.coe_toReal hx1 (hg.1 x1), ← EReal.coe_mul, ← EReal.coe_add]
      exact EReal.coe_ne_top _
    exact this (top_le_iff.mp h)
  refine ⟨hgp, fun u => ?_⟩
  refine vi_line (fun u => ‖u - z‖ ^ 2 / (2 * t)) g hg p (t⁻¹ • (p - z))
    (fun d => line_deriv_sq z p d t ht.ne') hgp (fun u => ?_) u
  have hpu := hp u
  beta_reduce at hpu
  have h := ereal_div_t t ht (g p) (g u) (hg.1 p) (hg.1 u) _ _ hpu
  simp only [div_div] at h
  exact h
end Prim

lemma prox_bound {n : ℕ} (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (x0 x p : E n) (t L : ℝ) (ht : 0 < t) (hL : 0 ≤ L) (vF : E n → E n)
    (hLip : ∀ a b : E n, ‖vF a - vF b‖ ≤ L * ‖a - b‖)
    (h0 : ∀ u, g x0 + ((⟪-vF x0, u - x0⟫_ℝ : ℝ) : EReal) ≤ g u) (hgx0 : g x0 ≠ ⊤)
    (hgp : g p ≠ ⊤)
    (hvi : ∀ u, g p + ((⟪-(t⁻¹ • (p - (x - t • vF x))), u - p⟫_ℝ : ℝ) : EReal) ≤ g u) :
    ‖p - x0‖ ≤ (1 + t * L) * ‖x - x0‖ := by
  have ha : g x0 = ((g x0).toReal : EReal) := (EReal.coe_toReal hgx0 (hg.1 x0)).symm
  have hb : g p = ((g p).toReal : EReal) := (EReal.coe_toReal hgp (hg.1 p)).symm
  have h1 := h0 p
  have h2 := hvi x0
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
  set e := p - x0
  set q := (x - x0) - t • (vF x - vF x0)
  have hpz : p - (x - t • vF x) = (e - q) + t • vF x0 := by
    simp only [e, q, smul_sub]; abel
  have hx0p : x0 - p = -e := by simp only [e]; abel
  rw [hpz, hx0p] at h2
  have key : ⟪-vF x0, e⟫_ℝ + ⟪-(t⁻¹ • ((e - q) + t • vF x0)), -e⟫_ℝ =
      t⁻¹ * (‖e‖ ^ 2 - ⟪q, e⟫_ℝ) := by
    simp only [inner_neg_left, inner_neg_right, neg_neg, inner_smul_left, inner_add_left,
      inner_sub_left, real_inner_self_eq_norm_sq, RCLike.conj_to_real]
    field_simp
    ring
  have hsum : t⁻¹ * (‖e‖ ^ 2 - ⟪q, e⟫_ℝ) ≤ 0 := by rw [← key]; linarith
  have hsum' : ‖e‖ ^ 2 ≤ ⟪q, e⟫_ℝ := by
    by_contra hcon
    push_neg at hcon
    have : 0 < t⁻¹ * (‖e‖ ^ 2 - ⟪q, e⟫_ℝ) := mul_pos (inv_pos.mpr ht) (by linarith)
    linarith
  have hqe := real_inner_le_norm q e
  have hq : ‖q‖ ≤ (1 + t * L) * ‖x - x0‖ := by
    calc ‖q‖ ≤ ‖x - x0‖ + ‖t • (vF x - vF x0)‖ := norm_sub_le _ _
      _ = ‖x - x0‖ + t * ‖vF x - vF x0‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
      _ ≤ ‖x - x0‖ + t * (L * ‖x - x0‖) := by gcongr; exact hLip x x0
      _ = (1 + t * L) * ‖x - x0‖ := by ring
  have hen := norm_nonneg e
  have hqn := norm_nonneg q
  have : ‖e‖ ≤ ‖q‖ := by nlinarith
  linarith

section EB
variable {m n : ℕ}

lemma eb_of_qg (f : E m → ℝ) (hf : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ Set.univ f)
    (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g) (A : E n →L[ℝ] E m)
    (S : Set (E n)) (hS : S = {x | ∀ z, primalObj f g A x ≤ primalObj f g A z})
    (hSne : S.Nonempty) (hSbd : Bornology.IsBounded S)
    (φstar : ℝ) (hstar : ∀ x ∈ S, primalObj f g A x = (φstar : EReal))
    (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ x y : E n, ‖gradient (fun z => f (A z)) x - gradient (fun z => f (A z)) y‖ ≤
      L * ‖x - y‖)
    (hQG : ∀ K : Set (E n), IsCompact K → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K,
      ((φstar + c * Metric.infDist x S ^ 2 : ℝ) : EReal) ≤ primalObj f g A x)
    (t : ℝ) (ht : 0 < t) : ∃ γ ν : ℝ, 0 < γ ∧ 0 < ν ∧ ErrorBound f g A t S φstar γ ν := by
  set F : E n → ℝ := fun z => f (A z) with hF
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hFd : ∀ x, DifferentiableAt ℝ F x := fun x => (hfd (A x)).comp x A.differentiableAt
  have hFc : ConvexOn ℝ Set.univ F := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [F, smul_eq_mul]
    rw [map_add, map_smul, map_smul]
    exact hfconv.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hφ : ∀ x, primalObj f g A x = ((F x : ℝ) : EReal) + g x := fun x => rfl
  obtain ⟨x0, hx0S⟩ := hSne
  have hx0v : primalObj f g A x0 = φstar := hstar x0 hx0S
  have hx0min : ∀ z, primalObj f g A x0 ≤ primalObj f g A z := by
    have := hx0S; rw [hS] at this; exact this
  have hmin' : ∀ z, (φstar : EReal) ≤ primalObj f g A z := fun z => hx0v ▸ hx0min z
  have hgx0 : g x0 ≠ ⊤ := by
    intro h
    have := hx0v
    rw [hφ, h, EReal.coe_add_top] at this
    exact EReal.coe_ne_top _ this.symm
  have hSle : ∀ x, primalObj f g A x ≤ φstar → x ∈ S := by
    intro x hx; rw [hS]; intro z; exact hx.trans (hmin' z)
  obtain ⟨r, hr⟩ := hSbd.subset_closedBall x0
  set R := max r 0 + 1 with hRdef
  have hR : 0 < R := by positivity
  have hSR : ∀ x, primalObj f g A x ≤ φstar → ‖x - x0‖ < R := by
    intro x hx
    have h1 := hr (hSle x hx)
    rw [Metric.mem_closedBall, dist_eq_norm] at h1
    have : r ≤ max r 0 := le_max_left _ _
    linarith
  obtain ⟨δ, hδ, hgrow⟩ := level_growth (primalObj f g A) (phi_lsc f hfd.continuous g hgc A)
    (phi_cvx f hfconv g hg A) (phi_bot f g hg A) x0 φstar hx0v hmin' R hR hSR
  set M := max R (R / δ) with hMdef
  have hsub : ∀ x, primalObj f g A x ≤ ((φstar + 1 : ℝ) : EReal) → ‖x - x0‖ ≤ M := by
    intro x hx
    by_cases hxR : R ≤ ‖x - x0‖
    · have h1 := (hgrow x hxR).trans hx
      rw [EReal.coe_le_coe_iff] at h1
      have h2 : δ * (‖x - x0‖ / R) ≤ 1 := by linarith
      rw [mul_div_assoc', div_le_one hR] at h2
      have : ‖x - x0‖ ≤ R / δ := by rw [le_div_iff₀ hδ]; linarith
      exact le_max_of_le_right this
    · push_neg at hxR; exact le_max_of_le_left hxR.le
  set M2 := (1 + t * L) * M with hM2
  obtain ⟨c, hc, hqg⟩ := hQG (Metric.closedBall x0 M2) (isCompact_closedBall x0 M2)
  have hSc : IsCompact S := by
    have hcl : IsClosed S := by
      have : S = primalObj f g A ⁻¹' Set.Iic (φstar : EReal) := by
        ext x; constructor
        · intro hx; exact le_of_eq (hstar x hx)
        · intro hx; exact hSle x hx
      rw [this]; exact (phi_lsc f hfd.continuous g hgc A).isClosed_preimage _
    exact Metric.isCompact_of_isClosed_isBounded hcl hSbd
  refine ⟨t + (1 + t * L) / c, 1, by positivity, one_pos, ⟨x0, hx0S⟩, ?_⟩
  intro x hx p hp
  obtain ⟨hgp, hvi⟩ := prox_vi f g hg A t ht x p hp
  have hxM := hsub x hx
  have h0vi : ∀ u, g x0 + ((⟪-gradient F x0, u - x0⟫_ℝ : ℝ) : EReal) ≤ g u :=
    vi_line F g hg x0 (gradient F x0) (line_deriv F x0 (hFd x0)) hgx0 (fun u => by
      have := hx0min u
      rw [hφ, hφ] at this
      rwa [add_comm, add_comm (((F u : ℝ) : EReal))] at this)
  have hpb := prox_bound g hg x0 x p t L ht hL (gradient F) hLip h0vi hgx0 hgp hvi
  have hpK : p ∈ Metric.closedBall x0 M2 := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hpb.trans (mul_le_mul_of_nonneg_left hxM (by positivity))
  have hqp := hqg p hpK
  obtain ⟨s, hsS, hsd⟩ := hSc.exists_infDist_eq_dist ⟨x0, hx0S⟩ p
  have hsv := hstar s hsS
  have hgs : g s ≠ ⊤ := by
    intro h
    rw [hφ, h, EReal.coe_add_top] at hsv
    exact EReal.coe_ne_top _ hsv.symm
  have hgpe : g p = ((g p).toReal : EReal) := (EReal.coe_toReal hgp (hg.1 p)).symm
  have hgse : g s = ((g s).toReal : EReal) := (EReal.coe_toReal hgs (hg.1 s)).symm
  have hv1 := hvi s
  rw [hgpe, hgse, ← EReal.coe_add, EReal.coe_le_coe_iff] at hv1
  have hv2 := grad_ineq F hFc p (gradient F p) (line_deriv F p (hFd p)) s
  rw [hφ, hgse, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hsv
  rw [hφ, hgpe, ← EReal.coe_add, EReal.coe_le_coe_iff] at hqp
  set d := Metric.infDist p S with hd
  set G := t⁻¹ • (x - p) with hG
  set w := gradient F p - t⁻¹ • (p - (x - t • gradient F x)) with hw
  have hwG : w = G + (gradient F p - gradient F x) := by
    simp only [hw, hG, smul_sub, smul_smul, inv_mul_cancel₀ ht.ne', one_smul]; abel
  have hdps : d = ‖p - s‖ := hsd.trans (dist_eq_norm _ _)
  have hinner : -(‖w‖ * d) ≤ ⟪w, s - p⟫_ℝ := by
    have := abs_real_inner_le_norm w (s - p)
    rw [hdps, ← norm_neg (p - s), neg_sub]
    have := neg_abs_le ⟪w, s - p⟫_ℝ
    linarith
  have hwd : ⟪w, s - p⟫_ℝ = ⟪gradient F p, s - p⟫_ℝ +
      ⟪-(t⁻¹ • (p - (x - t • gradient F x))), s - p⟫_ℝ := by
    rw [hw, sub_eq_add_neg, inner_add_left]
  have hcd : c * d ^ 2 ≤ ‖w‖ * d := by nlinarith
  have hd0 : 0 ≤ d := Metric.infDist_nonneg
  have hcd' : c * d ≤ ‖w‖ := by
    rcases eq_or_lt_of_le hd0 with h0 | hpos
    · rw [← h0, mul_zero]; exact norm_nonneg _
    · nlinarith
  have hGn : ‖x - p‖ = t * ‖G‖ := by
    rw [hG, norm_smul, norm_inv, Real.norm_of_nonneg ht.le, ← mul_assoc, mul_inv_cancel₀ ht.ne',
      one_mul]
  have hwn : ‖w‖ ≤ (1 + t * L) * ‖G‖ := by
    calc ‖w‖ ≤ ‖G‖ + ‖gradient F p - gradient F x‖ := by rw [hwG]; exact norm_add_le _ _
      _ ≤ ‖G‖ + L * ‖p - x‖ := by gcongr; exact hLip p x
      _ = (1 + t * L) * ‖G‖ := by rw [norm_sub_rev, hGn]; ring
  have htri : Metric.infDist x S ≤ d + dist x p := Metric.infDist_le_infDist_add_dist
  rw [dist_eq_norm, hGn] at htri
  have hdw : d ≤ (1 + t * L) * ‖G‖ / c := by
    rw [le_div_iff₀ hc]; linarith
  calc Metric.infDist x S ≤ (1 + t * L) * ‖G‖ / c + t * ‖G‖ := by linarith
    _ = (t + (1 + t * L) / c) * ‖G‖ := by field_simp; ring
end EB

section Conj
variable {m n : ℕ}

/-- Q2: conjugate of a differentiable convex f at a gradient. -/
lemma conj_f_grad (f : E m → ℝ) (hfconv : ConvexOn ℝ Set.univ f) (z : E m)
    (hfd : DifferentiableAt ℝ f z) :
    conj (fun u => (f u : EReal)) (gradient f z) = ((⟪gradient f z, z⟫_ℝ - f z : ℝ) : EReal) := by
  unfold conj
  apply le_antisymm
  · apply iSup_le
    intro x
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h := grad_ineq f hfconv z (gradient f z) (line_deriv f z hfd) x
    rw [inner_sub_right] at h
    linarith
  · refine le_iSup_of_le z ?_
    rw [← EReal.coe_sub]

/-- Q3: conjugate of g at a subgradient. -/
lemma conj_g_subgrad (g : E n → EReal) (x v : E n) (hgx : g x ≠ ⊤) (hgb : g x ≠ ⊥)
    (hv : ∀ u, g x + ((⟪v, u - x⟫_ℝ : ℝ) : EReal) ≤ g u) :
    conj g v = ((⟪v, x⟫_ℝ - (g x).toReal : ℝ) : EReal) := by
  have ha : g x = ((g x).toReal : EReal) := (EReal.coe_toReal hgx hgb).symm
  unfold conj
  apply le_antisymm
  · apply iSup_le
    intro u
    by_cases hu : g u = ⊤
    · rw [hu, EReal.sub_top]; exact bot_le
    have hb : g u = ((g u).toReal : EReal) := (EReal.coe_toReal hu (ne_bot_of_le_ne_bot
      (by rw [ha, ← EReal.coe_add]; exact EReal.coe_ne_bot _) (hv u))).symm
    have h := hv u
    rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_sub_right] at h
    rw [hb, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith
  · refine le_iSup_of_le x ?_
    rw [ha, ← EReal.coe_sub, EReal.toReal_coe]
end Conj

section LinReg
lemma ri_ball {m : ℕ} (P : Set (E m)) (h0 : (0 : E m) ∈ intrinsicInterior ℝ P) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ v ∈ (affineSpan ℝ P).direction, ‖v‖ < ε → v ∈ P := by
  have h0P : (0 : E m) ∈ affineSpan ℝ P := mem_affineSpan ℝ (intrinsicInterior_subset h0)
  rw [mem_intrinsicInterior] at h0
  obtain ⟨y, hy, hy0⟩ := h0
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
  obtain ⟨ε, hε, hball⟩ := hy
  refine ⟨ε, hε, fun v hv hvε => ?_⟩
  have hvA : v ∈ affineSpan ℝ P := by
    have := AffineSubspace.vadd_mem_of_mem_direction hv h0P
    simpa using this
  have hmem : (⟨v, hvA⟩ : affineSpan ℝ P) ∈ Metric.ball y ε := by
    rw [Metric.mem_ball, Subtype.dist_eq]
    show dist v (y : E m) < ε
    rw [hy0, dist_zero_right]; exact hvε
  exact hball hmem

lemma cm_mem {V : Type*} [AddCommGroup V] [Module ℝ V] (C : Set V) (hC : Convex ℝ C)
    {ι : Type*} [Fintype ι] (t : ι → ℝ) (ht : ∀ i, 0 ≤ t i) (p : ι → V) (hp : ∀ i, p i ∈ C)
    (a : V) (ha : a ∈ C) : (1 + ∑ i, t i)⁻¹ • (a + ∑ i, t i • p i) ∈ C := by
  have hs : 0 < 1 + ∑ i, t i := by
    have : 0 ≤ ∑ i, t i := Finset.sum_nonneg (fun i _ => ht i)
    linarith
  have := hC.centerMass_mem (t := Finset.univ) (w := fun o : Option ι => o.elim 1 t)
    (z := fun o => o.elim a p) (by intro o _; cases o <;> simp [ht])
    (by simpa [Fintype.sum_option] using hs) (by intro o _; cases o <;> simp [ha, hp])
  simpa [Finset.centerMass, Fintype.sum_option] using this

/-- Q7: bounded linear regularity from 0 ∈ ri (Cf - A Cg). -/
lemma lin_reg {m n : ℕ} (A : E n →L[ℝ] E m) (Cf : Set (E m)) (Cg : Set (E n))
    (hCf : Convex ℝ Cf) (hCg : Convex ℝ Cg)
    (h0 : (0 : E m) ∈ intrinsicInterior ℝ {u | ∃ c ∈ Cf, ∃ a ∈ Cg, u = c - A a}) (B : ℝ) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ c ∈ Cf, ∀ a ∈ Cg, ‖a‖ ≤ B →
      ∃ z ∈ Cg, A z ∈ Cf ∧ ‖z - a‖ ≤ κ * ‖c - A a‖ := by
  set P : Set (E m) := {u | ∃ c ∈ Cf, ∃ a ∈ Cg, u = c - A a} with hP
  have h0P : (0 : E m) ∈ affineSpan ℝ P := mem_affineSpan ℝ (intrinsicInterior_subset h0)
  obtain ⟨ε, hε, hball⟩ := ri_ball P h0
  set V := (affineSpan ℝ P).direction with hV
  have hPV : ∀ u ∈ P, u ∈ V := fun u hu => by
    have := AffineSubspace.vsub_mem_direction (mem_affineSpan ℝ hu) h0P
    simpa using this
  set b := stdOrthonormalBasis ℝ V with hb
  set δ := ε / 2 with hδdef
  have hδ : 0 < δ := by positivity
  have hbn : ∀ i, ‖((b i : V) : E m)‖ = 1 := fun i => by
    exact b.orthonormal.1 i
  have hrep : ∀ (i : Fin (Module.finrank ℝ V)) (s : Bool), ∃ ca : E m × E n,
      ca.1 ∈ Cf ∧ ca.2 ∈ Cg ∧ (if s then δ else -δ) • ((b i : V) : E m) = ca.1 - A ca.2 := by
    intro i s
    have hv : (if s then δ else -δ) • ((b i : V) : E m) ∈ V := V.smul_mem _ (b i).2
    have hn : ‖(if s then δ else -δ) • ((b i : V) : E m)‖ < ε := by
      rw [norm_smul, hbn, mul_one]
      cases s
      · simp only [Bool.false_eq_true, if_false, norm_neg, Real.norm_of_nonneg hδ.le]
        rw [hδdef]; linarith
      · simp only [if_true, Real.norm_of_nonneg hδ.le]
        rw [hδdef]; linarith
    obtain ⟨c, hc, a, ha, he⟩ := hball _ hv hn
    exact ⟨(c, a), hc, ha, he⟩
  choose R hRf hRg hRe using hrep
  set Rb : ℝ := ∑ i, (‖(R i true).2‖ + ‖(R i false).2‖) with hRb
  have hRb0 : ∀ i s, ‖(R i s).2‖ ≤ Rb := by
    intro i s
    have h1 : ‖(R i s).2‖ ≤ ‖(R i true).2‖ + ‖(R i false).2‖ := by
      cases s
      · have := norm_nonneg (R i true).2; linarith
      · have := norm_nonneg (R i false).2; linarith
    exact h1.trans (Finset.single_le_sum (f := fun i => ‖(R i true).2‖ + ‖(R i false).2‖)
      (fun j _ => by positivity) (Finset.mem_univ i))
  have hRbnn : 0 ≤ Rb := Finset.sum_nonneg (fun i _ => by positivity)
  set k : ℝ := (Fintype.card (Fin (Module.finrank ℝ V)) : ℝ) with hk
  have hk0 : 0 ≤ k := by positivity
  refine ⟨k * (Rb + |B|) / δ, by positivity, fun c hc a ha haB => ?_⟩
  set u := c - A a with hu
  have huV : -u ∈ V := V.neg_mem (hPV u ⟨c, hc, a, ha, rfl⟩)
  set σ : Fin (Module.finrank ℝ V) → ℝ := fun i => ⟪((b i : V) : E m), -u⟫_ℝ with hσ
  have hexp : ∑ i, σ i • ((b i : V) : E m) = -u := by
    have h := b.sum_repr' ⟨-u, huV⟩
    have h2 := congrArg Subtype.val h
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h2
    exact h2
  set s : Fin (Module.finrank ℝ V) → Bool := fun i => decide (0 ≤ σ i) with hs
  set t : Fin (Module.finrank ℝ V) → ℝ := fun i => |σ i| / δ with ht
  have ht0 : ∀ i, 0 ≤ t i := fun i => by positivity
  have hts : ∀ i, t i • ((R i (s i)).1 - A (R i (s i)).2) = σ i • ((b i : V) : E m) := by
    intro i
    rw [← hRe, smul_smul]
    congr 1
    by_cases h : 0 ≤ σ i
    · simp only [ht, hs, h, decide_true, if_true, abs_of_nonneg h]
      field_simp
    · have h' : σ i < 0 := not_le.mp h
      simp only [ht, hs, h, decide_false, Bool.false_eq_true, if_false, abs_of_neg h']
      field_simp
  have htb : ∀ i, t i ≤ ‖u‖ / δ := by
    intro i
    have h1 : |σ i| ≤ ‖u‖ := by
      have := abs_real_inner_le_norm ((b i : V) : E m) (-u)
      rwa [hbn, one_mul, norm_neg] at this
    exact div_le_div_of_nonneg_right h1 hδ.le
  set T := ∑ i, t i with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ => ht0 i)
  have hTb : T ≤ k * (‖u‖ / δ) := by
    have := Finset.sum_le_card_nsmul Finset.univ t (‖u‖ / δ) (fun i _ => htb i)
    rw [Finset.card_univ, nsmul_eq_mul] at this
    exact this
  set W := 1 + T with hW
  have hWpos : 0 < W := by linarith
  set z := W⁻¹ • (a + ∑ i, t i • (R i (s i)).2) with hz
  have hkey : A a + ∑ i, t i • A (R i (s i)).2 = c + ∑ i, t i • (R i (s i)).1 := by
    have h1 : ∑ i, t i • ((R i (s i)).1 - A (R i (s i)).2) = -u := by
      rw [← hexp]; exact Finset.sum_congr rfl (fun i _ => hts i)
    simp only [smul_sub, Finset.sum_sub_distrib] at h1
    rw [hu] at h1
    rw [← sub_eq_zero, ← neg_eq_zero]
    rw [← sub_eq_zero] at h1
    rw [← h1]
    abel
  refine ⟨z, cm_mem Cg hCg t ht0 (fun i => (R i (s i)).2) (fun i => hRg i (s i)) a ha, ?_, ?_⟩
  · have : A z = W⁻¹ • (c + ∑ i, t i • (R i (s i)).1) := by
      rw [hz, map_smul, map_add, map_sum, ← hkey]
      simp only [map_smul]
    rw [this]
    exact cm_mem Cf hCf t ht0 (fun i => (R i (s i)).1) (fun i => hRf i (s i)) c hc
  · have hza : z - a = W⁻¹ • ∑ i, t i • ((R i (s i)).2 - a) := by
      have hWa : W⁻¹ • (W • a) = a := inv_smul_smul₀ hWpos.ne' a
      calc z - a = W⁻¹ • (a + ∑ i, t i • (R i (s i)).2) - W⁻¹ • (W • a) := by rw [hWa]
        _ = W⁻¹ • ((a + ∑ i, t i • (R i (s i)).2) - W • a) := by rw [smul_sub]
        _ = W⁻¹ • ∑ i, t i • ((R i (s i)).2 - a) := by
          congr 1
          simp only [hW, hT, add_smul, one_smul, Finset.sum_smul, smul_sub,
            Finset.sum_sub_distrib]
          abel
    have hnorm : ‖z - a‖ ≤ T * (Rb + |B|) := by
      rw [hza, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hWpos.le)]
      have h1 : ‖∑ i, t i • ((R i (s i)).2 - a)‖ ≤ ∑ i, t i * (Rb + |B|) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
        rw [norm_smul, Real.norm_of_nonneg (ht0 i)]
        gcongr
        calc ‖(R i (s i)).2 - a‖ ≤ ‖(R i (s i)).2‖ + ‖a‖ := norm_sub_le _ _
          _ ≤ Rb + |B| := add_le_add (hRb0 i (s i)) (haB.trans (le_abs_self B))
      rw [← Finset.sum_mul] at h1
      have hWinv : W⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have hRB : 0 ≤ Rb + |B| := by positivity
      calc W⁻¹ * ‖∑ i, t i • ((R i (s i)).2 - a)‖ ≤ 1 * (T * (Rb + |B|)) := by
            gcongr
        _ = T * (Rb + |B|) := one_mul _
    calc ‖z - a‖ ≤ T * (Rb + |B|) := hnorm
      _ ≤ k * (‖u‖ / δ) * (Rb + |B|) := by gcongr
      _ = k * (Rb + |B|) / δ * ‖c - A a‖ := by rw [hu]; ring

end LinReg

section Dual
variable {m n : ℕ}

lemma pc_coe {k : ℕ} (f : E k → ℝ) (hfconv : ConvexOn ℝ Set.univ f) :
    RockafellarMaxMono.Shared.ProperConvex (fun z => (f z : EReal)) := by
  refine ⟨fun x => EReal.coe_ne_bot _, ⟨0, EReal.coe_ne_top _⟩, fun x y t ht0 ht1 => ?_⟩
  have h := hfconv.2 (Set.mem_univ x) (Set.mem_univ y) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
    (by ring)
  rw [smul_eq_mul, smul_eq_mul] at h
  beta_reduce
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
  exact h

lemma firm_data {k : ℕ} (h : E k → EReal) (v : E k) (hb : ∀ x, h x ≠ ⊥)
    (hF : FirmlyConvexRel h v) :
    ∃ μ : ℝ, (∀ x, ((μ + ⟪v, x⟫_ℝ : ℝ) : EReal) ≤ h x) ∧
      (∃ x0, h x0 ≤ ((μ + ⟪v, x0⟫_ℝ : ℝ) : EReal)) ∧
      (∀ X : Set (E k), IsCompact X → ∃ α : ℝ, 0 < α ∧ ∀ x ∈ X,
        ((μ + ⟪v, x⟫_ℝ + α / 2 *
          Metric.infDist x {x | h x ≤ ((μ + ⟪v, x⟫_ℝ : ℝ) : EReal)} ^ 2 : ℝ) : EReal) ≤ h x) := by
  dsimp only [FirmlyConvexRel] at hF
  obtain ⟨⟨t0, ht0⟩, hX⟩ := hF
  have key : ∀ (x : E k) (r : ℝ), ((r : EReal) ≤ h x - ((⟪v, x⟫_ℝ : ℝ) : EReal) ↔
      ((r + ⟪v, x⟫_ℝ : ℝ) : EReal) ≤ h x) := by
    intro x r
    rw [EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
      EReal.coe_add]
  have key2 : ∀ (x : E k) (r : ℝ), (h x - ((⟪v, x⟫_ℝ : ℝ) : EReal) ≤ (r : EReal) ↔
      h x ≤ ((r + ⟪v, x⟫_ℝ : ℝ) : EReal)) := by
    intro x r
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)),
      EReal.coe_add]
  have ht0' := ht0
  simp only [ProxAlg.FixedPoint.subdifferential, Set.mem_setOf_eq, inner_zero_left,
    EReal.coe_zero, add_zero] at ht0'
  obtain ⟨hlt, hmin⟩ := ht0'
  have hne : h t0 - ((⟪v, t0⟫_ℝ : ℝ) : EReal) ≠ ⊥ := by
    have hb0 := hb t0
    generalize h t0 = e at hb0 ⊢
    induction e using EReal.rec with
    | bot => exact absurd rfl hb0
    | top => simp
    | coe r => rw [← EReal.coe_sub]; exact EReal.coe_ne_bot _
  set μ := (h t0 - ((⟪v, t0⟫_ℝ : ℝ) : EReal)).toReal with hμ
  have hμe : h t0 - ((⟪v, t0⟫_ℝ : ℝ) : EReal) = (μ : EReal) :=
    (EReal.coe_toReal hlt.ne hne).symm
  have hlow : ∀ x, ((μ + ⟪v, x⟫_ℝ : ℝ) : EReal) ≤ h x := fun x => (key x μ).mp (hμe ▸ hmin x)
  have hT : {x | (0 : E k) ∈ ProxAlg.FixedPoint.subdifferential
      (fun x => h x - ((⟪v, x⟫_ℝ : ℝ) : EReal)) x} =
      {x | h x ≤ ((μ + ⟪v, x⟫_ℝ : ℝ) : EReal)} := by
    ext x
    simp only [ProxAlg.FixedPoint.subdifferential, Set.mem_setOf_eq, inner_zero_left,
      EReal.coe_zero, add_zero]
    constructor
    · rintro ⟨_, hx⟩
      exact (key2 x μ).mp (hμe ▸ hx t0)
    · intro hx
      have hx' := (key2 x μ).mpr hx
      exact ⟨lt_of_le_of_lt hx' (EReal.coe_lt_top μ), fun z => hx'.trans ((key z μ).mpr (hlow z))⟩
  have hinf : (⨅ y, h y - ((⟪v, y⟫_ℝ : ℝ) : EReal)) = (μ : EReal) := by
    apply le_antisymm
    · exact (iInf_le _ t0).trans hμe.le
    · exact le_iInf (fun y => (key y μ).mpr (hlow y))
  refine ⟨μ, hlow, ⟨t0, (key2 t0 μ).mp hμe.le⟩, fun X hXc => ?_⟩
  obtain ⟨α, hα, hαX⟩ := hX X hXc
  refine ⟨α, hα, fun x hx => ?_⟩
  have h1 := hαX x hx
  rw [hinf, hT, ← EReal.coe_add] at h1
  have h2 := (key x _).mp h1
  have e : μ + α / 2 * Metric.infDist x {x | h x ≤ ((μ + ⟪v, x⟫_ℝ : ℝ) : EReal)} ^ 2 + ⟪v, x⟫_ℝ
      = μ + ⟪v, x⟫_ℝ + α / 2 * Metric.infDist x {x | h x ≤ ((μ + ⟪v, x⟫_ℝ : ℝ) : EReal)} ^ 2 := by
    ring
  rw [e] at h2
  exact h2

lemma conj_eq {k : ℕ} (h : E k → EReal) (v : E k) (μ : ℝ)
    (hlow : ∀ x, ((μ + ⟪v, x⟫_ℝ : ℝ) : EReal) ≤ h x) (x0 : E k)
    (hx0 : h x0 ≤ ((μ + ⟪v, x0⟫_ℝ : ℝ) : EReal)) : conj h v = ((-μ : ℝ) : EReal) := by
  unfold conj
  apply le_antisymm
  · refine iSup_le (fun x => ?_)
    rw [EReal.sub_le_iff_le_add (Or.inr (EReal.coe_ne_top _)) (Or.inr (EReal.coe_ne_bot _))]
    calc ((⟪v, x⟫_ℝ : ℝ) : EReal) = ((-μ : ℝ) : EReal) + ((μ + ⟪v, x⟫_ℝ : ℝ) : EReal) := by
          rw [← EReal.coe_add]; congr 1; ring
      _ ≤ ((-μ : ℝ) : EReal) + h x := add_le_add le_rfl (hlow x)
  · refine le_iSup_of_le x0 ?_
    have he : h x0 = ((μ + ⟪v, x0⟫_ℝ : ℝ) : EReal) := le_antisymm hx0 (hlow x0)
    rw [he, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    linarith

lemma dual_at_min (f : E m → ℝ) (hfd : Differentiable ℝ f) (hfconv : ConvexOn ℝ Set.univ f)
    (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g) (A : E n →L[ℝ] E m)
    (w : E m) (x : E n) (hgx : g x ≠ ⊤)
    (hmin : ∀ u, ((f (A x + w) : ℝ) : EReal) + g x ≤ ((f (A u + w) : ℝ) : EReal) + g u) :
    dualObj f g A (gradient f (A x + w)) =
      ((⟪gradient f (A x + w), w⟫_ℝ - f (A x + w) - (g x).toReal : ℝ) : EReal) := by
  set y := gradient f (A x + w) with hy
  have hH : ∀ d, HasDerivAt (fun s : ℝ => f (A (x + s • d) + w))
      ⟪ContinuousLinearMap.adjoint A y, d⟫_ℝ 0 := by
    intro d
    have h := line_deriv f (A x + w) (hfd _) (A d)
    rw [ContinuousLinearMap.adjoint_inner_left]
    have e : (fun s : ℝ => f (A (x + s • d) + w)) = fun s : ℝ => f (A x + w + s • A d) := by
      funext s; rw [map_add, map_smul]; congr 1; abel
    rw [e]; exact h
  have vi := vi_line (fun u => f (A u + w)) g hg x (ContinuousLinearMap.adjoint A y) hH hgx
    (fun u => by rw [add_comm (g x), add_comm (g u)]; exact hmin u)
  unfold dualObj
  rw [conj_f_grad f hfconv (A x + w) (hfd _), conj_g_subgrad g x _ hgx (hg.1 x) vi,
    ← EReal.coe_add, EReal.coe_eq_coe_iff]
  rw [inner_add_right, inner_neg_left, ContinuousLinearMap.adjoint_inner_left]
  ring

lemma perturbed_min (f : E m → ℝ) (hfd : Differentiable ℝ f) (hfconv : ConvexOn ℝ Set.univ f)
    (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g) (A : E n →L[ℝ] E m)
    (S : Set (E n)) (hS : S = {x | ∀ z, primalObj f g A x ≤ primalObj f g A z})
    (hSne : S.Nonempty) (hSbd : Bornology.IsBounded S)
    (φstar : ℝ) (hstar : ∀ x ∈ S, primalObj f g A x = (φstar : EReal)) (w : E m) :
    ∃ x, g x ≠ ⊤ ∧
      ∀ u, ((f (A x + w) : ℝ) : EReal) + g x ≤ ((f (A u + w) : ℝ) : EReal) + g u := by
  have hφ : ∀ x, primalObj f g A x = ((f (A x) : ℝ) : EReal) + g x := fun x => rfl
  obtain ⟨x0, hx0S⟩ := hSne
  have hx0v : primalObj f g A x0 = φstar := hstar x0 hx0S
  have hx0min : ∀ z, primalObj f g A x0 ≤ primalObj f g A z := by
    have := hx0S; rw [hS] at this; exact this
  have hmin' : ∀ z, (φstar : EReal) ≤ primalObj f g A z := fun z => hx0v ▸ hx0min z
  have hgx0 : g x0 ≠ ⊤ := by
    intro h
    have := hx0v
    rw [hφ, h, EReal.coe_add_top] at this
    exact EReal.coe_ne_top _ this.symm
  have hSle : ∀ x, primalObj f g A x ≤ φstar → x ∈ S := by
    intro x hx; rw [hS]; intro z; exact hx.trans (hmin' z)
  obtain ⟨r, hr⟩ := hSbd.subset_closedBall x0
  set R := max r 0 + 1 with hRdef
  have hR : 0 < R := by positivity
  have hSR : ∀ x, primalObj f g A x ≤ φstar → ‖x - x0‖ < R := by
    intro x hx
    have h1 := hr (hSle x hx)
    rw [Metric.mem_closedBall, dist_eq_norm] at h1
    have : r ≤ max r 0 := le_max_left _ _
    linarith
  obtain ⟨δ, hδ, hgrow⟩ := level_growth (primalObj f g A) (phi_lsc f hfd.continuous g hgc A)
    (phi_cvx f hfconv g hg A) (phi_bot f g hg A) x0 φstar hx0v hmin' R hR hSR
  set g0 := (g x0).toReal with hg0
  have hg0e : g x0 = (g0 : EReal) := (EReal.coe_toReal hgx0 (hg.1 x0)).symm
  set D := f (A x0 + w) + g0 with hD
  set C := f (A x0 - w) + g0 with hC
  set R' := max (2 * R) (R * (D + C - 2 * φstar) / δ) with hR'
  have hR'0 : 0 ≤ R' := le_max_of_le_left (by linarith)
  set Fw : E n → EReal := fun u => g u + ((f (A u + w) : ℝ) : EReal) with hFw
  have hlsc : LowerSemicontinuous Fw :=
    lsc_aux g hgc (fun u => f (A u + w)) (hfd.continuous.comp (A.continuous.add continuous_const))
  have hout : ∀ y, R' < ‖y - x0‖ → Fw x0 ≤ Fw y := by
    intro y hy
    simp only [hFw]
    by_cases hyt : g y = ⊤
    · rw [hyt, EReal.top_add_coe]; exact le_top
    set gy := (g y).toReal with hgy
    have hgye : g y = (gy : EReal) := (EReal.coe_toReal hyt (hg.1 y)).symm
    rw [hg0e, hgye, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
    set mpt := (1 / 2 : ℝ) • x0 + (1 / 2 : ℝ) • y with hmpt
    have hm1 : ‖mpt - x0‖ = ‖y - x0‖ / 2 := by
      have : mpt - x0 = (1 / 2 : ℝ) • (y - x0) := by rw [hmpt]; module
      rw [this, norm_smul, Real.norm_of_nonneg (by norm_num)]; ring
    have hyR : 2 * R < ‖y - x0‖ := lt_of_le_of_lt (le_max_left _ _) hy
    have hg1 := hgrow mpt (by rw [hm1]; linarith)
    have hgm := gconv_real g hg.1 hg.2.2 x0 y g0 gy (1 / 2) (1 / 2) (by norm_num) (by norm_num)
      (by norm_num) hg0e.le hgye.le
    have hfm := hfconv.2 (Set.mem_univ (A x0 - w)) (Set.mem_univ (A y + w))
      (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
    have eA : (1 / 2 : ℝ) • (A x0 - w) + (1 / 2 : ℝ) • (A y + w) = A mpt := by
      rw [hmpt, map_add, map_smul, map_smul, smul_sub, smul_add]; abel
    rw [eA, smul_eq_mul, smul_eq_mul] at hfm
    rw [hφ] at hg1
    have hg1' : ((φstar + δ * (‖mpt - x0‖ / R) : ℝ) : EReal) ≤
        ((f (A mpt) + (1 / 2 * g0 + 1 / 2 * gy) : ℝ) : EReal) := by
      rw [EReal.coe_add (f (A mpt))]; exact hg1.trans (add_le_add le_rfl hgm)
    rw [EReal.coe_le_coe_iff, hm1] at hg1'
    have h3 : R * (D + C - 2 * φstar) / δ < ‖y - x0‖ := lt_of_le_of_lt (le_max_right _ _) hy
    rw [div_lt_iff₀ hδ] at h3
    have h4 : D + C - 2 * φstar ≤ 2 * (δ * (‖y - x0‖ / 2 / R)) := by
      have e : 2 * (δ * (‖y - x0‖ / 2 / R)) = ‖y - x0‖ * δ / R := by field_simp
      rw [e, le_div_iff₀ hR]; linarith
    simp only [hD, hC] at h4
    linarith
  obtain ⟨p, _, hp⟩ := exists_global_min Fw hlsc x0 R' hR'0 hout
  refine ⟨p, ?_, fun u => ?_⟩
  · intro hpt
    have := hp x0
    simp only [hFw, hpt, EReal.top_add_coe, top_le_iff] at this
    rw [hg0e, ← EReal.coe_add] at this
    exact EReal.coe_ne_top _ this
  · have := hp u
    simp only [hFw] at this
    rw [add_comm, add_comm (((f (A u + w)) : ℝ) : EReal)]
    exact this

set_option maxHeartbeats 1000000 in
/-- Q8: quadratic growth on every compact set (the heart of Theorem 4.2). -/
lemma qg_on_compact (f : E m → ℝ) (hf : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ Set.univ f)
    (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g) (A : E n →L[ℝ] E m)
    (S : Set (E n)) (hS : S = {x | ∀ z, primalObj f g A x ≤ primalObj f g A z})
    (hSne : S.Nonempty) (hSbd : Bornology.IsBounded S) (ybar : E m)
    (hybar : ∀ y, dualObj f g A ybar ≤ dualObj f g A y)
    (hsc : DualStrictComplementarity f g A ybar)
    (hffirm : FirmlyConvexRel (fun z => (f z : EReal)) ybar)
    (hgfirm : FirmlyConvexRel g (-(ContinuousLinearMap.adjoint A ybar)))
    (φstar : ℝ) (hstar : ∀ x ∈ S, primalObj f g A x = (φstar : EReal)) :
    ∀ K : Set (E n), IsCompact K → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K,
      ((φstar + c * Metric.infDist x S ^ 2 : ℝ) : EReal) ≤ primalObj f g A x := by
  intro K hK
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hφ : ∀ x, primalObj f g A x = ((f (A x) : ℝ) : EReal) + g x := fun x => rfl
  obtain ⟨μf, hflow, ⟨cf0, hcf0⟩, hfX⟩ := firm_data (fun z => (f z : EReal)) ybar
    (fun x => EReal.coe_ne_bot _) hffirm
  obtain ⟨μg, hglow, ⟨cg0, hcg0⟩, hgX⟩ :=
    firm_data g (-(ContinuousLinearMap.adjoint A ybar)) hg.1 hgfirm
  have hflow' : ∀ z, μf + ⟪ybar, z⟫_ℝ ≤ f z := fun z => EReal.coe_le_coe_iff.mp (hflow z)
  have hAw : ∀ x, ⟪-(ContinuousLinearMap.adjoint A ybar), x⟫_ℝ = -⟪ybar, A x⟫_ℝ := by
    intro x; rw [inner_neg_left, ContinuousLinearMap.adjoint_inner_left]
  have hcf : conj (fun z => (f z : EReal)) ybar = ((-μf : ℝ) : EReal) :=
    conj_eq _ ybar μf hflow cf0 hcf0
  have hcg : conj g (-(ContinuousLinearMap.adjoint A ybar)) = ((-μg : ℝ) : EReal) :=
    conj_eq g _ μg hglow cg0 hcg0
  have hψ : dualObj f g A ybar = ((-μf - μg : ℝ) : EReal) := by
    unfold dualObj; rw [hcf, hcg, ← EReal.coe_add, sub_eq_add_neg]
  obtain ⟨x0, hx0S⟩ := hSne
  have hx0min : ∀ z, primalObj f g A x0 ≤ primalObj f g A z := by
    have := hx0S; rw [hS] at this; exact this
  have hx0v : primalObj f g A x0 = φstar := hstar x0 hx0S
  have hgx0 : g x0 ≠ ⊤ := by
    intro h
    have := hx0v
    rw [hφ, h, EReal.coe_add_top] at this
    exact EReal.coe_ne_top _ this.symm
  have hd0 := dual_at_min f hfd hfconv g hg A 0 x0 hgx0 (fun u => by
    simpa only [add_zero, primalObj] using hx0min u)
  have hphi0 : φstar = f (A x0) + (g x0).toReal := by
    rw [hφ, ← EReal.coe_toReal hgx0 (hg.1 x0), ← EReal.coe_add, EReal.coe_eq_coe_iff] at hx0v
    exact hx0v.symm
  have hSD : φstar ≤ μf + μg := by
    have := hybar (gradient f (A x0 + 0))
    rw [hψ, hd0, EReal.coe_le_coe_iff] at this
    simp only [inner_zero_right, add_zero] at this
    linarith
  set Tf : Set (E m) := {x | ((f x : ℝ) : EReal) ≤ ((μf + ⟪ybar, x⟫_ℝ : ℝ) : EReal)} with hTf
  set Tg : Set (E n) := {x | g x ≤ ((μg + ⟪-(ContinuousLinearMap.adjoint A ybar), x⟫_ℝ : ℝ)
    : EReal)} with hTg
  have hTfc : Convex ℝ Tf := by
    intro x hx y hy a b ha hb hab
    simp only [hTf, Set.mem_setOf_eq, EReal.coe_le_coe_iff] at hx hy ⊢
    have h1 := hfconv.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    rw [smul_eq_mul, smul_eq_mul] at h1
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    have e : μf = a * μf + b * μf := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left hx ha, mul_le_mul_of_nonneg_left hy hb]
  have hTgc : Convex ℝ Tg := by
    intro x hx y hy a b ha hb hab
    simp only [hTg, Set.mem_setOf_eq] at hx hy ⊢
    refine (gconv_real g hg.1 hg.2.2 x y _ _ a b ha hb hab hx hy).trans (le_of_eq ?_)
    congr 1
    rw [inner_add_right, inner_smul_right, inner_smul_right]
    linear_combination μg * hab
  have hTfcl : IsClosed Tf :=
    isClosed_le (continuous_coe_real_ereal.comp hfd.continuous)
      (continuous_coe_real_ereal.comp (continuous_const.add (continuous_const.inner continuous_id)))
  have hTgcl : IsClosed Tg := by
    have hl := lsc_aux g hgc (fun x => -(μg + ⟪-(ContinuousLinearMap.adjoint A ybar), x⟫_ℝ))
      ((continuous_const.add (continuous_const.inner continuous_id)).neg)
    have e : Tg = (fun x => g x + ((-(μg + ⟪-(ContinuousLinearMap.adjoint A ybar), x⟫_ℝ) : ℝ)
        : EReal)) ⁻¹' Set.Iic 0 := by
      ext x
      simp only [hTg, Set.mem_preimage, Set.mem_Iic, Set.mem_setOf_eq]
      have hb := hg.1 x
      generalize g x = e at hb ⊢
      induction e using EReal.rec with
      | bot => exact absurd rfl hb
      | top =>
        rw [EReal.top_add_coe, top_le_iff, top_le_iff]
        exact ⟨fun h => absurd h (EReal.coe_ne_top _), fun h => absurd h (by simp)⟩
      | coe r =>
        rw [← EReal.coe_add, EReal.coe_le_coe_iff, ← EReal.coe_zero, EReal.coe_le_coe_iff]
        constructor <;> intro h <;> linarith
    rw [e]; exact hl.isClosed_preimage 0
  have hsub : ProxAlg.FixedPoint.subdifferential (dualObj f g A) ybar =
      {u | ∃ c ∈ Tf, ∃ a ∈ Tg, u = c - A a} := by
    ext w
    simp only [ProxAlg.FixedPoint.subdifferential, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, hw⟩
      obtain ⟨xw, hgxw, hxw⟩ :=
        perturbed_min f hfd hfconv g hg hgc A S hS ⟨x0, hx0S⟩ hSbd φstar hstar w
      have hdw := dual_at_min f hfd hfconv g hg A w xw hgxw hxw
      have h1 := hw (gradient f (A xw + w))
      rw [hψ, hdw, ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
      set y := gradient f (A xw + w) with hy
      set gx := (g xw).toReal with hgx
      have hgxe : g xw = (gx : EReal) := (EReal.coe_toReal hgxw (hg.1 xw)).symm
      have hfl := hflow' (A xw + w)
      have hgl : μg + ⟪-(ContinuousLinearMap.adjoint A ybar), xw⟫_ℝ ≤ gx := by
        have := hglow xw; rw [hgxe, EReal.coe_le_coe_iff] at this; exact this
      have e1 := hAw xw
      have e2 : ⟪ybar, A xw + w⟫_ℝ = ⟪ybar, A xw⟫_ℝ + ⟪ybar, w⟫_ℝ := inner_add_right _ _ _
      have e3 : ⟪w, y - ybar⟫_ℝ = ⟪y, w⟫_ℝ - ⟪ybar, w⟫_ℝ := by
        rw [inner_sub_right, real_inner_comm y w, real_inner_comm ybar w]
      refine ⟨A xw + w, ?_, xw, ?_, by abel⟩
      · show ((f (A xw + w) : ℝ) : EReal) ≤ ((μf + ⟪ybar, A xw + w⟫_ℝ : ℝ) : EReal)
        rw [EReal.coe_le_coe_iff]; linarith
      · show g xw ≤ ((μg + ⟪-(ContinuousLinearMap.adjoint A ybar), xw⟫_ℝ : ℝ) : EReal)
        rw [hgxe, EReal.coe_le_coe_iff]; linarith
    · rintro ⟨c, hc, a, ha, rfl⟩
      refine ⟨by rw [hψ]; exact EReal.coe_lt_top _, fun y => ?_⟩
      have hcr : f c ≤ μf + ⟪ybar, c⟫_ℝ := EReal.coe_le_coe_iff.mp hc
      have hgat : g a ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) ha
      set ga := (g a).toReal with hga
      have hgae : g a = (ga : EReal) := (EReal.coe_toReal hgat (hg.1 a)).symm
      have hgar : ga ≤ μg + ⟪-(ContinuousLinearMap.adjoint A ybar), a⟫_ℝ := by
        have := ha; simp only [hTg, Set.mem_setOf_eq] at this
        rw [hgae, EReal.coe_le_coe_iff] at this; exact this
      have hc1 : ((⟪y, c⟫_ℝ - f c : ℝ) : EReal) ≤ conj (fun z => (f z : EReal)) y := by
        unfold conj; refine le_iSup_of_le c ?_; rw [← EReal.coe_sub]
      have hc2 : ((⟪-(ContinuousLinearMap.adjoint A y), a⟫_ℝ - ga : ℝ) : EReal) ≤
          conj g (-(ContinuousLinearMap.adjoint A y)) := by
        unfold conj; refine le_iSup_of_le a ?_; rw [hgae, ← EReal.coe_sub]
      rw [hψ]
      unfold dualObj
      refine le_trans ?_ (add_le_add hc1 hc2)
      rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have e4 : ⟪-(ContinuousLinearMap.adjoint A y), a⟫_ℝ = -⟪y, A a⟫_ℝ := by
        rw [inner_neg_left, ContinuousLinearMap.adjoint_inner_left]
      have e5 := hAw a
      have e6 : ⟪c - A a, y - ybar⟫_ℝ =
          ⟪y, c⟫_ℝ - ⟪ybar, c⟫_ℝ - ⟪y, A a⟫_ℝ + ⟪ybar, A a⟫_ℝ := by
        rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_comm y c,
          real_inner_comm ybar c, real_inner_comm y (A a), real_inner_comm ybar (A a)]
        ring
      linarith
  unfold DualStrictComplementarity at hsc
  rw [hsub] at hsc
  obtain ⟨rK, hrK⟩ := hK.isBounded.subset_closedBall 0
  set B := 2 * rK + ‖cg0‖ with hB
  obtain ⟨κ, hκ, hlr⟩ := lin_reg A Tf Tg hTfc hTgc hsc B
  obtain ⟨α1, hα1, hf1⟩ := hfX (A '' K) (hK.image A.continuous)
  obtain ⟨α2, hα2, hg2⟩ := hgX K hK
  set α := min α1 α2 with hα
  have hα0 : 0 < α := lt_min hα1 hα2
  set M := 1 + κ + κ * ‖A‖ with hM
  have hM1 : 1 ≤ M := by have := norm_nonneg A; nlinarith
  have hMpos : 0 < M := by linarith
  refine ⟨α / (4 * M ^ 2), by positivity, fun x hxK => ?_⟩
  obtain ⟨c, hcT, hcd⟩ := hTfcl.exists_infDist_eq_dist ⟨cf0, hcf0⟩ (A x)
  obtain ⟨a, haT, had⟩ := hTgcl.exists_infDist_eq_dist ⟨cg0, hcg0⟩ x
  set d1 := Metric.infDist (A x) Tf with hd1
  set d2 := Metric.infDist x Tg with hd2
  have hF1 := hf1 (A x) ⟨x, hxK, rfl⟩
  have hG2 := hg2 x hxK
  have hxr : ‖x‖ ≤ rK := by
    have := hrK hxK; rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hd2le : d2 ≤ ‖x‖ + ‖cg0‖ := by
    have := Metric.infDist_le_dist_of_mem (x := x) (show cg0 ∈ Tg from hcg0)
    rw [dist_eq_norm] at this
    exact this.trans (norm_sub_le _ _)
  have haB : ‖a‖ ≤ B := by
    have h1 : ‖a‖ ≤ ‖x‖ + ‖x - a‖ := by
      have := norm_sub_le x (x - a); rwa [sub_sub_cancel] at this
    have h2 : ‖x - a‖ = d2 := by rw [had, dist_eq_norm]
    rw [hB]; linarith
  obtain ⟨z, hzT, hAzT, hzd⟩ := hlr c hcT a haT haB
  have hsplit : ∀ u, ((μf + ⟪ybar, A u⟫_ℝ : ℝ) : EReal) +
      ((μg + ⟪-(ContinuousLinearMap.adjoint A ybar), u⟫_ℝ : ℝ) : EReal) =
      ((μf + μg : ℝ) : EReal) := by
    intro u; rw [← EReal.coe_add, hAw u]; congr 1; ring
  have hzS : z ∈ S := by
    rw [hS]; intro z'
    calc primalObj f g A z ≤ ((μf + μg : ℝ) : EReal) := by
          rw [hφ, ← hsplit z]; exact add_le_add hAzT hzT
      _ ≤ primalObj f g A z' := by
          rw [hφ, ← hsplit z']; exact add_le_add (hflow (A z')) (hglow z')
  have hD : Metric.infDist x S ≤ M * (d1 + d2) := by
    have h1 := Metric.infDist_le_dist_of_mem (x := x) hzS
    rw [dist_eq_norm] at h1
    have h2 : ‖x - z‖ ≤ ‖x - a‖ + ‖z - a‖ := by
      have := norm_sub_le (x - a) (z - a)
      rwa [sub_sub_sub_cancel_right] at this
    have h3 : ‖c - A a‖ ≤ d1 + ‖A‖ * d2 := by
      have h4 : ‖c - A a‖ ≤ ‖c - A x‖ + ‖A x - A a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      have h5 : ‖c - A x‖ = d1 := by rw [hcd, dist_eq_norm, norm_sub_rev]
      have h6 : ‖A x - A a‖ ≤ ‖A‖ * d2 := by
        rw [← map_sub]
        calc ‖A (x - a)‖ ≤ ‖A‖ * ‖x - a‖ := A.le_opNorm _
          _ = ‖A‖ * d2 := by rw [had, dist_eq_norm]
      linarith
    have h7 : ‖x - a‖ = d2 := by rw [had, dist_eq_norm]
    have hd1n : 0 ≤ d1 := Metric.infDist_nonneg
    have hd2n : 0 ≤ d2 := Metric.infDist_nonneg
    have hAn := norm_nonneg A
    have h8 : κ * ‖c - A a‖ ≤ κ * (d1 + ‖A‖ * d2) := mul_le_mul_of_nonneg_left h3 hκ
    have h9 : Metric.infDist x S ≤ d2 + κ * (d1 + ‖A‖ * d2) := by linarith
    have h10 : 0 ≤ κ * ‖A‖ * d1 := by positivity
    have h11 : 0 ≤ κ * d2 := by positivity
    have e : M * (d1 + d2) = (d2 + κ * (d1 + ‖A‖ * d2)) + (d1 + κ * ‖A‖ * d1 + κ * d2) := by
      rw [hM]; ring
    linarith
  by_cases hgx : g x = ⊤
  · rw [hφ, hgx, EReal.coe_add_top]; exact le_top
  set gx := (g x).toReal with hgxr
  have hgxe : g x = (gx : EReal) := (EReal.coe_toReal hgx (hg.1 x)).symm
  have hF1' := EReal.coe_le_coe_iff.mp hF1
  rw [hgxe, EReal.coe_le_coe_iff, hAw] at hG2
  rw [hφ, hgxe, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hD0 : 0 ≤ Metric.infDist x S := Metric.infDist_nonneg
  have hd1n : 0 ≤ d1 := Metric.infDist_nonneg
  have hd2n : 0 ≤ d2 := Metric.infDist_nonneg
  have hsq : Metric.infDist x S ^ 2 ≤ 2 * M ^ 2 * (d1 ^ 2 + d2 ^ 2) := by
    have h1 : Metric.infDist x S ^ 2 ≤ (M * (d1 + d2)) ^ 2 := pow_le_pow_left₀ hD0 hD 2
    have e : 2 * M ^ 2 * (d1 ^ 2 + d2 ^ 2) - (M * (d1 + d2)) ^ 2 = M ^ 2 * (d1 - d2) ^ 2 := by
      ring
    have : 0 ≤ M ^ 2 * (d1 - d2) ^ 2 := by positivity
    linarith
  have hc : α / (4 * M ^ 2) * Metric.infDist x S ^ 2 ≤ α / 2 * (d1 ^ 2 + d2 ^ 2) := by
    calc α / (4 * M ^ 2) * Metric.infDist x S ^ 2
        ≤ α / (4 * M ^ 2) * (2 * M ^ 2 * (d1 ^ 2 + d2 ^ 2)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = α / 2 * (d1 ^ 2 + d2 ^ 2) := by field_simp; ring
  have hα1' : α ≤ α1 := min_le_left _ _
  have hα2' : α ≤ α2 := min_le_right _ _
  have h9a : α / 2 * d1 ^ 2 ≤ α1 / 2 * d1 ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have h9b : α / 2 * d2 ^ 2 ≤ α2 / 2 * d2 ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  have e' : α / 2 * (d1 ^ 2 + d2 ^ 2) = α / 2 * d1 ^ 2 + α / 2 * d2 ^ 2 := mul_add _ _ _
  linarith
end Dual

end PE093

open ErrBoundQG.Structured in
theorem solution {m n : ℕ}
    (f : E m → ℝ) (hf : ContDiff ℝ 1 f) (hfconv : ConvexOn ℝ Set.univ f)
    (g : E n → EReal) (hg : RockafellarMaxMono.Shared.ProperConvex g)
    (hgc : LowerSemicontinuous g) (A : E n →L[ℝ] E m)
    (S : Set (E n)) (hS : S = {x | ∀ z, primalObj f g A x ≤ primalObj f g A z})
    (hSne : S.Nonempty) (hSbd : Bornology.IsBounded S) (ybar : E m)
    (hybar : ∀ y, dualObj f g A ybar ≤ dualObj f g A y)
    (hnd : DualNondegenerate f g A)
    (hsc : DualStrictComplementarity f g A ybar)
    (hffirm : FirmlyConvexRel (fun z => (f z : EReal)) ybar)
    (hgfirm : FirmlyConvexRel g (-(ContinuousLinearMap.adjoint A ybar)))
    (φstar : ℝ) (hstar : ∀ x ∈ S, primalObj f g A x = (φstar : EReal))
    (β : ℝ) (hβ : 0 ≤ β)
    (hLip : ∀ y z : E m, ‖gradient f y - gradient f z‖ ≤ β * ‖y - z‖) :
    ∀ t : ℝ, 0 < t → ∃ γ ν : ℝ, 0 < γ ∧ 0 < ν ∧
      ErrorBound f g A t S φstar γ ν := by
  intro t ht
  have hfd : Differentiable ℝ f := hf.differentiable (by simp)
  have hgr : ∀ x, gradient (fun z => f (A z)) x =
      ContinuousLinearMap.adjoint A (gradient f (A x)) :=
    fun x => (PE093.grad_comp f A x (hfd (A x))).gradient
  refine PE093.eb_of_qg f hf hfconv g hg hgc A S hS hSne hSbd φstar hstar (‖A‖ * β * ‖A‖)
    (by positivity) (fun x y => ?_)
    (PE093.qg_on_compact f hf hfconv g hg hgc A S hS hSne hSbd ybar hybar hsc hffirm hgfirm
      φstar hstar) t ht
  rw [hgr, hgr, ← map_sub]
  calc ‖ContinuousLinearMap.adjoint A (gradient f (A x) - gradient f (A y))‖
      ≤ ‖ContinuousLinearMap.adjoint A‖ * ‖gradient f (A x) - gradient f (A y)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ‖A‖ * (β * ‖A x - A y‖) := by
        rw [LinearIsometryEquiv.norm_map]; gcongr; exact hLip _ _
    _ ≤ ‖A‖ * (β * (‖A‖ * ‖x - y‖)) := by
        rw [← map_sub]; gcongr; exact A.le_opNorm _
    _ = ‖A‖ * β * ‖A‖ * ‖x - y‖ := by ring
