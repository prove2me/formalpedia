-- Prove2me | solution 1 for ChanceStateCtrl.General.convex_optimality_eq_20
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-25T00:53:05.262688+00:00
-- url     : https://prove2.me/submissions/cc17cce8-b517-48ab-a8fc-18df2a2b5720

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

open ChanceStateCtrl.General

private lemma strict_comb {a b x y x' y' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (h1 : x < y) (h2 : x' < y') : a * x + b * x' < a * y + b * y' := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp at hab; subst hab; linarith
  · nlinarith [mul_pos h (sub_pos.2 h1), mul_nonneg hb (sub_pos.2 h2).le]

private lemma slope_tendsto {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : U → ℝ) (hF_diff : Differentiable ℝ F) (us v : U) :
    Tendsto (fun t : ℝ => t⁻¹ * (F (us + t • v) - F us)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ F us v)) := by
  have h1 : HasDerivAt (fun t : ℝ => us + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add us
  have h2 : HasDerivAt (fun t : ℝ => F (us + t • v)) (fderiv ℝ F us v) 0 := by
    have := (hF_diff (us + (0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
    simp only [zero_smul, add_zero] at this
    exact this
  have := h2.tendsto_slope_zero_right
  simpa [smul_eq_mul] using this

private lemma convex_grad {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : U → ℝ) (hF_convex : ConvexOn ℝ Set.univ F) (hF_diff : Differentiable ℝ F)
    (us u : U) : F us + fderiv ℝ F us (u - us) ≤ F u := by
  have hlim := slope_tendsto F hF_diff us (u - us)
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), t⁻¹ * (F (us + t • (u - us)) - F us) ≤ F u - F us := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
    have hpt : us + t • (u - us) = (1 - t) • us + t • u := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    have hc := hF_convex.2 (Set.mem_univ us) (Set.mem_univ u) (by linarith [ht.2] : (0:ℝ) ≤ 1 - t)
      ht.1.le (by ring)
    rw [← hpt, smul_eq_mul, smul_eq_mul] at hc
    rw [inv_mul_le_iff₀ ht.1]
    nlinarith
  have := le_of_tendsto hlim hev
  linarith

private lemma first_order {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (F : U → ℝ) (hF_diff : Differentiable ℝ F) (C : Set U) (hC : Convex ℝ C)
    (us : U) (hus : us ∈ C) (hmin : ∀ u ∈ C, F us ≤ F u) (u : U) (hu : u ∈ C) :
    0 ≤ fderiv ℝ F us (u - us) := by
  have hlim := slope_tendsto F hF_diff us (u - us)
  have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 ≤ t⁻¹ * (F (us + t • (u - us)) - F us) := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
    have hpt : us + t • (u - us) = (1 - t) • us + t • u := by
      simp only [sub_smul, one_smul, smul_sub]; abel
    have hmem : us + t • (u - us) ∈ C := by
      rw [hpt]; exact hC hus hu (by linarith [ht.2]) ht.1.le (by ring)
    exact mul_nonneg (inv_nonneg.2 ht.1.le) (sub_nonneg.2 (hmin _ hmem))
  exact ge_of_tendsto hlim hev

private lemma local_to_global {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (f : U → EReal) (hconv : ConvexEpi f) (hnebot : ∀ u, f u ≠ ⊥) (us : U) (r : ℝ) (hr : 0 < r)
    (h : U → ℝ) (hfh : ∀ u ∈ Metric.ball us r, f u = (h u : EReal)) (x : StrongDual ℝ U)
    (hx : ∀ w ∈ Metric.ball us r, h us + x (w - us) ≤ h w) : x ∈ convexSubdiffE f us := by
  intro w
  rw [hfh us (Metric.mem_ball_self hr), EReal.toReal_coe]
  rcases eq_or_ne (f w) ⊤ with hw | hw
  · rw [hw]; exact le_top
  set c := (f w).toReal with hcdef
  have hcw : f w = (c : EReal) := (EReal.coe_toReal hw (hnebot w)).symm
  rw [hcw]
  apply EReal.coe_le_coe_iff.2
  set d := ‖w - us‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  set t0 := r / (d + r) with ht0
  have ht0pos : 0 < t0 := div_pos hr (by linarith)
  have ht0le : t0 ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  have hsub : (1 - t0) • us + t0 • w - us = t0 • (w - us) := by
    simp only [sub_smul, one_smul, smul_sub]; abel
  have hzS : (1 - t0) • us + t0 • w ∈ Metric.ball us r := by
    rw [Metric.mem_ball, dist_eq_norm, hsub, norm_smul, Real.norm_of_nonneg ht0pos.le, ← hd, ht0]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  have hue : (us, h us) ∈ {q : U × ℝ | f q.1 ≤ (q.2 : EReal)} := by
    show f us ≤ ((h us : ℝ) : EReal)
    rw [hfh us (Metric.mem_ball_self hr)]
  have hwe : (w, c) ∈ {q : U × ℝ | f q.1 ≤ (q.2 : EReal)} := by
    show f w ≤ ((c : ℝ) : EReal)
    rw [hcw]
  have H := hconv hue hwe (by linarith : (0:ℝ) ≤ 1 - t0) ht0pos.le (by ring)
  simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd] at H
  rw [hfh _ hzS] at H
  have H1 : h ((1 - t0) • us + t0 • w) ≤ (1 - t0) * h us + t0 * c :=
    EReal.coe_le_coe_iff.1 H
  have H2 := hx _ hzS
  rw [hsub, map_smul, smul_eq_mul] at H2
  have H3 : t0 * (h us + x (w - us)) ≤ t0 * c := by nlinarith
  exact le_of_mul_le_mul_left H3 ht0pos

private lemma subdiff_nonempty {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    (f : U → EReal) (hconv : ConvexEpi f) (hnebot : ∀ u, f u ≠ ⊥) (us : U)
    (hf_cont : ∃ t ∈ 𝓝 us, (∀ u ∈ t, f u ≠ ⊤) ∧ ContinuousOn (fun u => (f u).toReal) t) :
    ∃ x, x ∈ convexSubdiffE f us := by
  obtain ⟨t, ht, htop, hcont⟩ := hf_cont
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 ht
  set B := Metric.ball us r with hB
  set h : U → ℝ := fun u => (f u).toReal with hhdef
  have hfh : ∀ u ∈ B, f u = (h u : EReal) := fun u hu =>
    (EReal.coe_toReal (htop u (hball hu)) (hnebot u)).symm
  set O := {q : U × ℝ | q.1 ∈ B ∧ h q.1 < q.2} with hO
  have hOopen : IsOpen O := by
    have hc : ContinuousOn (fun q : U × ℝ => q.2 - h q.1) (B ×ˢ Set.univ) := by
      apply ContinuousOn.sub continuous_snd.continuousOn
      exact (hcont.mono hball).comp continuous_fst.continuousOn (fun q hq => hq.1)
    have := hc.isOpen_inter_preimage (Metric.isOpen_ball.prod isOpen_univ) (isOpen_Ioi (a := (0:ℝ)))
    convert this using 1
    ext q; simp only [hO, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_prod, Set.mem_univ,
      and_true, Set.mem_preimage, Set.mem_Ioi, sub_pos]
  have hOconv : Convex ℝ O := by
    intro q hq q' hq' a b ha hb hab
    have hm : a • q.1 + b • q'.1 ∈ B := (convex_ball us r) hq.1 hq'.1 ha hb hab
    refine ⟨by simpa using hm, ?_⟩
    have e1 : (q.1, h q.1) ∈ {q : U × ℝ | f q.1 ≤ (q.2 : EReal)} := by
      show f q.1 ≤ ((h q.1 : ℝ) : EReal); rw [hfh _ hq.1]
    have e2 : (q'.1, h q'.1) ∈ {q : U × ℝ | f q.1 ≤ (q.2 : EReal)} := by
      show f q'.1 ≤ ((h q'.1 : ℝ) : EReal); rw [hfh _ hq'.1]
    have H := hconv e1 e2 ha hb hab
    simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
      Prod.smul_snd, smul_eq_mul] at H
    rw [hfh _ hm] at H
    have H1 := EReal.coe_le_coe_iff.1 H
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    exact lt_of_le_of_lt H1 (strict_comb ha hb hab hq.2 hq'.2)
  have hnot : (us, h us) ∉ O := fun hq => lt_irrefl _ hq.2
  obtain ⟨Λ, hΛ⟩ := geometric_hahn_banach_open_point hOconv hOopen hnot
  set φ : StrongDual ℝ U := Λ.comp (ContinuousLinearMap.inl ℝ U ℝ) with hφ
  set c := Λ (0, 1) with hc
  have hsplit : ∀ u s, Λ (u, s) = φ u + s * c := by
    intro u s
    have : (u, s) = (u, (0:ℝ)) + s • ((0:U), (1:ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]; rfl
  have husB : us ∈ B := Metric.mem_ball_self hr
  have hcneg : c < 0 := by
    have := hΛ (us, h us + 1) ⟨husB, by simp⟩
    rw [hsplit, hsplit] at this; linarith
  refine ⟨(-c⁻¹) • φ, local_to_global f hconv hnebot us r hr h hfh _ ?_⟩
  intro w hw
  have key : φ (w - us) + c * (h w - h us) ≤ 0 := by
    by_contra hD; push_neg at hD
    set D := φ (w - us) + c * (h w - h us)
    have := hΛ (w, h w + D / (-c)) ⟨hw, by simp; exact div_pos hD (by linarith)⟩
    rw [hsplit, hsplit] at this
    have hc0 : c ≠ 0 := hcneg.ne
    have hcc : D / (-c) * c = -D := by field_simp
    have e2 : (h w + D / -c) * c = h w * c - D := by rw [add_mul, hcc]; ring
    have hDexp : D = φ w - φ us + c * (h w - h us) := by simp only [D, map_sub]
    rw [e2] at this
    nlinarith
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  have : -c⁻¹ * φ (w - us) = (φ (w - us)) / (-c) := by field_simp
  rw [this]
  have h2 : φ (w - us) / (-c) ≤ h w - h us := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  linarith

theorem solution {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [CompleteSpace U] (F : U → ℝ) (hF_convex : ConvexOn ℝ Set.univ F)
    (hF_diff : Differentiable ℝ F) (f : U → EReal) (hf_convex : ConvexEpi f)
    (hf_ne_bot : ∀ u, f u ≠ ⊥) (hf_lsc : LowerSemicontinuous f)
    (hslater : ∃ uh : U, f uh < 0) (us : U) (hus : f us ≤ 0)
    (hf_cont : ∃ t ∈ 𝓝 us, (∀ u ∈ t, f u ≠ ⊤) ∧ ContinuousOn (fun u => (f u).toReal) t) :
    IsSolution {u | f u ≤ 0} F us ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ (∃ x ∈ convexSubdiffE f us, -(fderiv ℝ F us) = lam • x) ∧
        lam * (f us).toReal = 0 := by
  set ℓ := fderiv ℝ F us with hℓ
  have hfin : ∀ u, f u ≤ 0 → f u = ((f u).toReal : EReal) := fun u hu =>
    (EReal.coe_toReal (ne_top_of_le_ne_top EReal.zero_ne_top hu) (hf_ne_bot u)).symm
  set r0 := (f us).toReal with hr0
  have hfus : f us = (r0 : EReal) := hfin us hus
  have hr0le : r0 ≤ 0 := by
    have := hus; rw [hfus] at this; exact_mod_cast this
  constructor
  · rintro ⟨-, hmin⟩
    have hCconv : Convex ℝ {u | f u ≤ 0} := by
      intro u hu u' hu' a b ha hb hab
      have e1 : (u, (0:ℝ)) ∈ {q : U × ℝ | f q.1 ≤ (q.2 : EReal)} := by
        show f u ≤ ((0:ℝ) : EReal); simpa using hu
      have e2 : (u', (0:ℝ)) ∈ {q : U × ℝ | f q.1 ≤ (q.2 : EReal)} := by
        show f u' ≤ ((0:ℝ) : EReal); simpa using hu'
      have H := hf_convex e1 e2 ha hb hab
      simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
        Prod.smul_snd, smul_zero, add_zero] at H
      simpa using H
    have hFO : ∀ u, f u ≤ 0 → 0 ≤ ℓ (u - us) := fun u hu =>
      first_order F hF_diff _ hCconv us hus hmin u hu
    set G := {q : ℝ × ℝ | ∃ u, ℓ (u - us) < q.1 ∧ f u < (q.2 : EReal)} with hG
    have hGopen : IsOpen G := by
      have : G = ⋃ u : U, ({q : ℝ × ℝ | ℓ (u - us) < q.1} ∩ {q | f u < (q.2 : EReal)}) := by
        ext q; simp [hG]
      rw [this]
      refine isOpen_iUnion fun u => IsOpen.inter ?_ ?_
      · exact isOpen_lt continuous_const continuous_fst
      · exact isOpen_Ioi.preimage (continuous_coe_real_ereal.comp continuous_snd)
    have hGconv : Convex ℝ G := by
      rintro q ⟨u, hu1, hu2⟩ q' ⟨u', hu1', hu2'⟩ a b ha hb hab
      have hfu : f u = ((f u).toReal : EReal) :=
        (EReal.coe_toReal (ne_top_of_lt hu2) (hf_ne_bot u)).symm
      have hfu' : f u' = ((f u').toReal : EReal) :=
        (EReal.coe_toReal (ne_top_of_lt hu2') (hf_ne_bot u')).symm
      have e1 : (u, (f u).toReal) ∈ {q : U × ℝ | f q.1 ≤ (q.2 : EReal)} := by
        show f u ≤ (((f u).toReal : ℝ) : EReal); rw [← hfu]
      have e2 : (u', (f u').toReal) ∈ {q : U × ℝ | f q.1 ≤ (q.2 : EReal)} := by
        show f u' ≤ (((f u').toReal : ℝ) : EReal); rw [← hfu']
      have H := hf_convex e1 e2 ha hb hab
      simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
        Prod.smul_snd, smul_eq_mul] at H
      have l1 : (f u).toReal < q.2 := by rw [hfu] at hu2; exact_mod_cast hu2
      have l2 : (f u').toReal < q'.2 := by rw [hfu'] at hu2'; exact_mod_cast hu2'
      refine ⟨a • u + b • u', ?_, ?_⟩
      · have : a • u + b • u' - us = a • (u - us) + b • (u' - us) := by
          calc a • u + b • u' - us = a • u + b • u' - (a + b) • us := by rw [hab, one_smul]
            _ = a • (u - us) + b • (u' - us) := by rw [add_smul, smul_sub, smul_sub]; abel
        rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
        simp only [Prod.fst_add, Prod.smul_fst, smul_eq_mul]
        exact strict_comb ha hb hab hu1 hu1'
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        refine lt_of_le_of_lt H ?_
        exact_mod_cast strict_comb ha hb hab l1 l2
    have h00 : ((0:ℝ), (0:ℝ)) ∉ G := by
      rintro ⟨u, h1, h2⟩
      have := hFO u (le_of_lt (by simpa using h2))
      simp at h1; have := map_sub ℓ u us; linarith
    obtain ⟨Λ, hΛ⟩ := geometric_hahn_banach_open_point hGconv hGopen h00
    set α := Λ (1, 0) with hα
    set β := Λ (0, 1) with hβ
    have hsplit : ∀ a b : ℝ, Λ (a, b) = a * α + b * β := by
      intro a b
      have : ((a, b) : ℝ × ℝ) = a • ((1:ℝ), (0:ℝ)) + b • ((0:ℝ), (1:ℝ)) := by ext <;> simp
      rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hΛ0 : Λ ((0:ℝ), (0:ℝ)) = 0 := by rw [hsplit]; ring
    have hAB : ∀ u : U, ∀ r : ℝ, f u = (r : EReal) → ∀ A B : ℝ, ℓ (u - us) < A → r < B →
        A * α + B * β < 0 := by
      intro u r hr A B hA hB
      have := hΛ (A, B) ⟨u, hA, by rw [hr]; exact_mod_cast hB⟩
      rwa [hsplit, hΛ0] at this
    have hℓ0 : ℓ (us - us) = 0 := by simp
    have hαle : α ≤ 0 := by
      by_contra hpos; push_neg at hpos
      have := hAB us r0 hfus ((|(r0 + 1) * β| + 1) / α) (r0 + 1)
        (by rw [hℓ0]; positivity) (by linarith)
      have e : (|(r0 + 1) * β| + 1) / α * α = |(r0 + 1) * β| + 1 := by field_simp
      rw [e] at this
      have := neg_abs_le ((r0 + 1) * β)
      linarith
    have hβle : β ≤ 0 := by
      by_contra hpos; push_neg at hpos
      have := hAB us r0 hfus 1 ((|α| + |r0| + 1) / β)
        (by rw [hℓ0]; norm_num) (by
          rw [lt_div_iff₀ hpos]
          nlinarith [abs_nonneg α, abs_nonneg r0, neg_abs_le r0, le_abs_self r0])
      have e : (|α| + |r0| + 1) / β * β = |α| + |r0| + 1 := by field_simp
      rw [e] at this
      have := neg_abs_le α
      have := abs_nonneg r0
      linarith
    have hlim : ∀ u : U, ∀ r : ℝ, f u = (r : EReal) → ℓ (u - us) * α + r * β ≤ 0 := by
      intro u r hr
      by_contra hD; push_neg at hD
      set D := ℓ (u - us) * α + r * β
      rcases (show 0 ≤ -(α + β) by linarith).eq_or_lt with hS | hS
      · have := hAB u r hr (ℓ (u - us) + 1) (r + 1) (by linarith) (by linarith)
        nlinarith
      · have hε : 0 < D / (-(α + β)) := div_pos hD hS
        have := hAB u r hr (ℓ (u - us) + D / (-(α + β))) (r + D / (-(α + β)))
          (by linarith) (by linarith)
        have hne : α + β ≠ 0 := by intro h0; rw [h0] at hS; simp at hS
        have e : D / (-(α + β)) * (α + β) = -D := by field_simp
        have e2 : (ℓ (u - us) + D / -(α + β)) * α + (r + D / -(α + β)) * β
            = D + D / (-(α + β)) * (α + β) := by simp only [D]; ring
        linarith
    obtain ⟨uh, huh⟩ := hslater
    have hfuh : f uh = ((f uh).toReal : EReal) := hfin uh huh.le
    have hrh : (f uh).toReal < 0 := by rw [hfuh] at huh; exact_mod_cast huh
    have hαneg : α < 0 := by
      rcases hαle.lt_or_eq with h | h
      · exact h
      exfalso
      have hβneg : β < 0 := by
        rcases hβle.lt_or_eq with h' | h'
        · exact h'
        · exfalso
          have := hAB us r0 hfus 1 (r0 + 1) (by rw [hℓ0]; norm_num) (by linarith)
          rw [h, h'] at this; simp at this
      have := hlim uh _ hfuh
      rw [h] at this
      nlinarith
    set lam := β / α with hlam
    have hlam0 : 0 ≤ lam := div_nonneg_of_nonpos hβle hαneg.le
    have hstar : ∀ u : U, ∀ r : ℝ, f u = (r : EReal) → 0 ≤ ℓ (u - us) + lam * r := by
      intro u r hr
      have := hlim u r hr
      have e : ℓ (u - us) + lam * r = (ℓ (u - us) * α + r * β) / α := by
        have := hαneg.ne
        rw [hlam]; field_simp
      rw [e]; exact div_nonneg_of_nonpos this hαneg.le
    have hcomp : lam * r0 = 0 := by
      have := hstar us r0 hfus
      rw [hℓ0] at this
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hlam0 hr0le]
    rcases hlam0.eq_or_lt with hl | hl
    · -- `lam = 0`: then `ℓ = 0`
      obtain ⟨t, ht, htop, hct⟩ := hf_cont
      have hv : ∀ v : U, 0 ≤ ℓ v := by
        intro v
        have hT : Tendsto (fun s : ℝ => us + s • v) (𝓝[>] 0) (𝓝 us) := by
          have : Tendsto (fun s : ℝ => us + s • v) (𝓝 0) (𝓝 (us + (0:ℝ) • v)) :=
            (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        obtain ⟨s, hs, hspos⟩ := ((hT.eventually ht).and self_mem_nhdsWithin).exists
        have hfs : f (us + s • v) = ((f (us + s • v)).toReal : EReal) :=
          (EReal.coe_toReal (htop _ hs) (hf_ne_bot _)).symm
        have := hstar _ _ hfs
        rw [← hl, zero_mul, add_zero, add_sub_cancel_left, map_smul, smul_eq_mul] at this
        exact nonneg_of_mul_nonneg_right (by linarith) hspos
      have hℓz : ℓ = 0 := by
        ext v
        have h1 := hv v
        have h2 := hv (-v)
        rw [map_neg] at h2
        simp only [ContinuousLinearMap.zero_apply]
        linarith
      obtain ⟨x, hx⟩ := subdiff_nonempty f hf_convex hf_ne_bot us ⟨t, ht, htop, hct⟩
      exact ⟨0, le_rfl, ⟨x, hx, by rw [hℓz]; simp⟩, by simp⟩
    · refine ⟨lam, hlam0, ⟨(-lam⁻¹) • ℓ, ?_, ?_⟩, hcomp⟩
      · have hr00 : r0 = 0 := by
          rcases mul_eq_zero.1 hcomp with h | h
          · linarith
          · exact h
        intro w
        rw [← hr0, hr00, zero_add]
        rcases eq_or_ne (f w) ⊤ with hw | hw
        · rw [hw]; exact le_top
        have hfw : f w = ((f w).toReal : EReal) := (EReal.coe_toReal hw (hf_ne_bot w)).symm
        rw [hfw]
        apply EReal.coe_le_coe_iff.2
        have := hstar w _ hfw
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, neg_mul]
        have : lam⁻¹ * (-ℓ (w - us)) ≤ (f w).toReal := by
          rw [inv_mul_le_iff₀ hl]; linarith
        linarith [show -(lam⁻¹ * ℓ (w - us)) = lam⁻¹ * (-ℓ (w - us)) by ring]
      · ext v
        simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
        field_simp
  · rintro ⟨lam, hlam, ⟨x, hx, hxe⟩, hc⟩
    refine ⟨hus, fun u hu => ?_⟩
    have hu' : f u ≤ 0 := hu
    have hfu := hfin u hu'
    have hr : (f u).toReal ≤ 0 := by
      have := hu'; rw [hfu] at this; exact_mod_cast this
    have hsg := hx u
    rw [← hr0, hfu] at hsg
    have hsg' : r0 + x (u - us) ≤ (f u).toReal := EReal.coe_le_coe_iff.1 hsg
    have hg := convex_grad F hF_convex hF_diff us u
    have hl : ℓ (u - us) = -(lam * x (u - us)) := by
      have := congrArg (fun L : StrongDual ℝ U => L (u - us)) hxe
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul] at this
      linarith
    rw [← hℓ, hl] at hg
    nlinarith [mul_le_mul_of_nonneg_left hsg' hlam, mul_nonpos_of_nonneg_of_nonpos hlam hr]
