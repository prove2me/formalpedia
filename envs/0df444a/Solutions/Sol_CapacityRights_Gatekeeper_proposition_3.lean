-- Prove2me | solution 1 for CapacityRights.Gatekeeper.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T15:09:11.375725+00:00
-- url     : https://prove2.me/submissions/d60456d9-f26e-4b0d-9e50-c8343b43b35a

import Mathlib
import Definitions.Def_CapacityRights_Gatekeeper_Model

set_option autoImplicit false

namespace CapRightsP3

open MeasureTheory CapacityRights.Gatekeeper

def Tri (k : ℝ) : Set (ℝ × ℝ) := {q | 0 ≤ q.1 ∧ 0 ≤ q.2 ∧ q.1 + q.2 ≤ k}

lemma Tri_compact (k : ℝ) : IsCompact (Tri k) := by
  have hsub : Tri k ⊆ Set.Icc 0 k ×ˢ Set.Icc 0 k := by
    rintro ⟨a, b⟩ ⟨ha, hb, hab⟩
    dsimp only at ha hb hab
    exact ⟨⟨ha, by dsimp only; linarith⟩, ⟨hb, by dsimp only; linarith⟩⟩
  have hcl : IsClosed (Tri k) := by
    show IsClosed ({q : ℝ × ℝ | 0 ≤ q.1} ∩ ({q : ℝ × ℝ | 0 ≤ q.2} ∩ {q : ℝ × ℝ | q.1 + q.2 ≤ k}))
    exact (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_const continuous_snd).inter
        (isClosed_le (continuous_fst.add continuous_snd) continuous_const))
  exact (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hcl hsub

lemma Tri_scale {k : ℝ} (hk : 0 ≤ k) :
    Tri k = (fun s : ℝ × ℝ => (k * s.1, k * s.2)) '' Tri 1 := by
  ext ⟨a, b⟩
  simp only [Tri, Set.mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨ha, hb, hab⟩
    rcases hk.eq_or_lt with h | hk'
    · subst h
      refine ⟨0, 0, ⟨le_refl _, le_refl _, by norm_num⟩, by linarith, by linarith⟩
    · refine ⟨a / k, b / k, ⟨div_nonneg ha hk, div_nonneg hb hk, ?_⟩, ?_, ?_⟩
      · rw [← add_div, div_le_one hk']; exact hab
      · field_simp
      · field_simp
  · rintro ⟨s1, s2, ⟨h1, h2, h3⟩, rfl, rfl⟩
    exact ⟨mul_nonneg hk h1, mul_nonneg hk h2, by nlinarith⟩

lemma m1_cont (E : Env) (h : Continuous fun p : ℝ × ℝ => E.R1 p.1 p.2) :
    Continuous fun p : ℝ × ℝ => margin1 E p.1 p.2 := by
  unfold margin1; exact h.sub (continuous_const.mul continuous_fst)

lemma m2_cont (E : Env) (h : Continuous fun p : ℝ × ℝ => E.R2 p.1 p.2) :
    Continuous fun p : ℝ × ℝ => margin2 E p.1 p.2 := by
  unfold margin2; exact h.sub (continuous_const.mul continuous_fst)

noncomputable def F1 (E : Env) (k e1 : ℝ) : ℝ :=
  sSup ((fun s => margin1 E (k * s) e1) '' Set.Icc 0 1)

noncomputable def F2 (E : Env) (k e2 : ℝ) : ℝ :=
  sSup ((fun s => margin2 E (k * s) e2) '' Set.Icc 0 1)

noncomputable def Ft (E : Env) (k : ℝ) (e : ℝ × ℝ) : ℝ :=
  sSup ((fun s : ℝ × ℝ => margin1 E (k * s.1) e.1 + margin2 E (k * s.2) e.2) '' Tri 1)

lemma F1_cont (E : Env) (h : Continuous fun p : ℝ × ℝ => E.R1 p.1 p.2) :
    Continuous fun p : ℝ × ℝ => F1 E p.1 p.2 := by
  have hf : Continuous fun x : (ℝ × ℝ) × ℝ => margin1 E (x.1.1 * x.2) x.1.2 :=
    (m1_cont E h).comp ((continuous_fst.fst.mul continuous_snd).prodMk continuous_fst.snd)
  exact IsCompact.continuous_sSup (f := fun (p : ℝ × ℝ) (s : ℝ) => margin1 E (p.1 * s) p.2)
    isCompact_Icc hf

lemma F2_cont (E : Env) (h : Continuous fun p : ℝ × ℝ => E.R2 p.1 p.2) :
    Continuous fun p : ℝ × ℝ => F2 E p.1 p.2 := by
  have hf : Continuous fun x : (ℝ × ℝ) × ℝ => margin2 E (x.1.1 * x.2) x.1.2 :=
    (m2_cont E h).comp ((continuous_fst.fst.mul continuous_snd).prodMk continuous_fst.snd)
  exact IsCompact.continuous_sSup (f := fun (p : ℝ × ℝ) (s : ℝ) => margin2 E (p.1 * s) p.2)
    isCompact_Icc hf

lemma Ft_cont (E : Env) (h1 : Continuous fun p : ℝ × ℝ => E.R1 p.1 p.2)
    (h2 : Continuous fun p : ℝ × ℝ => E.R2 p.1 p.2) :
    Continuous fun p : ℝ × (ℝ × ℝ) => Ft E p.1 p.2 := by
  have hf : Continuous fun x : (ℝ × (ℝ × ℝ)) × (ℝ × ℝ) =>
      margin1 E (x.1.1 * x.2.1) x.1.2.1 + margin2 E (x.1.1 * x.2.2) x.1.2.2 :=
    ((m1_cont E h1).comp ((continuous_fst.fst.mul continuous_snd.fst).prodMk
        continuous_fst.snd.fst)).add
      ((m2_cont E h2).comp ((continuous_fst.fst.mul continuous_snd.snd).prodMk
        continuous_fst.snd.snd))
  exact IsCompact.continuous_sSup (f := fun (p : ℝ × (ℝ × ℝ)) (s : ℝ × ℝ) =>
    margin1 E (p.1 * s.1) p.2.1 + margin2 E (p.1 * s.2) p.2.2) (Tri_compact 1) hf

lemma CM1_eq (E : Env) {k : ℝ} (hk : 0 ≤ k) (e1 : ℝ) : CM1 E k e1 = F1 E k e1 := by
  unfold CM1 F1
  have : Set.Icc (0:ℝ) k = (fun s => k * s) '' Set.Icc 0 1 := by
    rw [Set.image_mul_left_Icc hk zero_le_one]; simp
  rw [this, Set.image_image]

lemma CM2_eq (E : Env) {k : ℝ} (hk : 0 ≤ k) (e2 : ℝ) : CM2 E k e2 = F2 E k e2 := by
  unfold CM2 F2
  have : Set.Icc (0:ℝ) k = (fun s => k * s) '' Set.Icc 0 1 := by
    rw [Set.image_mul_left_Icc hk zero_le_one]; simp
  rw [this, Set.image_image]

lemma CMtot_img (E : Env) (k : ℝ) (e : ℝ × ℝ) :
    CMtot E k e = sSup ((fun q : ℝ × ℝ => margin1 E q.1 e.1 + margin2 E q.2 e.2) '' Tri k) := by
  unfold CMtot
  congr 1
  ext x
  constructor
  · rintro ⟨q1, q2, h1, h2, h3, rfl⟩
    exact ⟨(q1, q2), ⟨h1, h2, h3⟩, rfl⟩
  · rintro ⟨⟨q1, q2⟩, ⟨h1, h2, h3⟩, rfl⟩
    exact ⟨q1, q2, h1, h2, h3, rfl⟩

lemma CMtot_eq (E : Env) {k : ℝ} (hk : 0 ≤ k) (e : ℝ × ℝ) : CMtot E k e = Ft E k e := by
  rw [CMtot_img E k e, Tri_scale hk, Set.image_image] <;> rfl

lemma integrable_of_cont (E : Env) (hS : E.Standing) {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    Integrable f E.μ := by
  obtain ⟨hprob, hbox, -⟩ := hS
  haveI := hprob
  have hμ : E.μ.restrict (shockBox E) = E.μ :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hbox)
  have hK : IsCompact (shockBox E) := isCompact_Icc.prod isCompact_Icc
  have : IntegrableOn f (shockBox E) E.μ := hf.continuousOn.integrableOn_compact hK
  rwa [IntegrableOn, hμ] at this

lemma cont_param (E : Env) (hS : E.Standing) {G : ℝ → ℝ × ℝ → ℝ}
    (hG : Continuous fun p : ℝ × (ℝ × ℝ) => G p.1 p.2) :
    Continuous fun k => ∫ e, G k e ∂E.μ := by
  obtain ⟨hprob, hbox, -⟩ := hS
  haveI := hprob
  have hμ : E.μ.restrict (shockBox E) = E.μ :=
    Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.2 hbox)
  have hK : IsCompact (shockBox E) := isCompact_Icc.prod isCompact_Icc
  have := continuous_parametric_integral_of_continuous (μ := E.μ) (f := G) hG hK
  rwa [hμ] at this

noncomputable def I1 (E : Env) (k : ℝ) : ℝ := ∫ e, CM1 E k e.1 ∂E.μ
noncomputable def I2 (E : Env) (k : ℝ) : ℝ := ∫ e, CM2 E k e.2 ∂E.μ
noncomputable def It (E : Env) (k : ℝ) : ℝ := ∫ e, CMtot E k e ∂E.μ

lemma int1 (E : Env) (hS : E.Standing) {k : ℝ} (hk : 0 ≤ k) :
    Integrable (fun e : ℝ × ℝ => CM1 E k e.1) E.μ := by
  have : (fun e : ℝ × ℝ => CM1 E k e.1) = fun e => F1 E k e.1 :=
    funext fun e => CM1_eq E hk e.1
  rw [this]
  exact integrable_of_cont E hS ((F1_cont E hS.2.2.2.2.2.2.2.2.2.1).comp
    (continuous_const.prodMk continuous_fst))

lemma int2 (E : Env) (hS : E.Standing) {k : ℝ} (hk : 0 ≤ k) :
    Integrable (fun e : ℝ × ℝ => CM2 E k e.2) E.μ := by
  have : (fun e : ℝ × ℝ => CM2 E k e.2) = fun e => F2 E k e.2 :=
    funext fun e => CM2_eq E hk e.2
  rw [this]
  exact integrable_of_cont E hS ((F2_cont E hS.2.2.2.2.2.2.2.2.2.2.1).comp
    (continuous_const.prodMk continuous_snd))

lemma intt (E : Env) (hS : E.Standing) {k : ℝ} (hk : 0 ≤ k) :
    Integrable (fun e : ℝ × ℝ => CMtot E k e) E.μ := by
  have : (fun e : ℝ × ℝ => CMtot E k e) = fun e => Ft E k e :=
    funext fun e => CMtot_eq E hk e
  rw [this]
  exact integrable_of_cont E hS ((Ft_cont E hS.2.2.2.2.2.2.2.2.2.1
    hS.2.2.2.2.2.2.2.2.2.2.1).comp (continuous_const.prodMk continuous_id))

lemma concave_incr {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f) {a b Δ : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hΔ : 0 ≤ Δ) : f a + f (b + Δ) ≤ f (a + Δ) + f b := by
  rcases (add_nonneg (sub_nonneg.2 hab) hΔ).eq_or_lt with h0 | hpos
  · have h1 : b = a := by linarith
    have h2 : Δ = 0 := by linarith
    subst h1 h2; simp
  · obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (b - a) / (b - a + Δ) := ⟨_, rfl⟩
    have htm : t * (b - a + Δ) = b - a := by rw [ht]; exact div_mul_cancel₀ _ hpos.ne'
    have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (sub_nonneg.2 hab) hpos.le
    have ht1 : t ≤ 1 := by rw [ht, div_le_one hpos]; linarith
    have hx : a ∈ Set.Ici (0:ℝ) := ha
    have hy : b + Δ ∈ Set.Ici (0:ℝ) := by show 0 ≤ b + Δ; linarith
    have hA := hf.2 hx hy ht0 (sub_nonneg.2 ht1) (by ring)
    have hB := hf.2 hx hy (sub_nonneg.2 ht1) ht0 (by ring)
    have e1 : t • a + (1 - t) • (b + Δ) = a + Δ := by
      simp only [smul_eq_mul]; linear_combination (-1:ℝ) * htm
    have e2 : (1 - t) • a + t • (b + Δ) = b := by
      simp only [smul_eq_mul]; linear_combination htm
    rw [e1] at hA; rw [e2] at hB
    simp only [smul_eq_mul] at hA hB
    linarith

lemma m1_concave (E : Env) (hS : E.Standing) {e1 : ℝ} (he : e1 ∈ Set.Icc E.a1 E.b1) :
    ConcaveOn ℝ (Set.Ici 0) (fun q => margin1 E q e1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hP1, -, -, -⟩ := hS
  have hc := (hP1 e1 he).2.1.concaveOn
  refine ⟨convex_Ici 0, fun x hx y hy a b ha hb hab => ?_⟩
  have := hc.2 hx hy ha hb hab
  simp only [margin1, smul_eq_mul] at this ⊢
  linarith

lemma incr_pt (E : Env) (hS : E.Standing) {e : ℝ × ℝ} (he : e.1 ∈ Set.Icc E.a1 E.b1)
    {k0 k : ℝ} (h0 : 0 ≤ k0) (hk : k0 ≤ k) :
    CM1 E k e.1 + CMtot E k0 e ≤ CMtot E k e + CM1 E k0 e.1 := by
  have hcv := m1_concave E hS he
  obtain ⟨-, -, -, -, -, -, -, -, -, hc1, hc2, -⟩ := hS
  have hm1 : Continuous fun q => margin1 E q e.1 :=
    (m1_cont E hc1).comp (continuous_id.prodMk continuous_const)
  have hM : Continuous fun q : ℝ × ℝ => margin1 E q.1 e.1 + margin2 E q.2 e.2 :=
    ((m1_cont E hc1).comp (continuous_fst.prodMk continuous_const)).add
      ((m2_cont E hc2).comp (continuous_snd.prodMk continuous_const))
  rw [CMtot_img, CMtot_img]
  unfold CM1
  set m1 : ℝ → ℝ := fun q => margin1 E q e.1 with hm1def
  set M : ℝ × ℝ → ℝ := fun q => margin1 E q.1 e.1 + margin2 E q.2 e.2 with hMdef
  have hb1 : ∀ c, BddAbove (m1 '' Set.Icc 0 c) := fun c => (isCompact_Icc.image hm1).bddAbove
  have hbT : ∀ c, BddAbove (M '' Tri c) := fun c => ((Tri_compact c).image hM).bddAbove
  have key : ∀ q ∈ Set.Icc 0 k, ∀ x ∈ Tri k0,
      m1 q + M x ≤ sSup (M '' Tri k) + sSup (m1 '' Set.Icc 0 k0) := by
    rintro q ⟨hq0, hqk⟩ ⟨a, b⟩ ⟨ha, hb, hab⟩
    dsimp only at ha hb hab
    have hMab : M (a, b) = m1 a + margin2 E b e.2 := rfl
    rcases le_total q k0 with hq | hq
    · have h1 : m1 q ≤ sSup (m1 '' Set.Icc 0 k0) := le_csSup (hb1 k0) ⟨q, ⟨hq0, hq⟩, rfl⟩
      have h2 : M (a, b) ≤ sSup (M '' Tri k) :=
        le_csSup (hbT k) ⟨(a, b), ⟨ha, hb, by dsimp only; linarith⟩, rfl⟩
      linarith
    · have hcc := concave_incr hcv ha (show a ≤ k0 by linarith) (show 0 ≤ q - k0 by linarith)
      have hq' : k0 + (q - k0) = q := by ring
      rw [hq'] at hcc
      have h1 : m1 k0 ≤ sSup (m1 '' Set.Icc 0 k0) := le_csSup (hb1 k0) ⟨k0, ⟨h0, le_rfl⟩, rfl⟩
      have h2 : M (a + (q - k0), b) ≤ sSup (M '' Tri k) :=
        le_csSup (hbT k) ⟨(a + (q - k0), b), ⟨by dsimp only; linarith, hb,
          by dsimp only; linarith⟩, rfl⟩
      have hM2 : M (a + (q - k0), b) = m1 (a + (q - k0)) + margin2 E b e.2 := rfl
      linarith
  have hne1 : (m1 '' Set.Icc 0 k).Nonempty := (Set.nonempty_Icc.2 (h0.trans hk)).image _
  have hneT : (M '' Tri k0).Nonempty :=
    ⟨_, ⟨(0, 0), ⟨le_rfl, le_rfl, by show (0:ℝ) + 0 ≤ k0; linarith⟩, rfl⟩⟩
  have step : ∀ q ∈ Set.Icc 0 k, m1 q + sSup (M '' Tri k0) ≤
      sSup (M '' Tri k) + sSup (m1 '' Set.Icc 0 k0) := by
    intro q hq
    have : sSup (M '' Tri k0) ≤ sSup (M '' Tri k) + sSup (m1 '' Set.Icc 0 k0) - m1 q :=
      csSup_le hneT (by rintro _ ⟨x, hx, rfl⟩; have := key q hq x hx; linarith)
    linarith
  have : sSup (m1 '' Set.Icc 0 k) ≤
      sSup (M '' Tri k) + sSup (m1 '' Set.Icc 0 k0) - sSup (M '' Tri k0) :=
    csSup_le hne1 (by rintro _ ⟨q, hq, rfl⟩; have := step q hq; linarith)
  linarith

lemma incr_int (E : Env) (hS : E.Standing) {k0 k : ℝ} (h0 : 0 ≤ k0) (hk : k0 ≤ k) :
    I1 E k + It E k0 ≤ It E k + I1 E k0 := by
  have hk' : 0 ≤ k := h0.trans hk
  have hae : ∀ᵐ e ∂E.μ, e ∈ shockBox E := mem_ae_iff.2 hS.2.1
  have hl : Integrable (fun e : ℝ × ℝ => CM1 E k e.1 + CMtot E k0 e) E.μ :=
    (int1 E hS hk').add (intt E hS h0)
  have hr : Integrable (fun e : ℝ × ℝ => CMtot E k e + CM1 E k0 e.1) E.μ :=
    (intt E hS hk').add (int1 E hS h0)
  have h := integral_mono_ae hl hr (hae.mono fun e he => incr_pt E hS he.1 h0 hk)
  rw [integral_add (int1 E hS hk') (intt E hS h0),
    integral_add (intt E hS hk') (int1 E hS h0)] at h
  exact h

lemma small (E : Env) (hS : E.Standing) {k : ℝ} (hk : 0 ≤ k) :
    k * (∫ e, deriv (fun q => E.R1 q e.1) k ∂E.μ) - E.w1 * k ≤ I1 E k - I1 E 0 := by
  obtain ⟨hprob, hbox, -, -, -, -, -, -, -, hc1, -, hd1, -, hP1, -, -, -⟩ := id hS
  haveI := hprob
  have hae : ∀ᵐ e ∂E.μ, e ∈ shockBox E := mem_ae_iff.2 hbox
  have hDi : Integrable (fun e : ℝ × ℝ => deriv (fun q => E.R1 q e.1) k) E.μ :=
    integrable_of_cont E hS (hd1.comp (continuous_const.prodMk continuous_fst))
  have hpt : ∀ᵐ e ∂E.μ,
      k * deriv (fun q => E.R1 q e.1) k - E.w1 * k ≤ CM1 E k e.1 - CM1 E 0 e.1 := by
    filter_upwards [hae] with e he
    have he1 : e.1 ∈ Set.Icc E.a1 E.b1 := he.1
    obtain ⟨-, hcv, hdiff, -⟩ := hP1 e.1 he1
    have h0 : CM1 E 0 e.1 = E.R1 0 e.1 := by
      unfold CM1; rw [Set.Icc_self, Set.image_singleton, csSup_singleton]; simp [margin1]
    have hm1 : Continuous fun q => margin1 E q e.1 :=
      (m1_cont E hc1).comp (continuous_id.prodMk continuous_const)
    have hk' : margin1 E k e.1 ≤ CM1 E k e.1 :=
      le_csSup ((isCompact_Icc.image hm1).bddAbove) ⟨k, ⟨hk, le_rfl⟩, rfl⟩
    have hsl : k * deriv (fun q => E.R1 q e.1) k ≤ E.R1 k e.1 - E.R1 0 e.1 := by
      rcases hk.eq_or_lt with h | h
      · subst h; simp
      · have := hcv.concaveOn.deriv_le_slope (x := 0) (y := k) (Set.mem_Ici.2 le_rfl)
          (Set.mem_Ici.2 hk) h (hdiff k)
        rw [slope_def_field, sub_zero, le_div_iff₀ h] at this
        try dsimp only at this
        linarith
    unfold margin1 at hk'
    linarith
  have hR : Integrable (fun e : ℝ × ℝ => CM1 E k e.1 - CM1 E 0 e.1) E.μ :=
    (int1 E hS hk).sub (int1 E hS le_rfl)
  have hL : Integrable (fun e : ℝ × ℝ => k * deriv (fun q => E.R1 q e.1) k - E.w1 * k) E.μ :=
    (hDi.const_mul k).sub (integrable_const _)
  have h := integral_mono_ae hL hR hpt
  rw [integral_sub (hDi.const_mul k) (integrable_const _), integral_const_mul,
    integral_sub (int1 E hS hk) (int1 E hS le_rfl)] at h
  simpa [I1] using h

lemma eff1_int (E : Env) (hS : E.Standing) {k1 k2 : ℝ} (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2) :
    ∫ e, CMeff1 E k1 k2 e ∂E.μ
      = (1 - E.δ) * I1 E k1 + E.δ * (It E (k1 + k2) - I2 E k2) := by
  unfold CMeff1 I1 I2 It
  rw [integral_add (show Integrable (fun e : ℝ × ℝ => (1 - E.δ) * CM1 E k1 e.1) E.μ from
      (int1 E hS hk1).const_mul _)
      (show Integrable (fun e : ℝ × ℝ => E.δ * (CMtot E (k1 + k2) e - CM2 E k2 e.2)) E.μ from
      ((intt E hS (add_nonneg hk1 hk2)).sub (int2 E hS hk2)).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_sub (intt E hS (add_nonneg hk1 hk2)) (int2 E hS hk2)]

lemma eff2_int (E : Env) (hS : E.Standing) {k1 k2 : ℝ} (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2) :
    ∫ e, CMeff2 E k1 k2 e ∂E.μ
      = E.δ * I2 E k2 + (1 - E.δ) * (It E (k1 + k2) - I1 E k1) := by
  unfold CMeff2 I1 I2 It
  rw [integral_add (show Integrable (fun e : ℝ × ℝ => E.δ * CM2 E k2 e.2) E.μ from
      (int2 E hS hk2).const_mul _)
      (show Integrable (fun e : ℝ × ℝ => (1 - E.δ) * (CMtot E (k1 + k2) e - CM1 E k1 e.1)) E.μ from
      ((intt E hS (add_nonneg hk1 hk2)).sub (int1 E hS hk1)).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_sub (intt E hS (add_nonneg hk1 hk2)) (int1 E hS hk1)]

lemma RI1_eq (E : Env) (hS : E.Standing) {d : ℕ → ℝ} (hd : IsAnnuity E d) {t : ℕ}
    (ht : t ∈ Finset.Icc 1 E.T) {k1 k2 p : ℝ} (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2) :
    RI1 E d t k1 k2 p = (1 - E.δ) * I1 E k1 + E.δ * (It E (k1 + k2) - I2 E k2)
      - ucc E * (k1 + k2) + p := by
  unfold RI1
  rw [eff1_int E hS hk1 hk2, hd.2.2 t ht]
  unfold ucc; ring

lemma Profit2_eq (E : Env) (hS : E.Standing) {k1 k2 p : ℝ} (hk1 : 0 ≤ k1) (hk2 : 0 ≤ k2) :
    Profit2 E k1 k2 p = E.δ * I2 E k2 + (1 - E.δ) * (It E (k1 + k2) - I1 E k1) - p := by
  unfold Profit2
  rw [eff2_int E hS hk1 hk2]

lemma npv_eq (E : Env) (k : ℝ) : NPV E k = annuityFactor E * It E k - E.v * k := by
  unfold NPV annuityFactor It
  rw [Finset.sum_mul]

lemma I1_cont (E : Env) (hS : E.Standing) : ContinuousOn (I1 E) (Set.Ici 0) := by
  have hc : Continuous fun k => ∫ e, F1 E k e.1 ∂E.μ :=
    cont_param E hS (G := fun k e => F1 E k e.1)
      ((F1_cont E hS.2.2.2.2.2.2.2.2.2.1).comp (continuous_fst.prodMk continuous_snd.fst))
  refine hc.continuousOn.congr fun k hk => ?_
  simp only [I1]
  congr 1
  funext e
  exact CM1_eq E hk e.1

lemma It_cont (E : Env) (hS : E.Standing) : ContinuousOn (It E) (Set.Ici 0) := by
  have hc : Continuous fun k => ∫ e, Ft E k e ∂E.μ :=
    cont_param E hS (G := fun k e => Ft E k e)
      (Ft_cont E hS.2.2.2.2.2.2.2.2.2.1 hS.2.2.2.2.2.2.2.2.2.2.1)
  refine hc.continuousOn.congr fun k hk => ?_
  simp only [It]
  congr 1
  funext e
  exact CMtot_eq E hk e

end CapRightsP3

open CapRightsP3

open CapacityRights.Gatekeeper MeasureTheory in
theorem solution (E : Env) (hS : E.Standing)
    (h20_1 : ucc E + E.w1 < ∫ e, deriv (fun q => E.R1 q e.1) 0 ∂E.μ)
    (h20_2 : ucc E + E.w2 < ∫ e, deriv (fun q => E.R2 q e.2) 0 ∂E.μ)
    (d : ℕ → ℝ) (hd : IsAnnuity E d)
    (kstar : ℝ) (hk : IsEfficient E kstar) :
    ∃ k2 ∈ Set.Ico 0 kstar, ∃ p : ℝ,
      (∀ t ∈ Finset.Icc 1 E.T,
        IsBestResponse1 E d t k2 p (kstar - k2)) ∧
      (∀ t ∈ Finset.Icc 1 E.T,
        ∃ khat : ℝ, IsBestResponse1 E d t 0 0 khat) ∧
      (∀ t ∈ Finset.Icc 1 E.T, ∀ khat : ℝ,
        IsBestResponse1 E d t 0 0 khat →
          RI1 E d t khat 0 0 ≤ RI1 E d t (kstar - k2) k2 p ∧
          Profit2 E khat 0 0 ≤ Profit2 E (kstar - k2) k2 p) := by
  obtain ⟨hprob, hbox, ha1, ha2, hv, hr, hT, hδ0, hδ1, hc1, hc2, hd1, hd2, hP1, hP2, -, -⟩ := id hS
  have hγ : 0 < γ E := by unfold γ; exact inv_pos.2 (by linarith)
  have hA : 0 < annuityFactor E := by
    unfold annuityFactor
    exact Finset.sum_pos (fun t _ => pow_pos hγ t) ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hT⟩⟩
  have hAu : annuityFactor E * ucc E = E.v := by unfold ucc; field_simp
  have hJ : ∀ k, 0 ≤ k → It E k - ucc E * k ≤ It E kstar - ucc E * kstar := by
    intro k hk0
    have h1 := hk.2 k hk0
    rw [npv_eq, npv_eq] at h1
    have : annuityFactor E * (It E k - ucc E * k)
        ≤ annuityFactor E * (It E kstar - ucc E * kstar) := by
      rw [mul_sub, mul_sub, ← mul_assoc, ← mul_assoc, hAu]; linarith
    exact le_of_mul_le_mul_left this hA
  have hHk : ∀ k, kstar ≤ k → I1 E k - ucc E * k ≤ I1 E kstar - ucc E * kstar := by
    intro k hk'
    have := incr_int E hS hk.1 hk'
    have := hJ k (hk.1.trans hk')
    linarith
  obtain ⟨ε, hε, hD⟩ : ∃ ε > 0, ∀ k, 0 < k → k < ε →
      ucc E + E.w1 < ∫ e, deriv (fun q => E.R1 q e.1) k ∂E.μ := by
    have hc : Continuous fun k => ∫ e, deriv (fun q => E.R1 q e.1) k ∂E.μ :=
      cont_param E hS (G := fun k e => deriv (fun q => E.R1 q e.1) k)
        (hd1.comp (continuous_fst.prodMk continuous_snd.fst))
    obtain ⟨ε, hε, h⟩ := Metric.eventually_nhds_iff.1
      (hc.continuousAt.eventually (lt_mem_nhds h20_1))
    exact ⟨ε, hε, fun k hk0 hkε => h (by rw [Real.dist_eq, sub_zero, abs_of_pos hk0]; exact hkε)⟩
  have hHsmall : ∀ k, 0 < k → k < ε → I1 E 0 - ucc E * 0 < I1 E k - ucc E * k := by
    intro k hk0 hkε
    have h1 := small E hS hk0.le
    have h2 := mul_lt_mul_of_pos_left (hD k hk0 hkε) hk0
    linarith
  have hkpos : 0 < kstar := by
    rcases hk.1.eq_or_lt with h | h
    · exfalso
      have hk2 : (0:ℝ) < ε / 2 := by linarith
      have h1 := hHsmall (ε / 2) hk2 (by linarith)
      have h2 := incr_int E hS (le_refl 0) hk2.le
      have h3 := hJ (ε / 2) hk2.le
      rw [← h] at h3
      linarith
    · exact h
  have hk'pos : 0 < min (ε / 2) kstar := lt_min (by linarith) hkpos
  have hk'ε : min (ε / 2) kstar < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hk'le : min (ε / 2) kstar ≤ kstar := min_le_right _ _
  have hHc : ContinuousOn (fun k => I1 E k - ucc E * k) (Set.Icc 0 kstar) :=
    ((I1_cont E hS).mono Set.Icc_subset_Ici_self).sub (continuousOn_const.mul continuousOn_id)
  obtain ⟨k1o, hk1o_mem, hk1o_max⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc 0 kstar)).exists_isMaxOn (Set.nonempty_Icc.2 hk.1) hHc
  have hHmax : ∀ k, 0 ≤ k → I1 E k - ucc E * k ≤ I1 E k1o - ucc E * k1o := by
    intro k hk0
    rcases le_total k kstar with h | h
    · exact isMaxOn_iff.1 hk1o_max k ⟨hk0, h⟩
    · exact (hHk k h).trans (isMaxOn_iff.1 hk1o_max kstar ⟨hk.1, le_rfl⟩)
  have hk1o_pos : 0 < k1o := by
    rcases hk1o_mem.1.eq_or_lt with h | h
    · exfalso
      have h1 := hHsmall _ hk'pos hk'ε
      have h2 := isMaxOn_iff.1 hk1o_max _ ⟨hk'pos.le, hk'le⟩
      rw [← h] at h2
      linarith
    · exact h
  have hGc : ContinuousOn (fun k => (1 - E.δ) * (I1 E k - ucc E * k)
      + E.δ * (It E k - ucc E * k)) (Set.Icc 0 kstar) :=
    (continuousOn_const.mul hHc).add (continuousOn_const.mul
      (((It_cont E hS).mono Set.Icc_subset_Ici_self).sub
        (continuousOn_const.mul continuousOn_id)))
  obtain ⟨kh, hkh_mem, hkh_max⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc 0 kstar)).exists_isMaxOn (Set.nonempty_Icc.2 hk.1) hGc
  have hGmax : ∀ k, 0 ≤ k → (1 - E.δ) * (I1 E k - ucc E * k) + E.δ * (It E k - ucc E * k)
      ≤ (1 - E.δ) * (I1 E kh - ucc E * kh) + E.δ * (It E kh - ucc E * kh) := by
    intro k hk0
    rcases le_total k kstar with h | h
    · exact isMaxOn_iff.1 hkh_max k ⟨hk0, h⟩
    · have h1 := hHk k h
      have h2 := hJ k (hk.1.trans h)
      have h3 := isMaxOn_iff.1 hkh_max kstar ⟨hk.1, le_rfl⟩
      have h4 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hδ1)
      have h5 := mul_le_mul_of_nonneg_left h2 hδ0
      try dsimp only at h3
      linarith
  have hk2_0 : 0 ≤ kstar - k1o := sub_nonneg.2 hk1o_mem.2
  obtain ⟨k2, rfl⟩ : ∃ k2, kstar = k1o + k2 := ⟨kstar - k1o, by ring⟩
  have hk2' : 0 ≤ k2 := by linarith
  have e0 : k1o + k2 - k2 = k1o := by ring
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = ((1 - E.δ) * (I1 E kh - ucc E * kh)
      + E.δ * (It E kh - ucc E * kh) - E.δ * I2 E 0)
      - ((1 - E.δ) * I1 E k1o + E.δ * (It E (k1o + k2) - I2 E k2)
        - ucc E * (k1o + k2)) := ⟨_, rfl⟩
  refine ⟨k2, ⟨hk2', by linarith⟩, p, ?_, ?_, ?_⟩
  · intro t ht
    rw [e0]
    refine ⟨hk1o_mem.1, fun k1' hk1' => ?_⟩
    rw [RI1_eq E hS hd ht hk1' hk2', RI1_eq E hS hd ht hk1o_mem.1 hk2']
    have h1 := hHmax k1' hk1'
    have h2 := hJ (k1' + k2) (add_nonneg hk1' hk2')
    have h4 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.2 hδ1)
    have h5 := mul_le_mul_of_nonneg_left h2 hδ0
    linarith
  · intro t ht
    refine ⟨kh, hkh_mem.1, fun k1' hk1' => ?_⟩
    rw [RI1_eq E hS hd ht hk1' le_rfl, RI1_eq E hS hd ht hkh_mem.1 le_rfl]
    have := hGmax k1' hk1'
    simp only [add_zero]
    linarith
  · intro t ht khat hBR
    obtain ⟨hkh0, hBRmax⟩ := hBR
    have hb := hBRmax kh hkh_mem.1
    rw [RI1_eq E hS hd ht hkh_mem.1 le_rfl, RI1_eq E hS hd ht hkh0 le_rfl] at hb
    simp only [add_zero] at hb
    rw [e0]
    constructor
    · rw [RI1_eq E hS hd ht hkh0 le_rfl, RI1_eq E hS hd ht hk1o_mem.1 hk2']
      have := hGmax khat hkh0
      simp only [add_zero]
      linarith
    · rw [Profit2_eq E hS hkh0 le_rfl, Profit2_eq E hS hk1o_mem.1 hk2']
      have := hJ khat hkh0
      simp only [add_zero]
      linarith
