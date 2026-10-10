-- Prove2me | solution 1 for ConvexOptAlg.CenterGravity.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-09T22:03:13.443984+00:00
-- url     : https://prove2.me/submissions/33e62190-f855-4b54-872e-bce601c73246

import Mathlib
import Definitions.Def_ConvexOptAlg_CenterGravity_Defs
import Definitions.Def_LogConcaveOn
import Theorems.Thm_ConvexOptimization_prekopa_marginal_log_concave

section PieceA
open MeasureTheory Set

namespace GrunbaumAux1

noncomputable def S (f : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in Ici t, f s

section generic
variable {f : ℝ → ℝ} {R : ℝ}

lemma S_eq_interval (hR : ∀ t, R < |t| → f t = 0) (t : ℝ) :
    S f t = ∫ s in t..R, f s := by
  unfold S
  rcases le_or_gt t R with h | h
  · rw [intervalIntegral.integral_of_le h, integral_Ici_eq_integral_Ioi]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    intro x hx
    apply hR
    have h1 : R < x := by
      by_contra hh
      exact hx.2 ⟨hx.1, not_lt.mp hh⟩
    exact lt_of_lt_of_le h1 (le_abs_self x)
  · have h1 : ∫ s in Ici t, f s = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      apply hR
      exact lt_of_lt_of_le (lt_of_lt_of_le h hx) (le_abs_self x)
    have h2 : ∫ s in Ioc R t, f s = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      apply hR
      exact lt_of_lt_of_le hx.1 (le_abs_self x)
    rw [h1, intervalIntegral.integral_symm, intervalIntegral.integral_of_le h.le, h2]
    simp


lemma S_cont (hint : Integrable f) (hR : ∀ t, R < |t| → f t = 0) : Continuous (S f) := by
  have : S f = fun t => -(∫ s in R..t, f s) := by
    funext t
    rw [S_eq_interval hR, intervalIntegral.integral_symm]
  rw [this]
  exact (hint.continuous_primitive R).neg

lemma S_nonneg (hf0 : ∀ t, 0 ≤ f t) (t : ℝ) : 0 ≤ S f t :=
  setIntegral_nonneg measurableSet_Ici (fun x _ => hf0 x)

lemma S_zero (hR : ∀ t, R < |t| → f t = 0) {t : ℝ} (h : R < t) : S f t = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro x hx
  apply hR
  exact lt_of_lt_of_le (lt_of_lt_of_le h hx) (le_abs_self x)

lemma S_integrableOn (hint : Integrable f) (hR : ∀ t, R < |t| → f t = 0) (hR0 : 0 ≤ R) :
    IntegrableOn (S f) (Ici 0) := by
  have : Ici (0:ℝ) = Icc 0 R ∪ Ioi R := by
    ext x
    simp only [mem_Ici, mem_union, mem_Icc, mem_Ioi]
    constructor
    · intro hx
      rcases le_or_gt x R with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    · rintro (h | h)
      · exact h.1
      · linarith
  rw [this]
  refine IntegrableOn.union ?_ ?_
  · exact (S_cont hint hR).continuousOn.integrableOn_Icc
  · exact (integrableOn_zero (s := Ioi R)).congr_fun (fun x hx => (S_zero hR hx).symm) measurableSet_Ioi


lemma layer_cake (hmeas : Measurable f) (hf0 : ∀ t, 0 ≤ f t) (hint : Integrable f)
    (hR : ∀ t, R < |t| → f t = 0) :
    ∫ t in Ici 0, t * f t = ∫ u in Ici 0, S f u := by
  set A : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2} with hA
  have hAm : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_snd)
  set H : ℝ × ℝ → ℝ := A.indicator (fun p => f p.2) with hH
  have hHm : Measurable H := (hmeas.comp measurable_snd).indicator hAm
  have hHint : Integrable H (volume.prod volume) := by
    have h1 : Integrable ((Icc 0 R).indicator (fun _ => (1:ℝ))) volume :=
      (integrable_indicator_iff measurableSet_Icc).2 (by simp)
    have hb : Integrable (fun z : ℝ × ℝ => (Icc 0 R).indicator (fun _ => (1:ℝ)) z.1 * f z.2)
        (volume.prod volume) := Integrable.mul_prod h1 hint
    refine hb.mono' hHm.aestronglyMeasurable (Filter.Eventually.of_forall ?_)
    intro p
    have hnn : 0 ≤ (Icc 0 R).indicator (fun _ => (1:ℝ)) p.1 * f p.2 :=
      mul_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (hf0 _)
    by_cases hp : p ∈ A
    · have hHp : H p = f p.2 := by simp [hH, hp]
      rw [hHp, Real.norm_of_nonneg (hf0 _)]
      by_cases h1 : p.1 ≤ R
      · have : (Icc 0 R).indicator (fun _ => (1:ℝ)) p.1 = 1 := indicator_of_mem (show p.1 ∈ Icc 0 R from ⟨hp.1, h1⟩) _
        rw [this, one_mul]
      · have : f p.2 = 0 := hR _ (lt_of_lt_of_le (not_le.mp h1) (le_trans hp.2 (le_abs_self _)))
        rw [this, mul_zero]
    · rw [hH, indicator_of_notMem hp]; simpa using hnn
  have h1 : ∀ u, ∫ s, H (u, s) = (Ici 0).indicator (S f) u := by
    intro u
    by_cases hu : 0 ≤ u
    · have : (fun s => H (u,s)) = (Ici u).indicator f := by
        funext s
        by_cases hs : u ≤ s
        · simp [hH, hA, indicator, hu, hs]
        · simp [hH, hA, indicator, hu, hs]
      simp only [this]
      rw [integral_indicator measurableSet_Ici, indicator_of_mem (show u ∈ Ici (0:ℝ) from hu)]
      rfl
    · have : (fun s => H (u,s)) = fun _ => 0 := by
        funext s
        simp [hH, hA, indicator, hu]
      simp only [this]
      rw [indicator_of_notMem (show u ∉ Ici (0:ℝ) from hu)]
      simp
  have h2 : ∀ s, ∫ u, H (u, s) = (Ici 0).indicator (fun s => s * f s) s := by
    intro s
    have : (fun u => H (u,s)) = (Icc 0 s).indicator (fun _ => f s) := by
      funext u
      by_cases hu : 0 ≤ u ∧ u ≤ s
      · simp [hH, hA, indicator, hu.1, hu.2]
      · have : ¬ (0 ≤ u ∧ u ≤ s) := hu
        simp only [hH, hA, indicator, mem_setOf_eq, mem_Icc, this, if_false]
    simp only [this]
    rw [integral_indicator_const _ measurableSet_Icc]
    by_cases hs : 0 ≤ s
    · rw [Real.volume_real_Icc_of_le hs, indicator_of_mem (show s ∈ Ici (0:ℝ) from hs)]
      simp
    · have : Icc (0:ℝ) s = ∅ := by
        ext x; simp only [mem_Icc, mem_empty_iff_false, iff_false]
        intro hx; exact hs (le_trans hx.1 hx.2)
      rw [this, indicator_of_notMem (show s ∉ Ici (0:ℝ) from hs)]
      simp
  symm
  calc ∫ u in Ici 0, S f u = ∫ u, (Ici 0).indicator (S f) u := (integral_indicator measurableSet_Ici).symm
   _ = ∫ u, ∫ s, H (u,s) := by simp_rw [h1]
   _ = ∫ s, ∫ u, H (u,s) := integral_integral_swap hHint
   _ = ∫ s, (Ici 0).indicator (fun s => s * f s) s := by simp_rw [h2]
   _ = ∫ s in Ici 0, s * f s := integral_indicator measurableSet_Ici

end generic

lemma gronwall (y : ℝ → ℝ) (hy : Continuous y) (a p : ℝ) (ha : 0 ≤ a)
    (h : ∀ τ, 0 ≤ τ → y τ ≤ p + a * ∫ u in (0:ℝ)..τ, y u) :
    ∀ τ, 0 ≤ τ → y τ ≤ p * Real.exp (a * τ) := by
  set Z : ℝ → ℝ := fun τ => ∫ u in (0:ℝ)..τ, y u with hZ
  have hZd : ∀ τ, HasDerivAt Z (y τ) τ := fun τ => (hy.integral_hasStrictDerivAt 0 τ).hasDerivAt
  set Φ : ℝ → ℝ := fun τ => Real.exp (-(a*τ)) * (p + a * Z τ) with hΦ
  have hΦd : ∀ τ, HasDerivAt Φ
      (Real.exp (-(a*τ)) * (a * y τ - a * (p + a * Z τ))) τ := by
    intro τ
    have h1 : HasDerivAt (fun τ => Real.exp (-(a*τ))) (Real.exp (-(a*τ)) * (-a)) τ := by
      have := ((hasDerivAt_id τ).const_mul a).neg.exp
      simpa using this
    have h2 : HasDerivAt (fun τ => p + a * Z τ) (a * y τ) τ := by
      simpa using ((hZd τ).const_mul a).const_add p
    exact (h1.mul h2).congr_deriv (by ring)
  have hanti : AntitoneOn Φ (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact (continuous_iff_continuousAt.2 (fun τ => (hΦd τ).continuousAt)).continuousOn
    · exact fun τ _ => (hΦd τ).differentiableAt.differentiableWithinAt
    · intro τ hτ
      rw [(hΦd τ).deriv]
      have hτ' : 0 ≤ τ := le_of_lt (by simpa using hτ)
      have h6 := h τ hτ'
      have : a * y τ - a * (p + a * Z τ) ≤ 0 := by
        have := mul_le_mul_of_nonneg_left h6 ha
        linarith
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le this
  intro τ hτ
  have h0 : Φ τ ≤ Φ 0 :=
    hanti (show (0:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.2 (le_refl _)) (show τ ∈ Set.Ici 0 from hτ) hτ
  have hΦ0 : Φ 0 = p := by simp [hΦ, hZ]
  have h3 : p + a * Z τ ≤ p * Real.exp (a * τ) := by
    have h4 : Real.exp (-(a*τ)) * (p + a * Z τ) ≤ p := by simpa [hΦ0] using h0
    have h5 : (p + a * Z τ) = Real.exp (a*τ) * (Real.exp (-(a*τ)) * (p + a * Z τ)) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [h5]
    calc Real.exp (a*τ) * (Real.exp (-(a*τ)) * (p + a * Z τ)) ≤ Real.exp (a*τ) * p :=
          mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
      _ = p * Real.exp (a * τ) := mul_comm _ _
  exact (h τ hτ).trans h3


section main
variable {g : ℝ → ℝ}

lemma pair_ineq (h0 : ∀ t, 0 ≤ g t)
    (hlc : ∀ s t a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → g s ^ a * g t ^ b ≤ g (a * s + b * t))
    {t t' s : ℝ} (h1 : t < t') (h2 : t' ≤ s) :
    g t * g s ≤ g t' * g (s - (t' - t)) := by
  have hs : 0 < s - t := by linarith
  set b := (t' - t) / (s - t) with hb
  have hb0 : 0 ≤ b := div_nonneg (by linarith) hs.le
  have hb1 : b ≤ 1 := (div_le_one hs).2 (by linarith)
  set a := 1 - b with ha
  have ha0 : 0 ≤ a := by linarith
  have hab : a + b = 1 := by ring
  have hbs : b * (s - t) = t' - t := by rw [hb]; field_simp
  have e1 : a * t + b * s = t' := by
    simp only [ha]; linear_combination hbs
  have e2 : b * t + a * s = s - (t' - t) := by
    simp only [ha]; linear_combination (-1) * hbs
  have k1 := hlc t s a b ha0 hb0 hab
  have k2 := hlc t s b a hb0 ha0 (by linarith)
  rw [e1] at k1
  rw [e2] at k2
  have r1 : g t ^ a * g t ^ b = g t := by
    rw [← Real.rpow_add' (h0 t) (by rw [hab]; norm_num), hab, Real.rpow_one]
  have r2 : g s ^ b * g s ^ a = g s := by
    rw [← Real.rpow_add' (h0 s) (by rw [add_comm, hab]; norm_num), add_comm, hab, Real.rpow_one]
  have : g t * g s = (g t ^ a * g s ^ b) * (g t ^ b * g s ^ a) := by
    calc g t * g s = (g t ^ a * g t ^ b) * (g s ^ b * g s ^ a) := by rw [r1, r2]
      _ = _ := by ring
  rw [this]
  exact mul_le_mul k1 k2 (mul_nonneg (Real.rpow_nonneg (h0 _) _) (Real.rpow_nonneg (h0 _) _)) (h0 _)

lemma S_shift (f : ℝ → ℝ) (t r : ℝ) :
    ∫ s in Ici (t + r), f (s - r) = ∫ s in Ici t, f s := by
  have := (measurePreserving_sub_right volume r).setIntegral_preimage_emb
    (measurableEmbedding_subRight r) f (Ici t)
  have e : (fun x : ℝ => x - r) ⁻¹' Ici t = Ici (t + r) := by
    ext x; simp [le_sub_iff_add_le]
  rw [e] at this
  exact this

lemma hazard (h0 : ∀ t, 0 ≤ g t)
    (hlc : ∀ s t a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → g s ^ a * g t ^ b ≤ g (a * s + b * t))
    (hint : Integrable g) {t t' : ℝ} (h : t < t') :
    g t * S g t' ≤ g t' * S g t := by
  unfold S
  have e : t' = t + (t' - t) := by ring
  calc g t * ∫ s in Ici t', g s = ∫ s in Ici t', g t * g s := by rw [integral_const_mul]
    _ ≤ ∫ s in Ici t', g t' * g (s - (t' - t)) := by
        apply setIntegral_mono_on (hint.integrableOn.const_mul _)
          (((hint.comp_sub_right (t' - t)).integrableOn).const_mul _) measurableSet_Ici
        intro s hs
        exact pair_ineq h0 hlc h hs
    _ = g t' * ∫ s in Ici t', g (s - (t' - t)) := by rw [integral_const_mul]
    _ = g t' * ∫ s in Ici t, g s := by
        rw [← S_shift g t (t' - t), ← e]


lemma integrable_mul_self (hmeas : Measurable g) (h0 : ∀ t, 0 ≤ g t) (hint : Integrable g)
    {R : ℝ} (hR : ∀ t, R < |t| → g t = 0) :
    Integrable (fun t => t * g t) := by
  refine (hint.const_mul R).mono' (measurable_id.mul hmeas).aestronglyMeasurable
    (Filter.Eventually.of_forall ?_)
  intro t
  rcases le_or_gt |t| R with h | h
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (h0 t)]
    exact mul_le_mul_of_nonneg_right h (h0 t)
  · simp [hR t h]

lemma Sneg_ge (h0 : ∀ t, 0 ≤ g t) (hint : Integrable g) (u : ℝ) :
    (∫ t, g t) - S g (-u) ≤ S (fun t => g (-t)) u := by
  have hintN : Integrable (fun t => g (-t)) := hint.comp_neg
  have h1 := integral_add_compl (measurableSet_Ici (a := u)) hintN
  rw [compl_Ici, integral_neg_eq_self (fun t => g t) volume] at h1
  have h2 : ∫ t in Iio u, g (-t) ≤ ∫ t in Iic u, g (-t) :=
    setIntegral_mono_set hintN.integrableOn (Filter.Eventually.of_forall (fun t => h0 _))
      (Iio_subset_Iic_self.eventuallyLE)
  rw [integral_comp_neg_Iic u g, ← integral_Ici_eq_integral_Ioi] at h2
  unfold S
  linarith

/-- Positivity of the right mass. -/
lemma right_mass_pos (hmeas : Measurable g) (h0 : ∀ t, 0 ≤ g t) (hint : Integrable g)
    {R : ℝ} (hR : ∀ t, R < |t| → g t = 0) (hpos : 0 < ∫ t, g t)
    (hmean : ∫ t, t * g t = 0) : 0 < ∫ t in Ici 0, g t := by
  have hp0 : 0 ≤ ∫ t in Ici 0, g t := setIntegral_nonneg measurableSet_Ici (fun x _ => h0 x)
  rcases hp0.lt_or_eq with h | h
  · exact h
  exfalso
  have hintN : Integrable (fun t => g (-t)) := hint.comp_neg
  have hRN : ∀ t, R < |t| → g (-t) = 0 := fun t ht => hR _ (by rwa [abs_neg])
  have hk := integrable_mul_self hmeas h0 hint hR
  have hkN := integrable_mul_self (hmeas.comp measurable_neg) (fun t => h0 _) hintN hRN
  -- g = 0 a.e. on Ici 0
  have hae : g =ᵐ[volume.restrict (Ici 0)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall (fun t => h0 t))
      hint.integrableOn).1 h.symm
  have hm1 : ∫ t in Ici 0, t * g t = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with t ht
    simp [ht]
  -- decomposition of the mean
  have hdec := integral_add_compl (measurableSet_Ici (a := (0:ℝ))) hk
  rw [compl_Ici, hmean, hm1, zero_add] at hdec
  have hneg : ∫ t in Iio 0, t * g t = - ∫ t in Ioi 0, t * g (-t) := by
    have := integral_comp_neg_Ioi (0:ℝ) (fun x => x * g x)
    simp only [neg_zero, neg_mul] at this
    rw [integral_neg] at this
    rw [← integral_Iic_eq_integral_Iio, ← this]
  have hm2 : ∫ t in Ioi 0, t * g (-t) = 0 := by linarith
  have hae2 : (fun t => t * g (-t)) =ᵐ[volume.restrict (Ioi 0)] 0 := by
    refine (setIntegral_eq_zero_iff_of_nonneg_ae ?_ hkN.integrableOn).1 hm2
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall ?_)
    intro t ht
    exact mul_nonneg (le_of_lt ht) (h0 _)
  have hg2 : (fun t => g (-t)) =ᵐ[volume.restrict (Ioi 0)] 0 := by
    filter_upwards [hae2, ae_restrict_mem measurableSet_Ioi] with t ht ht0
    have : t * g (-t) = 0 := ht
    rcases mul_eq_zero.1 this with h1 | h1
    · exact absurd h1 (ne_of_gt ht0)
    · simpa using h1
  have hI1 : ∫ t in Ioi 0, g (-t) = 0 := integral_eq_zero_of_ae hg2
  -- total mass
  have hM := integral_add_compl (measurableSet_Ici (a := (0:ℝ))) hintN
  rw [compl_Ici, integral_neg_eq_self (fun t => g t) volume] at hM
  rw [integral_Ici_eq_integral_Ioi, hI1] at hM
  have h3 : ∫ t in Iio 0, g (-t) = ∫ t in Ioi 0, g t := by
    have := integral_comp_neg_Iic (0:ℝ) g
    rw [neg_zero, integral_Iic_eq_integral_Iio] at this
    exact this
  rw [h3, ← integral_Ici_eq_integral_Ioi, ← h] at hM
  linarith

lemma mean_balance (hmeas : Measurable g) (h0 : ∀ t, 0 ≤ g t) (hint : Integrable g)
    {R : ℝ} (hR : ∀ t, R < |t| → g t = 0) (hmean : ∫ t, t * g t = 0) :
    ∫ t in Ici 0, t * g t = ∫ t in Ici 0, t * g (-t) := by
  have hk := integrable_mul_self hmeas h0 hint hR
  have hdec := integral_add_compl (measurableSet_Ici (a := (0:ℝ))) hk
  rw [compl_Ici, hmean] at hdec
  have hneg : ∫ t in Iio 0, t * g t = - ∫ t in Ioi 0, t * g (-t) := by
    have := integral_comp_neg_Ioi (0:ℝ) (fun x => x * g x)
    simp only [neg_zero, neg_mul] at this
    rw [integral_neg] at this
    rw [← integral_Iic_eq_integral_Iio, ← this]
  have h5 : ∫ t in Ici 0, t * g (-t) = ∫ t in Ioi 0, t * g (-t) := integral_Ici_eq_integral_Ioi
  linarith

lemma gron_apply (h0 : ∀ t, 0 ≤ g t)
    (hlc : ∀ s t a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → g s ^ a * g t ^ b ≤ g (a * s + b * t))
    (hint : Integrable g) {R : ℝ} (hR : ∀ t, R < |t| → g t = 0)
    (hp : 0 < S g 0) (a : ℝ) (ha : a = g 0 / S g 0) (ha0 : 0 ≤ a) :
    ∀ u, 0 ≤ u → S g (-u) ≤ S g 0 * Real.exp (a * u) := by
  have hleft : ∀ s, s ≤ 0 → g s ≤ a * S g s := by
    intro s hs
    rcases hs.lt_or_eq with hs | hs
    · have := hazard h0 hlc hint hs
      rw [ha, div_mul_eq_mul_div, le_div_iff₀ hp]
      linarith
    · subst hs
      rw [ha, div_mul_cancel₀ _ hp.ne']
  have hSc : Continuous (S g) := S_cont hint hR
  apply gronwall (fun u => S g (-u)) (hSc.comp continuous_neg) a (S g 0) ha0
  intro τ hτ
  have e1 : S g (-τ) = S g 0 + ∫ s in (-τ)..0, g s := by
    rw [S_eq_interval hR, S_eq_interval hR, ← intervalIntegral.integral_add_adjacent_intervals
      (hint.intervalIntegrable (a := -τ) (b := 0)) (hint.intervalIntegrable (a := 0) (b := R))]
    ring
  have e2 : ∫ s in (-τ)..0, g s ≤ ∫ s in (-τ)..0, a * S g s :=
    intervalIntegral.integral_mono_on (by linarith) hint.intervalIntegrable
      ((hSc.const_smul a).intervalIntegrable _ _) (fun s hs => hleft s hs.2)
  have e3 : ∫ s in (-τ)..0, a * S g s = a * ∫ u in (0:ℝ)..τ, S g (-u) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_neg (fun x => S g x)]
    simp
  show S g (-τ) ≤ S g 0 + a * ∫ u in (0:ℝ)..τ, S g (-u)
  linarith

lemma main_core (hmeas : Measurable g) (h0 : ∀ t, 0 ≤ g t)
    (hlc : ∀ s t a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → g s ^ a * g t ^ b ≤ g (a * s + b * t))
    (hint : Integrable g) {R : ℝ} (hR0 : 0 ≤ R) (hR : ∀ t, R < |t| → g t = 0)
    (hpos : 0 < ∫ t, g t) (hmean : ∫ t, t * g t = 0) :
    Real.exp (-1) * ∫ t, g t ≤ ∫ t in Ici 0, g t := by
  have hp : 0 < S g 0 := right_mass_pos hmeas h0 hint hR hpos hmean
  have hpI : ∫ t in Ici 0, g t = S g 0 := rfl
  rw [hpI]
  have hMnn : 0 ≤ ∫ t, g t := hpos.le
  by_cases hg0 : g 0 = 0
  · have hleft : ∀ s < 0, g s = 0 := by
      intro s hs
      have := hazard h0 hlc hint hs
      rw [hg0, zero_mul] at this
      by_contra hne
      have : 0 < g s := lt_of_le_of_ne (h0 s) (Ne.symm hne)
      nlinarith
    have hMp : ∫ t, g t = S g 0 := by
      have := integral_add_compl (measurableSet_Ici (a := (0:ℝ))) hint
      have hz : ∫ x in Iio (0:ℝ), g x = 0 :=
        setIntegral_eq_zero_of_forall_eq_zero (fun x hx => hleft x hx)
      rw [compl_Ici, hz, add_zero] at this
      exact this.symm
    rw [hMp]
    have : Real.exp (-1) ≤ 1 := by
      rw [Real.exp_le_one_iff]; norm_num
    nlinarith
  · have hg0' : 0 < g 0 := lt_of_le_of_ne (h0 0) (Ne.symm hg0)
    set M := ∫ t, g t with hM
    set p := S g 0 with hpdef
    set a := g 0 / p with ha
    have ha0 : 0 < a := div_pos hg0' hp
    have hintN : Integrable (fun t => g (-t)) := hint.comp_neg
    have hRN : ∀ t, R < |t| → g (-t) = 0 := fun t ht => hR _ (by rwa [abs_neg])
    have hSc : Continuous (S g) := S_cont hint hR
    have hright : ∀ s, 0 ≤ s → a * S g s ≤ g s := by
      intro s hs
      rcases hs.lt_or_eq with hs | hs
      · have := hazard h0 hlc hint hs
        rw [ha, div_mul_eq_mul_div, div_le_iff₀ hp]
        linarith
      · subst hs
        rw [ha, div_mul_cancel₀ _ hp.ne']
    -- (A)
    have hA : a * ∫ u in Ici 0, S g u ≤ p := by
      rw [← integral_const_mul]
      exact setIntegral_mono_on ((S_integrableOn hint hR hR0).const_mul a) hint.integrableOn
        measurableSet_Ici (fun s hs => hright s hs)
    -- (B)
    have hB := gron_apply h0 hlc hint hR hp a ha ha0.le
    -- layer cake and balance
    have hLC1 := layer_cake hmeas h0 hint hR
    have hLC2 : ∫ t in Ici 0, t * g (-t) = ∫ u in Ici 0, S (fun t => g (-t)) u :=
      layer_cake (hmeas.comp measurable_neg) (fun t => h0 _) hintN hRN
    have hbal := mean_balance hmeas h0 hint hR hmean
    have hSN_int := S_integrableOn hintN hRN hR0
    have hSN_c : Continuous (S (fun t => g (-t))) := S_cont hintN hRN
    have heq : ∫ u in Ici 0, S g u = ∫ u in Ici 0, S (fun t => g (-t)) u := by
      rw [← hLC1, ← hLC2, hbal]
    -- (D)
    have hU : (0:ℝ) ≤ 1 / a := by positivity
    have hD1 : ∫ u in (0:ℝ)..(1 / a), (M - p * Real.exp (a * u)) = (M - p * (Real.exp 1 - 1)) / a := by
      rw [intervalIntegral.integral_sub (by simp) ((by fun_prop : Continuous fun u : ℝ => p * Real.exp (a * u)).intervalIntegrable _ _)]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) ha0.ne']
      simp only [intervalIntegral.integral_const, smul_eq_mul, mul_zero, integral_exp, Real.exp_zero]
      field_simp
      ring_nf
    have hD2 : ∫ u in Icc (0:ℝ) (1 / a), (M - p * Real.exp (a * u)) ≤
        ∫ u in Icc (0:ℝ) (1 / a), S (fun t => g (-t)) u := by
      apply setIntegral_mono_on
      · exact (by fun_prop : Continuous fun u : ℝ => M - p * Real.exp (a * u)).continuousOn.integrableOn_Icc
      · exact hSN_int.mono_set Icc_subset_Ici_self
      · exact measurableSet_Icc
      · intro u hu
        have := Sneg_ge h0 hint u
        have := hB u hu.1
        linarith
    have hD3 : ∫ u in Icc (0:ℝ) (1 / a), S (fun t => g (-t)) u ≤ ∫ u in Ici 0, S (fun t => g (-t)) u :=
      setIntegral_mono_set hSN_int
        (Filter.Eventually.of_forall (fun u => S_nonneg (fun t => h0 _) u))
        (Icc_subset_Ici_self.eventuallyLE)
    have hD4 : ∫ u in Icc (0:ℝ) (1 / a), (M - p * Real.exp (a * u)) = (M - p * (Real.exp 1 - 1)) / a := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hU, hD1]
    -- combine
    have hfin : (M - p * (Real.exp 1 - 1)) / a ≤ ∫ u in Ici 0, S g u := by
      rw [heq, ← hD4]; exact hD2.trans hD3
    have hfin2 : M - p * (Real.exp 1 - 1) ≤ a * ∫ u in Ici 0, S g u := by
      have := mul_le_mul_of_nonneg_left hfin ha0.le
      rwa [mul_div_cancel₀ _ ha0.ne'] at this
    have hMle : M ≤ Real.exp 1 * p := by linarith
    have hexp : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (-1) * M ≤ Real.exp (-1) * (Real.exp 1 * p) :=
          mul_le_mul_of_nonneg_left hMle (Real.exp_pos _).le
      _ = p := by rw [← mul_assoc, hexp, one_mul]

end main

theorem oneD_centered_aux (g : ℝ → ℝ) (hmeas : Measurable g) (h0 : ∀ t, 0 ≤ g t)
    (hlc : ∀ s t a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → g s ^ a * g t ^ b ≤ g (a * s + b * t))
    (hint : Integrable g) (hsupp : ∃ R : ℝ, ∀ t, R < |t| → g t = 0)
    (hpos : 0 < ∫ t, g t) (hmean : ∫ t, t * g t = 0) :
    Real.exp (-1) * ∫ t, g t ≤ ∫ t in Set.Ici 0, g t := by
  obtain ⟨R, hR⟩ := hsupp
  exact main_core hmeas h0 hlc hint (abs_nonneg R)
    (fun t ht => hR t (lt_of_le_of_lt (le_abs_self R) ht)) hpos hmean

end GrunbaumAux1

open MeasureTheory

namespace GrunbaumSpec

theorem oneD_centered (g : ℝ → ℝ) (hmeas : Measurable g) (h0 : ∀ t, 0 ≤ g t)
    (hlc : ∀ s t a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → g s ^ a * g t ^ b ≤ g (a * s + b * t))
    (hint : Integrable g) (hsupp : ∃ R : ℝ, ∀ t, R < |t| → g t = 0)
    (hpos : 0 < ∫ t, g t) (hmean : ∫ t, t * g t = 0) :
    Real.exp (-1) * ∫ t, g t ≤ ∫ t in Set.Ici 0, g t :=
  GrunbaumAux1.oneD_centered_aux g hmeas h0 hlc hint hsupp hpos hmean

end GrunbaumSpec

end PieceA

section PieceB

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GrunbaumAuxB

open ConvexOptAlg.CenterGravity

noncomputable def e1 : ℝ ≃ᵐ EuclideanSpace ℝ (Fin 1) :=
  (MeasurableEquiv.funUnique (Fin 1) ℝ).symm.trans (MeasurableEquiv.toLp 2 (Fin 1 → ℝ))

theorem e1_apply (t : ℝ) (i : Fin 1) : e1 t i = t := rfl

theorem e1_symm_apply (x : EuclideanSpace ℝ (Fin 1)) : e1.symm x = x 0 := rfl

theorem e1_affine (a b s t : ℝ) : e1 (a * s + b * t) = a • e1 s + b • e1 t := by
  ext i
  simp [e1_apply]

noncomputable def Φ0 (m : ℕ) : EuclideanSpace ℝ (Fin (m+1)) ≃ᵐ ℝ × EuclideanSpace ℝ (Fin m) :=
  (MeasurableEquiv.toLp 2 (Fin (m+1) → ℝ)).symm.trans
   ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.toLp 2 (Fin m → ℝ))))

theorem Φ0_mp (m : ℕ) : MeasurePreserving (Φ0 m) volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (m+1))).trans
   ((volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).trans
    (MeasurePreserving.prod (MeasurePreserving.id _)
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)).symm))

theorem Φ0_symm_zero {m : ℕ} (t : ℝ) (y : EuclideanSpace ℝ (Fin m)) : (Φ0 m).symm (t, y) 0 = t := by
  rfl

theorem Φ0_symm_succ {m : ℕ} (t : ℝ) (y : EuclideanSpace ℝ (Fin m)) (j : Fin m) :
    (Φ0 m).symm (t, y) j.succ = y j := by
  rfl

theorem Φ0_symm_affine {m : ℕ} (a b : ℝ) (p q : ℝ × EuclideanSpace ℝ (Fin m)) :
    (Φ0 m).symm (a • p + b • q) = a • (Φ0 m).symm p + b • (Φ0 m).symm q := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [show a • p + b • q = ((a • p + b • q).1, (a • p + b • q).2) from rfl, Φ0_symm_zero]
    simp [show ∀ r : ℝ × EuclideanSpace ℝ (Fin m), (Φ0 m).symm r 0 = r.1 from
      fun r => Φ0_symm_zero r.1 r.2]
  · rw [show a • p + b • q = ((a • p + b • q).1, (a • p + b • q).2) from rfl, Φ0_symm_succ]
    simp [show ∀ r : ℝ × EuclideanSpace ℝ (Fin m), (Φ0 m).symm r j.succ = r.2 j from
      fun r => Φ0_symm_succ r.1 r.2 j]


theorem indicator_logConcave {E : Type*} [AddCommGroup E] [Module ℝ E] (S : Set E)
    (hS : Convex ℝ S) :
    ConvexOptimization.LogConcaveOn Set.univ (S.indicator (fun _ => (1 : ℝ))) := by
  refine ⟨fun x _ => Set.indicator_nonneg (fun _ _ => zero_le_one) x, ?_⟩
  intro x _ y _ a b ha hb hab
  by_cases hxy : x ∈ S ∧ y ∈ S
  · have : a • x + b • y ∈ S := hS hxy.1 hxy.2 ha hb hab
    simp [Set.indicator_of_mem, hxy.1, hxy.2, this]
  · rcases ha.eq_or_lt with rfl | ha'
    · have hb1 : b = 1 := by linarith
      subst hb1
      simp
    rcases hb.eq_or_lt with rfl | hb'
    · have ha1 : a = 1 := by linarith
      subst ha1
      simp
    · have h0 : S.indicator (fun _ => (1 : ℝ)) x = 0 ∨ S.indicator (fun _ => (1 : ℝ)) y = 0 := by
        by_cases hx : x ∈ S
        · right
          exact Set.indicator_of_notMem (fun hy => hxy ⟨hx, hy⟩) _
        · left
          exact Set.indicator_of_notMem hx _
      have hnn : 0 ≤ S.indicator (fun _ => (1 : ℝ)) (a • x + b • y) :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
      rcases h0 with h | h
      · rw [h, Real.zero_rpow ha'.ne']
        simpa using hnn
      · rw [h, Real.zero_rpow hb'.ne']
        simpa using hnn

variable {m : ℕ}

noncomputable def F (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) :
    ℝ × EuclideanSpace ℝ (Fin m) → ℝ :=
  fun p => K.indicator (fun _ => (1 : ℝ)) ((Φ0 m).symm p)

noncomputable def g0 (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) (t : ℝ) : ℝ :=
  ∫ y, F K (t, y)

theorem F_nonneg (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) (p) : 0 ≤ F K p :=
  Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem F_measurable {K : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hK : MeasurableSet K) :
    Measurable (F K) :=
  (Measurable.indicator measurable_const hK).comp (Φ0 m).symm.measurable

theorem norm_sq_symm (t : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    ‖(Φ0 m).symm (t, y)‖ ^ 2 = t ^ 2 + ‖y‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, Fin.sum_univ_succ]
  simp only [Φ0_symm_zero, Φ0_symm_succ, Real.norm_eq_abs, sq_abs]

theorem F_section_integrable {K : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hK : IsCompact K)
    (s : ℝ) : Integrable (fun y => F K (s, y)) := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1)))
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hmeas : Measurable (fun y => F K (s, y)) :=
    (F_measurable hKm).comp (measurable_const.prodMk measurable_id)
  have hint : Integrable ((Metric.closedBall (0 : EuclideanSpace ℝ (Fin m)) R).indicator
      (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).2
      (integrableOn_const (measure_closedBall_lt_top.ne))
  refine hint.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : (Φ0 m).symm (s, y) ∈ K
  · have h1 : F K (s, y) = 1 := by simp [F, Set.indicator_of_mem, hy]
    have hb := hR hy
    rw [mem_closedBall_zero_iff] at hb
    have : ‖y‖ ≤ R := by
      have h2 := norm_sq_symm s y
      have : ‖y‖ ^ 2 ≤ R ^ 2 := by
        have := pow_le_pow_left₀ (norm_nonneg _) hb 2
        nlinarith [sq_nonneg s]
      exact abs_le_of_sq_le_sq' this (le_trans (norm_nonneg _) hb) |>.2
    rw [h1, Set.indicator_of_mem (by simpa using this)]
    simp
  · have h1 : F K (s, y) = 0 := by simp [F, Set.indicator_of_notMem, hy]
    rw [h1]
    simpa using Set.indicator_nonneg (fun _ _ => zero_le_one) y


noncomputable def Fp (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) :
    EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin m) → ℝ :=
  fun p => F K (e1.symm p.1, p.2)

theorem Fp_measurable {K : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hK : MeasurableSet K) :
    Measurable (Fp K) :=
  (F_measurable hK).comp ((e1.symm.measurable.comp measurable_fst).prodMk measurable_snd)

theorem Fp_eq_indicator (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) :
    Fp K = Set.indicator {p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin m) |
      (Φ0 m).symm (e1.symm p.1, p.2) ∈ K} (fun _ => (1 : ℝ)) := by
  funext p
  simp [Fp, F, Set.indicator]

theorem Fp_convex {K : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hK : Convex ℝ K) :
    Convex ℝ {p : EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin m) |
      (Φ0 m).symm (e1.symm p.1, p.2) ∈ K} := by
  intro p hp q hq a b ha hb hab
  have hp' : (Φ0 m).symm (e1.symm p.1, p.2) ∈ K := hp
  have hq' : (Φ0 m).symm (e1.symm q.1, q.2) ∈ K := hq
  show (Φ0 m).symm (e1.symm (a • p + b • q).1, (a • p + b • q).2) ∈ K
  have : (e1.symm (a • p + b • q).1, (a • p + b • q).2)
      = a • (e1.symm p.1, p.2) + b • (e1.symm q.1, q.2) := by
    ext
    · simp [e1_symm_apply]
    · simp
  rw [this, Φ0_symm_affine]
  exact hK hp' hq' ha hb hab

theorem Fp_logConcave {K : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hK : Convex ℝ K) :
    ConvexOptimization.LogConcaveOn Set.univ (Fp K) := by
  rw [Fp_eq_indicator]
  exact indicator_logConcave _ (Fp_convex hK)

theorem g0_eq (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) (t : ℝ) :
    g0 K t = ∫ y, Fp K (e1 t, y) := by
  simp [g0, Fp]

theorem g0_logConcave {K : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hK : IsConvexBody K) :
    ∀ s t a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → g0 K s ^ a * g0 K t ^ b ≤ g0 K (a * s + b * t) := by
  obtain ⟨hKc, hKconv, -⟩ := hK
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have key := ConvexOptimization.prekopa_marginal_log_concave (Fp K) (Fp_measurable hKm)
    (Fp_logConcave hKconv) (fun x => F_section_integrable hKc (e1.symm x))
  intro s t a b ha hb hab
  have := key.2 (e1 s) (Set.mem_univ _) (e1 t) (Set.mem_univ _) a b ha hb hab
  rw [g0_eq, g0_eq, g0_eq, e1_affine]
  exact this


theorem g0_fubini {K : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hK : IsCompact K)
    (w : ℝ → ℝ) (hw : Measurable w) (C : ℝ) (hC : ∀ x ∈ K, |w (x 0)| ≤ C) :
    Integrable (fun t => w t * g0 K t) ∧ ∫ t, w t * g0 K t = ∫ x in K, w (x 0) := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  set f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ := K.indicator (fun x => w (x 0)) with hf
  have hfint : Integrable f := by
    rw [hf, integrable_indicator_iff hKm]
    refine Measure.integrableOn_of_bounded (M := C) hK.measure_lt_top.ne
      (hw.comp (EuclideanSpace.proj (0 : Fin (m + 1))).continuous.measurable).aestronglyMeasurable
      ((ae_restrict_iff' hKm).2 (Filter.Eventually.of_forall fun x hx => by
        simpa using hC x hx))
  have hcomp : (fun p => f ((Φ0 m).symm p)) = fun p => w p.1 * F K p := by
    funext p
    simp only [hf, F, Set.indicator]
    split_ifs
    · rw [show p = (p.1, p.2) from rfl, Φ0_symm_zero]; simp
    · simp
  have hmp := (Φ0_mp m).symm
  have hfint' : Integrable (fun p => w p.1 * F K p) := by
    rw [← hcomp]
    exact (hmp.integrable_comp_emb (Φ0 m).symm.measurableEmbedding).2 hfint
  have hint_eq : ∫ p, w p.1 * F K p = ∫ x in K, w (x 0) := by
    rw [← hcomp, hmp.integral_comp' f, ← integral_indicator hKm]
  have hfint2 : Integrable (fun p => w p.1 * F K p) (volume.prod volume) := by
    rwa [← Measure.volume_eq_prod]
  have hfub : ∫ p, w p.1 * F K p = ∫ t, ∫ y, w t * F K (t, y) := by
    rw [Measure.volume_eq_prod, integral_prod _ hfint2]
  have hinner : (fun t => ∫ y, w t * F K (t, y)) = fun t => w t * g0 K t := by
    funext t
    rw [integral_const_mul]
    rfl
  refine ⟨?_, ?_⟩
  · rw [← hinner]
    have := hfint2.integral_prod_left
    simpa using this
  · rw [← hint_eq, hfub, hinner]


theorem g0_nonneg (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) (t : ℝ) : 0 ≤ g0 K t :=
  integral_nonneg (fun y => F_nonneg K (t, y))

theorem g0_measurable {K : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hK : MeasurableSet K) :
    Measurable (g0 K) :=
  ((F_measurable hK).stronglyMeasurable.integral_prod_right').measurable

theorem g0_support {K : Set (EuclideanSpace ℝ (Fin (m + 1)))} (hK : IsCompact K) :
    ∃ R : ℝ, ∀ t, R < |t| → g0 K t = 0 := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1)))
  refine ⟨R, fun t ht => ?_⟩
  have : ∀ y, F K (t, y) = 0 := by
    intro y
    have hy : (Φ0 m).symm (t, y) ∉ K := by
      intro hmem
      have h1 := hR hmem
      rw [mem_closedBall_zero_iff] at h1
      have h2 : |(Φ0 m).symm (t, y) 0| ≤ ‖(Φ0 m).symm (t, y)‖ := by
        simpa using PiLp.norm_apply_le ((Φ0 m).symm (t, y)) 0
      rw [Φ0_symm_zero] at h2
      linarith
    simp [F, Set.indicator_of_notMem, hy]
  simp [g0, this]

end GrunbaumAuxB

namespace GrunbaumSpec
open ConvexOptAlg.CenterGravity

theorem slice_profile {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) (hK : IsConvexBody K) :
    ∃ g : ℝ → ℝ, Measurable g ∧ (∀ t, 0 ≤ g t) ∧
      (∀ s t a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → g s ^ a * g t ^ b ≤ g (a * s + b * t)) ∧
      Integrable g ∧ (∃ R : ℝ, ∀ t, R < |t| → g t = 0) ∧
      ∫ t, g t = (volume K).toReal ∧
      ∫ t in Set.Ici 0, g t = (volume (K ∩ {x | 0 ≤ x 0})).toReal ∧
      ∫ t, t * g t = ∫ x in K, x 0 := by
  have hKc : IsCompact K := hK.1
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin (m + 1)))
  have h1 := GrunbaumAuxB.g0_fubini hKc (fun _ => 1) measurable_const 1 (fun x _ => by simp)
  have h2 := GrunbaumAuxB.g0_fubini hKc (Set.indicator (Set.Ici 0) (fun _ => (1 : ℝ)))
    (measurable_const.indicator measurableSet_Ici) 1 (fun x _ => by
      by_cases h : 0 ≤ x 0 <;> simp [Set.indicator, h])
  have h3 := GrunbaumAuxB.g0_fubini hKc (fun t => t) measurable_id R (fun x hx => by
    have h1 := hR hx
    rw [mem_closedBall_zero_iff] at h1
    have h2 : |x 0| ≤ ‖x‖ := by simpa using PiLp.norm_apply_le x 0
    exact h2.trans h1)
  refine ⟨GrunbaumAuxB.g0 K, GrunbaumAuxB.g0_measurable hKm, GrunbaumAuxB.g0_nonneg K,
    GrunbaumAuxB.g0_logConcave hK, by simpa using h1.1, GrunbaumAuxB.g0_support hKc, ?_, ?_, ?_⟩
  · simpa [Measure.real] using h1.2
  · have hl : ∀ t, Set.indicator (Set.Ici (0 : ℝ)) (fun _ => (1 : ℝ)) t * GrunbaumAuxB.g0 K t
        = Set.indicator (Set.Ici (0 : ℝ)) (GrunbaumAuxB.g0 K) t := by
      intro t
      by_cases h : 0 ≤ t <;> simp [Set.indicator, h]
    have hr : ∀ x : EuclideanSpace ℝ (Fin (m + 1)),
        Set.indicator (Set.Ici (0 : ℝ)) (fun _ => (1 : ℝ)) (x 0)
        = Set.indicator {x : EuclideanSpace ℝ (Fin (m + 1)) | 0 ≤ x 0} (fun _ => (1 : ℝ)) x := by
      intro x
      by_cases h : 0 ≤ x 0 <;> simp [Set.indicator, h]
    have hset : MeasurableSet {x : EuclideanSpace ℝ (Fin (m + 1)) | 0 ≤ x 0} :=
      measurableSet_le measurable_const (EuclideanSpace.proj (0 : Fin (m + 1))).continuous.measurable
    have := h2.2
    simp only [hl, hr] at this
    rw [integral_indicator measurableSet_Ici] at this
    rw [this, setIntegral_indicator hset]
    simp [Measure.real]
  · exact h3.2

end GrunbaumSpec
end PieceB

section PieceC

open MeasureTheory
open scoped InnerProductSpace ENNReal

namespace GrunbaumAuxC
open ConvexOptAlg.CenterGravity

/-- A linear isometry equivalence sending `w` to `‖w‖ • e₀`. -/
theorem exists_rot {m : ℕ} (w : EuclideanSpace ℝ (Fin (m + 1))) :
    ∃ R : EuclideanSpace ℝ (Fin (m + 1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m + 1)),
      R w = ‖w‖ • EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ) := by
  refine ⟨Submodule.reflection (ℝ ∙ (w - ‖w‖ • EuclideanSpace.single (0 : Fin (m + 1)) (1 : ℝ)))ᗮ, ?_⟩
  apply Submodule.reflection_sub
  simp [norm_smul]

end GrunbaumAuxC

namespace GrunbaumSpec
open ConvexOptAlg.CenterGravity

theorem rotate_to_axis {m : ℕ} (K : Set (EuclideanSpace ℝ (Fin (m + 1)))) (hK : IsConvexBody K)
    (hc : ∫ x in K, x = 0) (w : EuclideanSpace ℝ (Fin (m + 1))) (hw : w ≠ 0) :
    ∃ K' : Set (EuclideanSpace ℝ (Fin (m + 1))), IsConvexBody K' ∧ (∫ x in K', x = 0) ∧
      volume K' = volume K ∧
      volume (K' ∩ {x | 0 ≤ x 0}) = volume (K ∩ {x | 0 ≤ ⟪x, w⟫_ℝ}) := by
  obtain ⟨R, hR⟩ := GrunbaumAuxC.exists_rot w
  have hmp : MeasurePreserving R volume volume := R.measurePreserving
  have hemb : MeasurableEmbedding R := R.toHomeomorph.measurableEmbedding
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  obtain ⟨hKc, hKcv, hKi⟩ := hK
  have himg : ∀ S : Set (EuclideanSpace ℝ (Fin (m + 1))), volume (R '' S) = volume S := by
    intro S
    have h1 : R '' S = R.symm ⁻¹' S := R.toEquiv.image_eq_preimage_symm S
    rw [h1]
    exact R.symm.measurePreserving.measure_preimage_emb R.symm.toHomeomorph.measurableEmbedding S
  refine ⟨R '' K, ⟨?_, ?_, ?_⟩, ?_, himg K, ?_⟩
  · exact hKc.image R.continuous
  · exact hKcv.linear_image R.toLinearEquiv.toLinearMap
  · have := R.toHomeomorph.image_interior K
    exact this ▸ hKi.image _
  · rw [hmp.setIntegral_image_emb hemb]
    have h2 := ContinuousLinearEquiv.integral_comp_comm (μ := volume.restrict K) R.toContinuousLinearEquiv (fun x => x)
    exact h2.trans (by rw [hc]; exact map_zero _)
  · have : R '' (K ∩ {x | 0 ≤ ⟪x, w⟫_ℝ}) = R '' K ∩ {x | 0 ≤ x 0} := by
      have key : ∀ x : EuclideanSpace ℝ (Fin (m + 1)), ⟪x, w⟫_ℝ = ‖w‖ * (R x) 0 := by
        intro x
        have h3 : ⟪R x, R w⟫_ℝ = ⟪x, w⟫_ℝ := R.inner_map_map x w
        rw [← h3, hR, inner_smul_right, EuclideanSpace.inner_single_right]
        simp
      ext y
      simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨x, ⟨hxK, hx⟩, rfl⟩
        refine ⟨⟨x, hxK, rfl⟩, ?_⟩
        rw [key] at hx
        exact nonneg_of_mul_nonneg_right hx hnorm
      · rintro ⟨⟨x, hxK, rfl⟩, hy⟩
        refine ⟨x, ⟨hxK, ?_⟩, rfl⟩
        rw [key]
        exact mul_nonneg hnorm.le hy
    rw [← this, himg]

end GrunbaumSpec
end PieceC

section PieceD
open MeasureTheory
open scoped InnerProductSpace ENNReal
namespace ConvexOptAlg.CenterGravity

theorem lemma_2_2 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K)
    (hcent : ∫ x in K, x = 0) (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0) :
    ENNReal.ofReal (Real.exp (-1)) * volume K ≤ volume (K ∩ {x | 0 ≤ ⟪x, w⟫_ℝ}) := by
  cases n with
  | zero => exact absurd (Subsingleton.elim w 0) hw
  | succ m =>
    obtain ⟨K', hK', hc', hvol, hhalf⟩ := GrunbaumSpec.rotate_to_axis K hK hcent w hw
    obtain ⟨g, hmeas, h0, hlc, hint, hsupp, hI, hIhalf, hmean⟩ := GrunbaumSpec.slice_profile K' hK'
    have hfin : volume K' < ∞ := hK'.1.measure_lt_top
    have hposv : 0 < volume K' := by
      obtain ⟨_, _, hi⟩ := hK'
      exact lt_of_lt_of_le (isOpen_interior.measure_pos volume hi) (measure_mono interior_subset)
    have hmean0 : ∫ x in K', x 0 = 0 := by
      have hint2 : IntegrableOn (fun x : EuclideanSpace ℝ (Fin (m + 1)) => x) K' volume :=
        continuous_id.continuousOn.integrableOn_compact hK'.1
      have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (0 : Fin (m + 1)) : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ) hint2
      simpa [hc'] using this
    have hpos : 0 < ∫ t, g t := by
      rw [hI]; exact ENNReal.toReal_pos hposv.ne' hfin.ne
    have hA := GrunbaumSpec.oneD_centered g hmeas h0 hlc hint hsupp hpos (by rw [hmean]; exact hmean0)
    rw [hI, hIhalf] at hA
    have hfin2 : volume (K' ∩ {x | 0 ≤ x 0}) ≠ ∞ :=
      ne_top_of_le_ne_top hfin.ne (measure_mono Set.inter_subset_left)
    rw [← hvol, ← hhalf]
    rw [← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_toReal hfin2, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    exact ENNReal.ofReal_le_ofReal hA

end ConvexOptAlg.CenterGravity

open ConvexOptAlg.CenterGravity in
theorem solution {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsConvexBody K)
    (hcent : ∫ x in K, x = 0) (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0) :
    ENNReal.ofReal (Real.exp (-1)) * volume K ≤ volume (K ∩ {x | 0 ≤ ⟪x, w⟫_ℝ}) :=
  ConvexOptAlg.CenterGravity.lemma_2_2 K hK hcent w hw
end PieceD

