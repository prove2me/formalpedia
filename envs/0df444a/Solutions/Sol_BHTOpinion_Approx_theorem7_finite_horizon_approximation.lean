-- Prove2me | solution 1 for BHTOpinion.Approx.theorem7_finite_horizon_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T05:20:49.517579+00:00
-- url     : https://prove2.me/submissions/4c5ff367-1af8-4b9f-a6bc-65875be87921

import Mathlib
import Definitions.Def_BHTOpinion_Approx_Discrete
import Definitions.Def_BHTOpinion_Approx_Continuum

set_option autoImplicit false

namespace BHTApproxT7

open MeasureTheory Set Filter Topology BHTOpinion.Continuum BHTOpinion.Approx

/-- truncation used by the interaction kernel -/
noncomputable def phi (w : ℝ) : ℝ := if |w| < 1 then w else 0

lemma phi_measurable : Measurable phi := by
  unfold phi
  exact Measurable.ite (measurableSet_lt continuous_abs.measurable measurable_const)
    measurable_id measurable_const

lemma abs_phi_le (w : ℝ) : |phi w| ≤ 1 := by
  unfold phi; split_ifs with h
  · exact h.le
  · simp

lemma opL_eq_phi (x : ℝ → ℝ) (α : ℝ) : opL x α = ∫ γ in I, phi (x γ - x α) := by
  unfold opL phi
  congr 1; funext γ; rw [abs_sub_comm]

lemma volI_real : volume.real I = 1 := by
  simp [I]

lemma opL_abs_le (x : ℝ → ℝ) (α : ℝ) : |opL x α| ≤ 1 := by
  rw [opL_eq_phi]
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := I)
    (f := fun γ => phi (x γ - x α)) (C := 1) (by simp [I]) (fun γ _ => by
      rw [Real.norm_eq_abs]; exact abs_phi_le _)
  rw [volI_real, Real.norm_eq_abs] at h; simpa using h

lemma aem_of_meas {x : ℝ → ℝ} (hx : Measurable (fun a : I => x a)) :
    AEMeasurable x (volume.restrict I) := by
  show AEMeasurable x (volume.restrict (Icc (0:ℝ) 1))
  rw [← map_comap_subtype_coe (measurableSet_Icc : MeasurableSet (Icc (0:ℝ) 1))]
  exact (MeasurableEmbedding.subtype_coe measurableSet_Icc).aemeasurable_map_iff.mpr hx.aemeasurable

lemma integrable_phi {x : ℝ → ℝ} (hx : AEMeasurable x (volume.restrict I)) (c : ℝ) :
    Integrable (fun γ => phi (x γ - c)) (volume.restrict I) := by
  refine Integrable.of_bound ?_ 1 (Eventually.of_forall fun γ => ?_)
  · exact (phi_measurable.comp_aemeasurable (hx.sub aemeasurable_const)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact abs_phi_le _

/-- pointwise key inequality for the lower slope bound -/
lemma phi_diff_ge (a b c : ℝ) (hab : a ≤ b) :
    -(b - a) ≤ phi (c - b) - phi (c - a) := by
  unfold phi
  split_ifs with h1 h2 h2
  · linarith
  · -- |c-b|<1, |c-a| ≥ 1
    rcases le_or_gt 0 (c - a) with h | h
    · rw [abs_of_nonneg h] at h2; linarith
    · rw [abs_of_neg h] at h2; rw [abs_lt] at h1; linarith
  · rcases le_or_gt 0 (c - b) with h | h
    · rw [abs_of_nonneg h] at h1; rw [abs_lt] at h2; linarith
    · rw [abs_of_neg h] at h1; rw [abs_lt] at h2; linarith
  · linarith

lemma opL_diff_ge {x : ℝ → ℝ} (hx : AEMeasurable x (volume.restrict I)) (α β : ℝ)
    (h : x α ≤ x β) : -(x β - x α) ≤ opL x β - opL x α := by
  rw [opL_eq_phi, opL_eq_phi, ← integral_sub (integrable_phi hx _) (integrable_phi hx _)]
  have hc : ∫ _ in I, (-(x β - x α)) = -(x β - x α) := by
    rw [setIntegral_const, volI_real]; simp
  rw [← hc]
  refine setIntegral_mono_on (integrable_const _) ?_ measurableSet_Icc (fun γ _ => ?_)
  · exact (integrable_phi hx _).sub (integrable_phi hx _)
  · exact phi_diff_ge _ _ _ h

/-- increments of a solution of the integral equation -/
lemma sol_incr {x0 : ℝ → ℝ} {x : ℝ → ℝ → ℝ} (hx : IsSolution x0 x) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) {α : ℝ} (hα : α ∈ I) :
    x t α - x s α = ∫ τ in s..t, opL (x τ) α := by
  rw [hx.eq t ht α hα, hx.eq s hs α hα, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hx.integrable t ht α hα) (hx.integrable s hs α hα)]

lemma sol_lip {x0 : ℝ → ℝ} {x : ℝ → ℝ → ℝ} (hx : IsSolution x0 x) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) {α : ℝ} (hα : α ∈ I) : |x t α - x s α| ≤ |t - s| := by
  rw [sol_incr hx hs ht hα]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (C := 1)
    (f := fun τ => opL (x τ) α) (fun τ _ => by rw [Real.norm_eq_abs]; exact opL_abs_le _ _)
  rw [Real.norm_eq_abs] at this; linarith

lemma sol_init {x0 : ℝ → ℝ} {x : ℝ → ℝ → ℝ} (hx : IsSolution x0 x) {α : ℝ} (hα : α ∈ I) :
    x 0 α = x0 α := by
  rw [hx.eq 0 le_rfl α hα]; simp

/-- Theorem 4 of the paper: lower slope bound m e^{-t}. -/
theorem slope_bound {m : ℝ} (hm : 0 < m) {x0 : ℝ → ℝ}
    (hx0 : ∀ α ∈ I, ∀ β ∈ I, α < β → m * (β - α) ≤ x0 β - x0 α)
    {x : ℝ → ℝ → ℝ} (hx : IsSolution x0 x) :
    ∀ t : ℝ, 0 ≤ t → ∀ α ∈ I, ∀ β ∈ I, α < β → m * Real.exp (-t) * (β - α) ≤ x t β - x t α := by
  intro t0 ht0 α hα β hβ hαβ
  set u : ℝ → ℝ := fun t => x t β - x t α with hu
  set d0 := x0 β - x0 α with hd0
  have hu0 : u 0 = d0 := by simp only [hu, sol_init hx hα, sol_init hx hβ, hd0]
  have hd0pos : 0 < d0 := lt_of_lt_of_le (mul_pos hm (by linarith)) (hx0 α hα β hβ hαβ)
  have hm0 : m * (β - α) ≤ d0 := hx0 α hα β hβ hαβ
  -- increment formula
  have hint : ∀ s t, 0 ≤ s → 0 ≤ t →
      IntervalIntegrable (fun τ => opL (x τ) β - opL (x τ) α) volume s t := by
    intro s t hs ht
    exact (((hx.integrable s hs β hβ).symm.trans (hx.integrable t ht β hβ))).sub
      (((hx.integrable s hs α hα).symm.trans (hx.integrable t ht α hα)))
  have hincr : ∀ s t, 0 ≤ s → 0 ≤ t → u t - u s = ∫ τ in s..t, (opL (x τ) β - opL (x τ) α) := by
    intro s t hs ht
    have h1 := sol_incr hx hs ht hβ
    have h2 := sol_incr hx hs ht hα
    rw [intervalIntegral.integral_sub
      ((hx.integrable s hs β hβ).symm.trans (hx.integrable t ht β hβ))
      ((hx.integrable s hs α hα).symm.trans (hx.integrable t ht α hα))]
    simp only [hu]; linarith
  have hlip : ∀ s t, 0 ≤ s → 0 ≤ t → |u t - u s| ≤ 2 * |t - s| := by
    intro s t hs ht
    have h1 := sol_lip hx hs ht hβ
    have h2 := sol_lip hx hs ht hα
    have : u t - u s = (x t β - x s β) - (x t α - x s α) := by simp only [hu]; ring
    rw [this]
    calc |(x t β - x s β) - (x t α - x s α)| ≤ |x t β - x s β| + |x t α - x s α| := abs_sub _ _
      _ ≤ 2 * |t - s| := by linarith
  have hcont : ContinuousOn u (Ici 0) := by
    intro t ht
    rw [Metric.continuousWithinAt_iff]
    intro e he
    refine ⟨e / 2, by linarith, fun s hs hst => ?_⟩
    rw [Real.dist_eq] at hst ⊢
    have := hlip t s ht hs
    linarith
  have hkey : ∀ τ, 0 ≤ τ → 0 ≤ u τ → -u τ ≤ opL (x τ) β - opL (x τ) α := by
    intro τ hτ hpos
    exact opL_diff_ge (aem_of_meas (hx.mem_Y τ hτ).1) α β (by simp only [hu] at hpos; linarith)
  -- Gronwall on intervals where u > 0
  have hgron : ∀ T, 0 ≤ T → (∀ t ∈ Ico 0 T, 0 < u t) → ∀ t ∈ Icc 0 T, d0 * Real.exp (-t) ≤ u t := by
    intro T hT hposT
    have := le_gronwallBound_of_liminf_deriv_right_le (f := fun t => -u t) (f' := fun t => u t)
      (δ := -d0) (K := -1) (ε := 0) (a := 0) (b := T)
      ((hcont.mono Icc_subset_Ici_self).neg) ?_ (by simp [hu0]) (fun t _ => by simp)
    · intro t ht
      have h := this t ht
      rw [gronwallBound_ε0] at h
      simp only [sub_zero, neg_one_mul] at h
      linarith
    · intro t ht r hr
      have hut := hposT t ht
      have ht0 : 0 ≤ t := ht.1
      set η := min (u t / 2) ((r - u t) / 4) with hη
      have hηpos : 0 < η := lt_min (by linarith) (by linarith)
      refine Eventually.frequently ?_
      filter_upwards [Ioo_mem_nhdsGT (show t < t + η by linarith)] with z hz
      have hz0 : 0 ≤ z := by linarith [hz.1]
      have hzt : 0 < z - t := by linarith [hz.1]
      have hbound : ∀ τ ∈ Icc t z, -(opL (x τ) β - opL (x τ) α) ≤ u t + 2 * η := by
        intro τ hτ
        have hτ0 : 0 ≤ τ := le_trans ht0 hτ.1
        have hl := hlip t τ ht0 hτ0
        have hτt : |τ - t| ≤ η := by
          rw [abs_of_nonneg (by linarith [hτ.1])]; linarith [hτ.2, hz.2]
        have hupos : 0 ≤ u τ := by
          have := abs_le.mp (le_trans hl (by linarith : 2 * |τ - t| ≤ 2 * η))
          have : η ≤ u t / 2 := min_le_left _ _
          linarith
        have := hkey τ hτ0 hupos
        have := (abs_le.mp (le_trans hl (by linarith : 2 * |τ - t| ≤ 2 * η))).2
        linarith
      have hI : ∫ τ in t..z, -(opL (x τ) β - opL (x τ) α) ≤ ∫ τ in t..z, (u t + 2 * η) :=
        intervalIntegral.integral_mono_on hz.1.le (hint t z ht0 hz0).neg intervalIntegrable_const
          hbound
      rw [intervalIntegral.integral_neg, ← hincr t z ht0 hz0, intervalIntegral.integral_const,
        smul_eq_mul] at hI
      have h4 : η ≤ (r - u t) / 4 := min_le_right _ _
      rw [inv_mul_lt_iff₀ hzt]
      nlinarith
  -- positivity of u
  have hpos : ∀ t, 0 ≤ t → 0 < u t := by
    intro t ht
    by_contra hneg
    push Not at hneg
    set S := Icc 0 t ∩ {s | u s ≤ 0} with hS
    have hSc : IsClosed S :=
      (hcont.mono Icc_subset_Ici_self).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hSne : S.Nonempty := ⟨t, ⟨⟨ht, le_rfl⟩, hneg⟩⟩
    have hSb : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
    have hmem := hSc.csInf_mem hSne hSb
    set t1 := sInf S
    have ht1 : 0 ≤ t1 := hmem.1.1
    have hbelow : ∀ s ∈ Ico 0 t1, 0 < u s := by
      intro s hs
      by_contra hc; push Not at hc
      have : t1 ≤ s := csInf_le hSb ⟨⟨hs.1, by linarith [hs.2, hmem.1.2]⟩, hc⟩
      linarith [hs.2]
    have h1 := hgron t1 ht1 hbelow t1 ⟨ht1, le_rfl⟩
    have h2 : 0 < d0 * Real.exp (-t1) := mul_pos hd0pos (Real.exp_pos _)
    have h3 : u t1 ≤ 0 := hmem.2
    linarith
  have := hgron t0 ht0 (fun t ht => hpos t ht.1) t0 ⟨ht0, le_rfl⟩
  have hexp : 0 < Real.exp (-t0) := Real.exp_pos _
  simp only [hu] at this
  nlinarith

/-- pointwise Lipschitz-type estimate for phi -/
lemma phi_lip (a b δ : ℝ) (hδ : 0 ≤ δ) (h : |b - a| ≤ 2 * δ) :
    |phi b - phi a| ≤ 2 * δ + (if 1 - 2 * δ ≤ |a| ∧ |a| ≤ 1 + 2 * δ then 1 else 0) := by
  have hite : (0:ℝ) ≤ (if 1 - 2 * δ ≤ |a| ∧ |a| ≤ 1 + 2 * δ then 1 else 0) := by
    split_ifs <;> norm_num
  have h1 : |b| ≤ |a| + 2 * δ := by
    have := abs_sub_abs_le_abs_sub b a; linarith
  have h2 : |a| ≤ |b| + 2 * δ := by
    have := abs_sub_abs_le_abs_sub a b; rw [abs_sub_comm] at this; linarith
  by_cases ha : |a| < 1 <;> by_cases hb : |b| < 1
  · simp only [phi, ha, hb, if_true]; linarith
  · have hb' := not_lt.mp hb
    simp only [phi, ha, hb, if_true, if_false]
    rw [if_pos (show 1 - 2 * δ ≤ |a| ∧ |a| ≤ 1 + 2 * δ from ⟨by linarith, by linarith⟩), zero_sub,
      abs_neg]
    linarith
  · have ha' := not_lt.mp ha
    simp only [phi, ha, hb, if_true, if_false]
    rw [if_pos (show 1 - 2 * δ ≤ |a| ∧ |a| ≤ 1 + 2 * δ from ⟨by linarith, by linarith⟩), sub_zero]
    linarith
  · simp only [phi, ha, hb, if_false, sub_self, abs_zero]; linarith

lemma cluster {m' : ℝ} (hm' : 0 < m') {x : ℝ → ℝ}
    (hxs : ∀ α ∈ I, ∀ β ∈ I, α < β → m' * (β - α) ≤ x β - x α) (lo w : ℝ) :
    ∃ c, ∀ γ ∈ I, lo ≤ x γ ∧ x γ ≤ lo + w → |γ - c| ≤ w / m' := by
  by_cases h : ∃ γ0 ∈ I, lo ≤ x γ0 ∧ x γ0 ≤ lo + w
  · obtain ⟨γ0, hγ0, hl, hu⟩ := h
    refine ⟨γ0, fun γ hγ hγ' => ?_⟩
    rw [le_div_iff₀ hm']
    rcases lt_trichotomy γ γ0 with hlt | heq | hgt
    · have := hxs γ hγ γ0 hγ0 hlt
      rw [abs_of_neg (by linarith)]; nlinarith [hγ'.1, hγ'.2]
    · subst heq; simp only [sub_self, abs_zero, zero_mul]; linarith
    · have := hxs γ0 hγ0 γ hγ hgt
      rw [abs_of_pos (by linarith)]; nlinarith [hγ'.1, hγ'.2]
  · push Not at h
    exact ⟨0, fun γ hγ hγ' => absurd hγ'.2 (not_le.mpr (h γ hγ hγ'.1))⟩

/-- Lemma 1 of the paper (with constant 16 instead of 8). -/
lemma opL_lip {m' : ℝ} (hm' : 0 < m') {x y : ℝ → ℝ}
    (hxs : ∀ α ∈ I, ∀ β ∈ I, α < β → m' * (β - α) ≤ x β - x α)
    (hxm : AEMeasurable x (volume.restrict I)) (hym : AEMeasurable y (volume.restrict I))
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : ∀ γ ∈ I, |x γ - y γ| ≤ δ) {α : ℝ} (hα : α ∈ I) :
    |opL y α - opL x α| ≤ (2 + 16 / m') * δ := by
  obtain ⟨c1, hc1⟩ := cluster hm' hxs (x α + (1 - 2 * δ)) (4 * δ)
  obtain ⟨c2, hc2⟩ := cluster hm' hxs (x α - (1 + 2 * δ)) (4 * δ)
  set J1 : Set ℝ := Icc (c1 - 4 * δ / m') (c1 + 4 * δ / m') with hJ1
  set J2 : Set ℝ := Icc (c2 - 4 * δ / m') (c2 + 4 * δ / m') with hJ2
  have hi1 : ∀ γ, (0:ℝ) ≤ J1.indicator 1 γ := fun γ => indicator_nonneg (fun _ _ => zero_le_one) γ
  have hi2 : ∀ γ, (0:ℝ) ≤ J2.indicator 1 γ := fun γ => indicator_nonneg (fun _ _ => zero_le_one) γ
  have hpt : ∀ γ ∈ I, |phi (y γ - y α) - phi (x γ - x α)| ≤
      2 * δ + (J1.indicator 1 γ + J2.indicator 1 γ) := by
    intro γ hγ
    have hd : |(y γ - y α) - (x γ - x α)| ≤ 2 * δ := by
      have h1 := hδ γ hγ
      have h2 := hδ α hα
      rw [abs_sub_comm] at h1 h2
      calc |(y γ - y α) - (x γ - x α)| = |(y γ - x γ) - (y α - x α)| := by ring_nf
        _ ≤ |y γ - x γ| + |y α - x α| := abs_sub _ _
        _ ≤ 2 * δ := by linarith
    refine le_trans (phi_lip _ _ δ hδ0 hd) (add_le_add le_rfl ?_)
    split_ifs with hc
    · rcases le_or_gt 0 (x γ - x α) with hs | hs
      · rw [abs_of_nonneg hs] at hc
        have h := hc1 γ hγ ⟨by linarith [hc.1], by linarith [hc.2]⟩
        have hmem : γ ∈ J1 := by
          rw [abs_le] at h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
        rw [indicator_of_mem hmem, Pi.one_apply]; linarith [hi2 γ]
      · rw [abs_of_neg hs] at hc
        have h := hc2 γ hγ ⟨by linarith [hc.1], by linarith [hc.2]⟩
        have hmem : γ ∈ J2 := by
          rw [abs_le] at h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
        rw [indicator_of_mem hmem, Pi.one_apply]; linarith [hi1 γ]
    · linarith [hi1 γ, hi2 γ]
  have hJ : ∀ J : Set ℝ, MeasurableSet J →
      ∫ γ in I, J.indicator (1 : ℝ → ℝ) γ = volume.real (J ∩ I) := by
    intro J hJ
    rw [integral_indicator_one hJ, measureReal_restrict_apply hJ]
  have hind : ∀ J : Set ℝ, MeasurableSet J →
      Integrable (J.indicator (1 : ℝ → ℝ)) (volume.restrict I) :=
    fun J hJ => (integrable_const (1:ℝ)).indicator hJ
  have hv : ∀ c : ℝ, volume.real (Icc (c - 4 * δ / m') (c + 4 * δ / m') ∩ I) ≤ 8 * δ / m' := by
    intro c
    have hw : 0 ≤ 4 * δ / m' := by positivity
    calc volume.real (Icc (c - 4 * δ / m') (c + 4 * δ / m') ∩ I)
        ≤ volume.real (Icc (c - 4 * δ / m') (c + 4 * δ / m')) :=
          measureReal_mono inter_subset_left measure_Icc_lt_top.ne
      _ = 8 * δ / m' := by rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hiy := integrable_phi hym (y α)
  have hix := integrable_phi hxm (x α)
  rw [opL_eq_phi, opL_eq_phi, ← integral_sub hiy hix]
  have hrhs : Integrable (fun γ => 2 * δ + (J1.indicator 1 γ + J2.indicator 1 γ))
      (volume.restrict I) :=
    (integrable_const _).add ((hind J1 measurableSet_Icc).add (hind J2 measurableSet_Icc))
  have hval : (2 + 16 / m') * δ = 2 * δ + (8 * δ / m' + 8 * δ / m') := by
    field_simp; ring
  calc |∫ γ in I, (phi (y γ - y α) - phi (x γ - x α))|
      ≤ ∫ γ in I, |phi (y γ - y α) - phi (x γ - x α)| := abs_integral_le_integral_abs
    _ ≤ ∫ γ in I, (2 * δ + (J1.indicator 1 γ + J2.indicator 1 γ)) :=
        setIntegral_mono_on (hiy.sub hix).abs hrhs measurableSet_Icc hpt
    _ = 2 * δ + (volume.real (J1 ∩ I) + volume.real (J2 ∩ I)) := by
        rw [integral_add (f := fun _ => 2 * δ)
          (g := fun γ => J1.indicator (1 : ℝ → ℝ) γ + J2.indicator (1 : ℝ → ℝ) γ)
          (integrable_const _) ((hind J1 measurableSet_Icc).add (hind J2 measurableSet_Icc)),
          integral_add (f := fun γ => J1.indicator (1 : ℝ → ℝ) γ)
          (g := fun γ => J2.indicator (1 : ℝ → ℝ) γ) (hind J1 measurableSet_Icc)
          (hind J2 measurableSet_Icc), setIntegral_const, volI_real, hJ _ measurableSet_Icc,
          hJ _ measurableSet_Icc, one_smul]
        try rfl
    _ ≤ (2 + 16 / m') * δ := by rw [hval]; linarith [hv c1, hv c2]

/-- the block index used by `G` -/
noncomputable def idx (n : ℕ) (hn : 0 < n) (α : ℝ) : Fin n :=
  ⟨min ⌊(n : ℝ) * α⌋₊ (n - 1), lt_of_le_of_lt (min_le_right _ _) (Nat.sub_lt hn one_pos)⟩

lemma G_eq {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) (α : ℝ) : G v α = v (idx n hn α) := by
  unfold G idx; rw [dif_pos hn]

lemma idx_block {n : ℕ} (hn : 0 < n) (k : Fin n) {γ : ℝ} (h1 : ((k : ℕ) : ℝ) / n < γ)
    (h2 : γ < (((k : ℕ) : ℝ) + 1) / n) : idx n hn γ = k := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  apply Fin.ext
  simp only [idx]
  have hk0 : (0:ℝ) ≤ ((k : ℕ) : ℝ) / n := by positivity
  have hγ0 : 0 ≤ (n:ℝ) * γ := mul_nonneg hnpos.le (by linarith)
  have hfl : ⌊(n:ℝ) * γ⌋₊ = (k : ℕ) := by
    rw [Nat.floor_eq_iff hγ0]
    constructor
    · rw [div_lt_iff₀ hnpos] at h1; linarith
    · rw [lt_div_iff₀ hnpos] at h2; linarith
  rw [hfl]; exact min_eq_left (Nat.le_sub_one_of_lt k.isLt)

lemma integral_G {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) (f : ℝ → ℝ) :
    IntegrableOn (fun γ => f (G v γ)) I ∧ ∫ γ in I, f (G v γ) = (1 / n) * ∑ j, f (v j) := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hpiece : ∀ k : Fin n, EqOn (fun γ => f (G v γ)) (fun _ => f (v k))
      (uIoo (((k : ℕ) : ℝ) / n) ((((k : ℕ) + 1 : ℕ) : ℝ) / n)) := by
    intro k γ hγ
    have hle : ((k : ℕ) : ℝ) / n ≤ ((((k : ℕ) + 1 : ℕ) : ℝ)) / n := by
      gcongr; push_cast; linarith
    rw [uIoo_of_le hle] at hγ
    simp only [G_eq hn]
    rw [idx_block hn k hγ.1 (by have := hγ.2; push_cast at this; exact this)]
  have hint : ∀ k < n, IntervalIntegrable (fun γ => f (G v γ)) volume
      ((k : ℝ) / n) (((k + 1 : ℕ) : ℝ) / n) := by
    intro k hk
    exact (intervalIntegrable_const).congr_uIoo (hpiece ⟨k, hk⟩).symm
  have ha0 : ((0 : ℕ) : ℝ) / n = 0 := by simp
  have han : ((n : ℕ) : ℝ) / n = 1 := by field_simp
  have hII : IntervalIntegrable (fun γ => f (G v γ)) volume 0 1 := by
    have := IntervalIntegrable.trans_iterate (a := fun k : ℕ => (k : ℝ) / n) hint
    rwa [ha0, han] at this
  refine ⟨?_, ?_⟩
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mp hII
  · show ∫ γ in Icc (0:ℝ) 1, f (G v γ) = _
    have hsum := intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ) / n) hint
    rw [ha0, han] at hsum
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one, ← hsum,
      ← Fin.sum_univ_eq_sum_range (fun k => ∫ γ in ((k : ℕ) : ℝ) / n..(((k + 1 : ℕ)) : ℝ) / n,
        f (G v γ)) n, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [intervalIntegral.integral_congr_uIoo (hpiece k), intervalIntegral.integral_const,
      smul_eq_mul]
    push_cast; field_simp; ring

lemma opL_G {n : ℕ} (hn : 0 < n) (v : Fin n → ℝ) (α : ℝ) :
    opL (G v) α = (1 / n) * discreteRhs v (idx n hn α) := by
  have h := (integral_G hn v (fun w => phi (w - G v α))).2
  rw [opL_eq_phi, h, discreteRhs, Finset.sum_filter, G_eq hn v α]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp only [phi]; rw [abs_sub_comm]

lemma y_incr {n : ℕ} (hn : 0 < n) {ξ : ℝ → Fin n → ℝ} (hξ : IsDiscreteSolution ξ)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (α : ℝ) :
    IntervalIntegrable (fun τ => opL (G (ξ (τ / n))) α) volume s t ∧
    G (ξ (t / n)) α - G (ξ (s / n)) α = ∫ τ in s..t, opL (G (ξ (τ / n))) α := by
  have hnpos : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hsn : 0 ≤ s / n := div_nonneg hs hnpos.le
  have htn : 0 ≤ t / n := div_nonneg ht hnpos.le
  have hfi : IntervalIntegrable (fun σ => discreteRhs (ξ σ) (idx n hn α)) volume (s / n) (t / n) :=
    (hξ.2.1 (s / n) hsn (idx n hn α)).symm.trans (hξ.2.1 (t / n) htn (idx n hn α))
  have hfun : (fun τ => opL (G (ξ (τ / n))) α) =
      fun τ => (1 / n) * discreteRhs (ξ (τ / n)) (idx n hn α) := by
    funext τ; rw [opL_G hn]
  have hcomp : IntervalIntegrable (fun τ => discreteRhs (ξ (τ / n)) (idx n hn α)) volume s t := by
    have h := hfi.comp_mul_left (c := (n:ℝ)⁻¹)
    have e1 : s / n / (n:ℝ)⁻¹ = s := by field_simp
    have e2 : t / n / (n:ℝ)⁻¹ = t := by field_simp
    rw [e1, e2] at h
    convert h using 3 with τ
    rw [div_eq_inv_mul]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact hcomp.const_mul _
  · have hc := intervalIntegral.integral_comp_div (a := s) (b := t)
      (fun σ => discreteRhs (ξ σ) (idx n hn α)) hnpos.ne'
    rw [hfun, intervalIntegral.integral_const_mul, hc, G_eq hn, G_eq hn,
      hξ.2.2 (t / n) htn (idx n hn α), hξ.2.2 (s / n) hsn (idx n hn α), add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left (hξ.2.1 _ htn _) (hξ.2.1 _ hsn _), smul_eq_mul]
    field_simp

lemma tri3 (a b c : ℝ) : |a + b - c| ≤ |a| + |b| + |c| := by
  have h1 := abs_sub (a + b) c
  have h2 := abs_add_le a b
  linarith

theorem main (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (x0 : ℝ → ℝ) (hx0m : BHTOpinion.Continuum.InXm m x0) (hx0M : BHTOpinion.Continuum.InXM M x0)
    (x : ℝ → ℝ → ℝ) (hx : BHTOpinion.Continuum.IsSolution x0 x)
    (ξ : (n : ℕ) → ℝ → Fin n → ℝ)
    (hproper : ∀ n : ℕ, 0 < n → IsProperDiscreteSolution (ξ n))
    (hsorted : ∀ n : ℕ, 0 < n → Monotone (ξ n 0))
    (hinit : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      ∀ α ∈ BHTOpinion.Continuum.I, |G (ξ n 0) α - x0 α| ≤ δ) :
    ∀ T ε : ℝ, 0 < ε → ∃ n' : ℕ, ∀ n : ℕ, n' ≤ n → 0 < n →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α ∈ BHTOpinion.Continuum.I, |G (ξ n (t / n)) α - x t α| ≤ ε := by
  intro T ε hε
  set T' := max T 0 with hT'
  have hT'0 : 0 ≤ T' := le_max_right _ _
  set mT := m * Real.exp (-(T' + 1)) with hmT
  have hmTpos : 0 < mT := mul_pos hm (Real.exp_pos _)
  set K := 2 + 16 / mT with hK
  have hKpos : 0 < K := by positivity
  set δ := ε * Real.exp (-(K * T')) with hδ
  have hδpos : 0 < δ := mul_pos hε (Real.exp_pos _)
  obtain ⟨N, hN⟩ := hinit δ hδpos
  refine ⟨N, fun n hnN hn t ht α hα => ?_⟩
  have hξ := (hproper n hn).1
  have hslope := slope_bound hm hx0m.2 hx
  have : Nonempty I := ⟨⟨0, by simp [I]⟩⟩
  set y : ℝ → ℝ → ℝ := fun τ γ => G (ξ n (τ / n)) γ with hy
  have hbdd : ∀ τ, 0 ≤ τ → BddAbove (range fun γ : I => |y τ γ - x τ γ|) := by
    intro τ hτ
    obtain ⟨C, hC⟩ := (hx.mem_Y τ hτ).2
    refine ⟨(∑ j, |ξ n (τ / n) j|) + C, ?_⟩
    rintro _ ⟨γ, rfl⟩
    have h1 : |y τ γ| ≤ ∑ j, |ξ n (τ / n) j| := by
      simp only [hy, G_eq hn]
      exact Finset.single_le_sum (f := fun j => |ξ n (τ / n) j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ _)
    have h2 := hC γ γ.2
    calc |y τ γ - x τ γ| ≤ |y τ γ| + |x τ γ| := abs_sub _ _
      _ ≤ _ := by linarith
  set e : ℝ → ℝ := fun τ => ⨆ γ : I, |y τ γ - x τ γ| with he
  have hle_e : ∀ τ, 0 ≤ τ → ∀ γ ∈ I, |y τ γ - x τ γ| ≤ e τ := fun τ hτ γ hγ =>
    le_ciSup (f := fun γ : I => |y τ γ - x τ γ|) (hbdd τ hτ) ⟨γ, hγ⟩
  have he_le : ∀ τ c, (∀ γ ∈ I, |y τ γ - x τ γ| ≤ c) → e τ ≤ c := fun τ c h =>
    ciSup_le fun γ => h γ γ.2
  have he_nn : ∀ τ, 0 ≤ τ → 0 ≤ e τ := fun τ hτ =>
    le_trans (abs_nonneg _) (hle_e τ hτ 0 (by simp [I]))
  have hyinc : ∀ s τ, 0 ≤ s → 0 ≤ τ → ∀ γ,
      IntervalIntegrable (fun σ => opL (y σ) γ) volume s τ ∧
      y τ γ - y s γ = ∫ σ in s..τ, opL (y σ) γ :=
    fun s τ hs hτ γ => y_incr hn hξ hs hτ γ
  have hylip : ∀ s τ, 0 ≤ s → 0 ≤ τ → ∀ γ, |y τ γ - y s γ| ≤ |τ - s| := by
    intro s τ hs hτ γ
    rw [(hyinc s τ hs hτ γ).2]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := τ) (C := 1)
      (f := fun σ => opL (y σ) γ) (fun σ _ => by rw [Real.norm_eq_abs]; exact opL_abs_le _ _)
    rw [Real.norm_eq_abs] at this; linarith
  have helip : ∀ s τ, 0 ≤ s → 0 ≤ τ → e τ ≤ e s + 2 * |τ - s| := by
    intro s τ hs hτ
    apply he_le
    intro γ hγ
    have h1 := hylip s τ hs hτ γ
    have h2 := sol_lip hx hs hτ hγ
    have h3 := hle_e s hs γ hγ
    have h4 := tri3 (y s γ - x s γ) (y τ γ - y s γ) (x τ γ - x s γ)
    have h5 : (y s γ - x s γ) + (y τ γ - y s γ) - (x τ γ - x s γ) = y τ γ - x τ γ := by ring
    rw [h5] at h4
    linarith
  have hecont : ContinuousOn e (Icc 0 T') := by
    intro τ hτ
    rw [Metric.continuousWithinAt_iff]
    intro r hr
    refine ⟨r / 4, by linarith, fun s hs hsτ => ?_⟩
    rw [Real.dist_eq] at hsτ ⊢
    have h1 := helip τ s hτ.1 hs.1
    have h2 := helip s τ hs.1 hτ.1
    rw [abs_sub_comm] at h2
    rw [abs_lt]; constructor <;> linarith
  have hderiv : ∀ τ ∈ Ico 0 T', ∀ r, K * e τ < r →
      ∃ᶠ z in 𝓝[>] τ, (z - τ)⁻¹ * (e z - e τ) < r := by
    intro τ hτ r hr
    have hτ0 := hτ.1
    set η := min 1 ((r - K * e τ) / (4 * K)) with hη
    have hηpos : 0 < η := lt_min one_pos (div_pos (by linarith) (by positivity))
    have hη1 : η ≤ 1 := min_le_left _ _
    have hη2 : η * (4 * K) ≤ r - K * e τ := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
    refine Eventually.frequently ?_
    filter_upwards [Ioo_mem_nhdsGT (show τ < τ + η by linarith)] with z hz
    have hz0 : 0 ≤ z := by linarith [hz.1]
    have hzt : 0 < z - τ := by linarith [hz.1]
    have hez : e z ≤ e τ + (z - τ) * (K * (e τ + 2 * η)) := by
      apply he_le
      intro γ hγ
      have hpt : ∀ σ ∈ Set.uIoc τ z, ‖opL (y σ) γ - opL (x σ) γ‖ ≤ K * (e τ + 2 * η) := by
        intro σ hσ
        rw [uIoc_of_le hz.1.le] at hσ
        have hσ0 : 0 ≤ σ := by linarith [hσ.1]
        have hesσ : e σ ≤ e τ + 2 * η := by
          have := helip τ σ hτ0 hσ0
          rw [abs_of_pos (by linarith [hσ.1])] at this
          linarith [hσ.2, hz.2]
        have hxs : ∀ a ∈ I, ∀ b ∈ I, a < b → mT * (b - a) ≤ x σ b - x σ a := by
          intro a ha b hb hab
          have h1 := hslope σ hσ0 a ha b hb hab
          have h2 : mT ≤ m * Real.exp (-σ) := by
            rw [hmT]; gcongr
            linarith [hσ.2, hz.2, hτ.2]
          have h3 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hab.le)
          linarith
        have hym : AEMeasurable (y σ) (volume.restrict I) :=
          (integral_G hn (ξ n (σ / n)) (fun w => w)).1.aemeasurable
        have hl := opL_lip hmTpos hxs (aem_of_meas (hx.mem_Y σ hσ0).1) hym (he_nn σ hσ0)
          (fun γ' hγ' => by rw [abs_sub_comm]; exact hle_e σ hσ0 γ' hγ') hγ
        rw [Real.norm_eq_abs]
        calc |opL (y σ) γ - opL (x σ) γ| ≤ K * e σ := hl
          _ ≤ K * (e τ + 2 * η) := by gcongr
      have hyz := hyinc τ z hτ0 hz0 γ
      have hxz := sol_incr hx hτ0 hz0 hγ
      have hxi : IntervalIntegrable (fun σ => opL (x σ) γ) volume τ z :=
        (hx.integrable τ hτ0 γ hγ).symm.trans (hx.integrable z hz0 γ hγ)
      have hdiff : (y z γ - x z γ) =
          (y τ γ - x τ γ) + ∫ σ in τ..z, (opL (y σ) γ - opL (x σ) γ) := by
        rw [intervalIntegral.integral_sub hyz.1 hxi, ← hyz.2, ← hxz]; ring
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hpt
      rw [Real.norm_eq_abs, abs_of_pos hzt] at hnorm
      rw [hdiff]
      have h3 := abs_add_le (y τ γ - x τ γ) (∫ σ in τ..z, (opL (y σ) γ - opL (x σ) γ))
      have h4 := hle_e τ hτ0 γ hγ
      nlinarith
    rw [inv_mul_lt_iff₀ hzt]
    have hgap : K * (e τ + 2 * η) < r := by nlinarith
    calc e z - e τ ≤ (z - τ) * (K * (e τ + 2 * η)) := by linarith
      _ < (z - τ) * r := mul_lt_mul_of_pos_left hgap hzt
  have h0 : e 0 ≤ δ := by
    apply he_le
    intro γ hγ
    have := hN n hnN hn γ hγ
    rw [← sol_init hx hγ] at this
    simpa only [hy, zero_div] using this
  have hgr := le_gronwallBound_of_liminf_deriv_right_le (f := e) (f' := fun τ => K * e τ)
    (δ := δ) (K := K) (ε := 0) (a := 0) (b := T') hecont hderiv h0 (fun τ _ => by simp)
  have ht' : t ∈ Icc 0 T' := ⟨ht.1, le_trans ht.2 (le_max_left _ _)⟩
  have h1 := hgr t ht'
  rw [gronwallBound_ε0, sub_zero] at h1
  have h2 : δ * Real.exp (K * t) ≤ ε := by
    rw [hδ, mul_assoc, ← Real.exp_add]
    have : Real.exp (-(K * T') + K * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [mul_le_mul_of_nonneg_left ht'.2 hKpos.le]
    nlinarith
  have h3 : |G (ξ n (t / n)) α - x t α| ≤ e t := hle_e t ht.1 α hα
  linarith

end BHTApproxT7

open BHTOpinion.Approx in
theorem solution (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (x0 : ℝ → ℝ) (hx0m : BHTOpinion.Continuum.InXm m x0) (hx0M : BHTOpinion.Continuum.InXM M x0)
    (x : ℝ → ℝ → ℝ) (hx : BHTOpinion.Continuum.IsSolution x0 x)
    (ξ : (n : ℕ) → ℝ → Fin n → ℝ)
    (hproper : ∀ n : ℕ, 0 < n → IsProperDiscreteSolution (ξ n))
    (hsorted : ∀ n : ℕ, 0 < n → Monotone (ξ n 0))
    (hinit : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < n →
      ∀ α ∈ BHTOpinion.Continuum.I, |G (ξ n 0) α - x0 α| ≤ δ) :
    ∀ T ε : ℝ, 0 < ε → ∃ n' : ℕ, ∀ n : ℕ, n' ≤ n → 0 < n →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α ∈ BHTOpinion.Continuum.I, |G (ξ n (t / n)) α - x t α| ≤ ε := by
  exact BHTApproxT7.main m M hm hM x0 hx0m hx0M x hx ξ hproper hsorted hinit
