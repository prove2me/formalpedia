-- Prove2me | solution 1 for GenCostSched.GFCS.beta_increment_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:57:39.466179+00:00
-- url     : https://prove2.me/submissions/260729c7-ca7c-4f71-8737-306ea64c5900

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model
import Theorems.Thm_GenCostSched_GFCS_eq_24

open MeasureTheory Set
open scoped ENNReal

namespace GFCSBilAux
open GenCostSched.GFCS

theorem gp_nonneg {m : ℕ} (I : Instance m) (j : Fin m) (hj : I.JobStanding j) (t : ℝ)
    (ht : I.r j ≤ t) : 0 ≤ I.g' j t := by
  have hd := hj.2.2.2.2.2 t ht
  have hmono := hj.2.2.2.1
  have := hmono.derivWithin_nonneg (x := t)
  rwa [hd.derivWithin (uniqueDiffOn_Ici _ t (mem_Ici.2 ht))] at this

theorem gp_int {m : ℕ} (I : Instance m) (j : Fin m) (hj : I.JobStanding j) (a b : ℝ)
    (ha : I.r j ≤ a) : IntegrableOn (I.g' j) (Icc a b) := by
  have hd := hj.2.2.2.2.2
  have hcont : ContinuousOn (I.g j) (Icc a b) := by
    intro t ht
    exact ((hd t (ha.trans ht.1)).continuousWithinAt).mono
      (fun u hu => mem_Ici.2 (ha.trans hu.1))
  have h1 : IntegrableOn (I.g' j) (Ioc a b) := by
    apply intervalIntegral.integrableOn_deriv_of_nonneg hcont
    · intro t ht
      exact (hd t (ha.trans ht.1.le)).hasDerivAt (Ici_mem_nhds (lt_of_le_of_lt ha ht.1))
    · intro t ht
      exact gp_nonneg I j hj t (ha.trans ht.1.le)
  exact (integrableOn_Icc_iff_integrableOn_Ioc).2 h1

/-- Integrability and nonnegativity of `β̂` for an integral schedule. -/
theorem BH_int {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s)
    (x : Fin m → ℝ → ℝ) (hx : IsOffIntSched s A ρ x) :
    IntegrableOn (betaHat I.g' x) (Ici s) ∧ (∀ t, 0 ≤ betaHat I.g' x t) ∧
      (∀ ℓ, Integrable (fun τ => I.g' ℓ τ * x ℓ τ)) := by
  obtain ⟨x1, x2, x3, x4, x5, x6, ⟨T0, hT0⟩⟩ := hx
  set T := max T0 s
  have hT : ∀ j t, T < t → x j t = 0 := fun j t ht => hT0 j t (lt_of_le_of_lt (le_max_left _ _) ht)
  have hfnn : ∀ ℓ τ, 0 ≤ I.g' ℓ τ * x ℓ τ := by
    intro ℓ τ
    rcases x2 ℓ τ with h | h
    · simp [h]
    · rw [h, mul_one]
      have hℓ : ℓ ∈ A := by
        by_contra hc; rw [x4 ℓ hc τ] at h; exact zero_ne_one h
      have hτ : s ≤ τ := by
        by_contra hc; rw [x3 ℓ τ (lt_of_not_ge hc)] at h; exact zero_ne_one h
      exact gp_nonneg I ℓ (hI ℓ) τ ((hA ℓ hℓ).trans hτ)
  have hfint : ∀ ℓ, Integrable (fun τ => I.g' ℓ τ * x ℓ τ) := by
    intro ℓ
    by_cases hℓ : ℓ ∈ A
    · have hi := (gp_int I ℓ (hI ℓ) s T (hA ℓ hℓ)).integrable_indicator measurableSet_Icc
      have h2 : Integrable (fun τ => (Icc s T).indicator (I.g' ℓ) τ * x ℓ τ) := by
        refine hi.mul_bdd (c := 1) (x1 ℓ).aestronglyMeasurable ?_
        refine Filter.Eventually.of_forall (fun τ => ?_)
        rcases x2 ℓ τ with h | h <;> simp [h]
      refine h2.congr (Filter.Eventually.of_forall (fun τ => ?_))
      dsimp only
      by_cases hτ : τ ∈ Icc s T
      · simp [indicator_of_mem hτ]
      · rw [indicator_of_notMem hτ]
        simp only [mem_Icc, not_and_or, not_le] at hτ
        rcases hτ with h | h
        · simp [x3 ℓ τ h]
        · simp [hT ℓ τ h]
    · have : (fun τ => I.g' ℓ τ * x ℓ τ) = fun _ => 0 := by
        funext τ; simp [x4 ℓ hℓ τ]
      rw [this]; exact integrable_zero _ _ _
  have hanti : Antitone (betaHat I.g' x) := by
    intro t t' htt
    apply Finset.sum_le_sum
    intro ℓ _
    apply setIntegral_mono_set (hfint ℓ).integrableOn
    · exact Filter.Eventually.of_forall (fun τ => hfnn ℓ τ)
    · exact (Ioi_subset_Ioi htt).eventuallyLE
  have hnn : ∀ t, 0 ≤ betaHat I.g' x t := by
    intro t
    apply Finset.sum_nonneg
    intro ℓ _
    exact setIntegral_nonneg measurableSet_Ioi (fun τ _ => hfnn ℓ τ)
  have hzero : ∀ t, T ≤ t → betaHat I.g' x t = 0 := by
    intro t ht
    apply Finset.sum_eq_zero
    intro ℓ _
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro τ hτ
    simp [hT ℓ τ (lt_of_le_of_lt ht hτ)]
  refine ⟨?_, hnn, hfint⟩
  have hbd : IntegrableOn (betaHat I.g' x) (Icc s T) := by
    refine Measure.integrableOn_of_bounded (M := betaHat I.g' x s) (by simp)
      hanti.measurable.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun t ht => ?_))
    rw [Real.norm_of_nonneg (hnn t)]
    exact hanti ht.1
  refine hbd.of_forall_sdiff_eq_zero measurableSet_Ici ?_
  intro t ht
  apply hzero
  by_contra hc
  exact ht.2 ⟨mem_Ici.1 ht.1, le_of_not_ge hc⟩


/-- Postponing processing lowers the integral of a nonincreasing weight. Here `h - h T` is the
tail integral of a nonnegative `w` on `[s, T]`. -/
theorem dom (h w : ℝ → ℝ) (s T : ℝ) (hw : IntegrableOn w (Icc s T))
    (hwnn : ∀ u ∈ Icc s T, 0 ≤ w u) (hcont : ContinuousOn h (Icc s T))
    (hrep : ∀ t ∈ Icc s T, h t - h T = ∫ u in Ioc t T, w u)
    (x x' : ℝ → ℝ) (hxm : Measurable x) (hx'm : Measurable x')
    (hx01 : ∀ t, 0 ≤ x t ∧ x t ≤ 1) (hx'01 : ∀ t, 0 ≤ x' t ∧ x' t ≤ 1)
    (hxs : ∀ t, t ∉ Icc s T → x t = 0) (hx's : ∀ t, t ∉ Icc s T → x' t = 0)
    (htot : ∫⁻ t, ENNReal.ofReal (x' t) = ∫⁻ t, ENNReal.ofReal (x t))
    (hcum : ∀ u, s ≤ u → ∫⁻ t in Icc s u, ENNReal.ofReal (x' t) ≤
      ∫⁻ t in Icc s u, ENNReal.ofReal (x t)) :
    ∫ t, h t * x' t ≤ ∫ t, h t * x t := by
  set wt : ℝ → ℝ := (Icc s T).indicator w with hwt
  have hwtm : AEMeasurable wt := (hw.integrable_indicator measurableSet_Icc).aemeasurable
  have hψnn : ∀ t ∈ Icc s T, 0 ≤ h t - h T := by
    intro t ht; rw [hrep t ht]
    exact setIntegral_nonneg_of_ae_restrict
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall
        (fun u hu => hwnn u ⟨ht.1.trans hu.1.le, hu.2⟩)))
  -- integrability facts
  have hyint : ∀ y : ℝ → ℝ, Measurable y → (∀ t, 0 ≤ y t ∧ y t ≤ 1) →
      (∀ t, t ∉ Icc s T → y t = 0) → Integrable y ∧ Integrable (fun t => (h t - h T) * y t) ∧
        Integrable (fun t => h t * y t) := by
    intro y hym hy01 hys
    have hyI : Integrable y := by
      have : IntegrableOn y (Icc s T) := Measure.integrableOn_of_bounded (M := 1) (by simp)
        hym.aestronglyMeasurable (Filter.Eventually.of_forall (fun t => by
          rw [Real.norm_of_nonneg (hy01 t).1]; exact (hy01 t).2))
      exact (integrableOn_univ).1 (this.of_forall_sdiff_eq_zero MeasurableSet.univ
        (fun t ht => hys t ht.2))
    have hmul : ∀ (φ : ℝ → ℝ), ContinuousOn φ (Icc s T) → Integrable (fun t => φ t * y t) := by
      intro φ hφ
      have h1 := (hφ.integrableOn_Icc (μ := volume)).integrable_indicator measurableSet_Icc
      have h2 : Integrable (fun t => (Icc s T).indicator φ t * y t) := by
        refine h1.mul_bdd (c := 1) hym.aestronglyMeasurable ?_
        exact Filter.Eventually.of_forall (fun t => by
          rw [Real.norm_of_nonneg (hy01 t).1]; exact (hy01 t).2)
      refine h2.congr (Filter.Eventually.of_forall (fun t => ?_))
      by_cases ht : t ∈ Icc s T
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht, hys t ht]
    exact ⟨hyI, hmul _ (hcont.sub continuousOn_const), hmul _ hcont⟩
  -- the lintegral representation
  have hL : ∀ y : ℝ → ℝ, Measurable y → (∀ t, 0 ≤ y t ∧ y t ≤ 1) →
      (∀ t, t ∉ Icc s T → y t = 0) →
      ∫⁻ t, ENNReal.ofReal ((h t - h T) * y t) =
        ∫⁻ u, ENNReal.ofReal (wt u) * ∫⁻ t in Ico s u, ENNReal.ofReal (y t) := by
    intro y hym hy01 hys
    set G : ℝ → ℝ → ℝ≥0∞ := fun t u =>
      ({p : ℝ × ℝ | s ≤ p.1 ∧ p.1 < p.2}).indicator
        (fun p => ENNReal.ofReal (y p.1) * ENNReal.ofReal (wt p.2)) (t, u) with hG
    have hGm : AEMeasurable (Function.uncurry G) (volume.prod volume) := by
      have hS : MeasurableSet {p : ℝ × ℝ | s ≤ p.1 ∧ p.1 < p.2} :=
        (measurableSet_le measurable_const measurable_fst).inter
          (measurableSet_lt measurable_fst measurable_snd)
      have : Function.uncurry G = ({p : ℝ × ℝ | s ≤ p.1 ∧ p.1 < p.2}).indicator
          (fun p => ENNReal.ofReal (y p.1) * ENNReal.ofReal (wt p.2)) := by
        funext p; simp [hG, Function.uncurry]
      rw [this]
      exact ((hym.ennreal_ofReal.comp measurable_fst).aemeasurable.mul
        (hwtm.ennreal_ofReal.comp_snd)).indicator hS
    have e1 : ∫⁻ t, ENNReal.ofReal ((h t - h T) * y t) = ∫⁻ t, ∫⁻ u, G t u := by
      congr 1; funext t
      by_cases ht : t ∈ Icc s T
      · rw [ENNReal.ofReal_mul (hψnn t ht), hrep t ht,
          ofReal_integral_eq_lintegral_ofReal (hw.mono_set (fun u hu => ⟨ht.1.trans hu.1.le, hu.2⟩))
            ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall
              (fun u hu => hwnn u ⟨ht.1.trans hu.1.le, hu.2⟩)))]
        have : ∫⁻ u, G t u = ENNReal.ofReal (y t) * ∫⁻ u in Ioi t, ENNReal.ofReal (wt u) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator measurableSet_Ioi]
          congr 1; funext u
          by_cases hu : t < u
          · simp [hG, ht.1, hu, indicator_of_mem (mem_Ioi.2 hu)]
          · simp [hG, hu, indicator_of_notMem (show u ∉ Ioi t from hu)]
        rw [this, mul_comm]
        congr 1
        rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioc]
        congr 1; funext u
        by_cases hu : u ∈ Ioc t T
        · rw [indicator_of_mem hu, indicator_of_mem (show u ∈ Ioi t from hu.1)]
          simp [hwt, indicator_of_mem (show u ∈ Icc s T from ⟨ht.1.trans hu.1.le, hu.2⟩)]
        · rw [indicator_of_notMem hu]
          by_cases hu' : t < u
          · rw [indicator_of_mem (show u ∈ Ioi t from hu')]
            have hTu : T < u := by
              by_contra hc; exact hu ⟨hu', le_of_not_gt hc⟩
            simp [hwt, indicator_of_notMem (show u ∉ Icc s T from fun hh => absurd hh.2 (not_le.2 hTu))]
          · rw [indicator_of_notMem (show u ∉ Ioi t from hu')]
      · have h0 : ∀ u, G t u = 0 := by
          intro u; simp only [hG, indicator]; split_ifs <;> simp [hys t ht]
        rw [hys t ht]
        simp [h0]
    rw [e1, lintegral_lintegral_swap hGm]
    congr 1; funext u
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_indicator measurableSet_Ico]
    congr 1; funext t
    by_cases h' : s ≤ t ∧ t < u
    · rw [indicator_of_mem (show t ∈ Ico s u from h')]; simp [hG, h', mul_comm]
    · rw [indicator_of_notMem (show t ∉ Ico s u from h')]; simp [hG, h']
  have hcmp : ∫⁻ t, ENNReal.ofReal ((h t - h T) * x' t) ≤
      ∫⁻ t, ENNReal.ofReal ((h t - h T) * x t) := by
    rw [hL x' hx'm hx'01 hx's, hL x hxm hx01 hxs]
    apply lintegral_mono
    intro u
    refine mul_le_mul_of_nonneg_left ?_ (by simp)
    by_cases hu : s ≤ u
    · rw [setLIntegral_congr Ico_ae_eq_Icc, setLIntegral_congr Ico_ae_eq_Icc]
      exact hcum u hu
    · rw [Ico_eq_empty (fun h => hu h.le)]; simp
  obtain ⟨hxI, hxψ, hxh⟩ := hyint x hxm hx01 hxs
  obtain ⟨hx'I, hx'ψ, hx'h⟩ := hyint x' hx'm hx'01 hx's
  have hnn : ∀ y : ℝ → ℝ, (∀ t, 0 ≤ y t ∧ y t ≤ 1) → (∀ t, t ∉ Icc s T → y t = 0) →
      0 ≤ᵐ[volume] (fun t => (h t - h T) * y t) := by
    intro y hy01 hys
    refine Filter.Eventually.of_forall (fun t => ?_)
    by_cases ht : t ∈ Icc s T
    · exact mul_nonneg (hψnn t ht) (hy01 t).1
    · simp [hys t ht]
  have hsplit : ∀ y : ℝ → ℝ, Integrable y → Integrable (fun t => (h t - h T) * y t) →
      ∫ t, h t * y t = (∫ t, (h t - h T) * y t) + h T * ∫ t, y t := by
    intro y hyI hyψ
    calc ∫ t, h t * y t = ∫ t, ((h t - h T) * y t + h T * y t) := by
          congr 1; funext t; ring
      _ = (∫ t, (h t - h T) * y t) + ∫ t, h T * y t := integral_add hyψ (hyI.const_mul (h T))
      _ = _ := by rw [integral_const_mul]
  rw [hsplit x' hx'I hx'ψ, hsplit x hxI hxψ]
  have htot' : ∫ t, x' t = ∫ t, x t := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun t => (hx'01 t).1))
        hx'm.aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun t => (hx01 t).1))
        hxm.aestronglyMeasurable, htot]
  rw [htot']
  have hfinx : ∫⁻ t, ENNReal.ofReal ((h t - h T) * x t) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hxψ (hnn x hx01 hxs)]; exact ENNReal.ofReal_ne_top
  have := ENNReal.toReal_mono hfinx hcmp
  rw [← integral_eq_lintegral_of_nonneg_ae (hnn x' hx'01 hx's) hx'ψ.aestronglyMeasurable,
    ← integral_eq_lintegral_of_nonneg_ae (hnn x hx01 hxs) hxψ.aestronglyMeasurable] at this
  linarith

theorem hprops {m : ℕ} (I : Instance m) (ℓ : Fin m) (hJ : I.JobStanding ℓ) (h2 : I.TwiceDiff)
    (K : ℝ) (hK : I.CurvBound K) (s : ℝ) (hs : I.r ℓ ≤ s) (h w : ℝ → ℝ)
    (hh : h = fun t => (t - s) * I.g' ℓ t - K * I.g ℓ t)
    (hw : w = fun t => (K - 1) * I.g' ℓ t - (t - s) * I.g'' ℓ t) (a b : ℝ) (hsa : s ≤ a)
    (hab : a ≤ b) :
    ContinuousOn h (Icc a b) ∧ IntegrableOn w (Icc a b) ∧ (∀ u, s ≤ u → 0 ≤ w u) ∧
      ∀ t ∈ Icc a b, h t - h b = ∫ u in Ioc t b, w u := by
  have hg := hJ.2.2.2.2.2
  have hg' := h2 ℓ
  have hwnn : ∀ u, s ≤ u → 0 ≤ w u := by
    intro u hu
    rw [hw]
    have hc := hK.2 ℓ u (hs.trans hu)
    have hgp := gp_nonneg I ℓ hJ u (hs.trans hu)
    rcases le_or_gt 0 (I.g'' ℓ u) with hp | hn
    · have : (u - s) * I.g'' ℓ u ≤ (u - I.r ℓ) * I.g'' ℓ u :=
        mul_le_mul_of_nonneg_right (by linarith) hp
      linarith
    · have h1 : (u - s) * I.g'' ℓ u ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hn.le
      have h3 : 0 ≤ (K - 1) * I.g' ℓ u := mul_nonneg (by linarith [hK.1]) hgp
      linarith
  have hD : ∀ u, s < u → HasDerivAt (fun t => -h t) (w u) u := by
    intro u hu
    have hru : I.r ℓ < u := lt_of_le_of_lt hs hu
    have hga := (hg u hru.le).hasDerivAt (Ici_mem_nhds hru)
    have hg'a := (hg' u hru.le).hasDerivAt (Ici_mem_nhds hru)
    have h1 : HasDerivAt (fun t => t - s) 1 u := (hasDerivAt_id u).sub_const s
    have h3 : HasDerivAt (fun t => (t - s) * I.g' ℓ t) (1 * I.g' ℓ u + (u - s) * I.g'' ℓ u) u :=
      h1.mul hg'a
    have h4 : HasDerivAt (fun t => K * I.g ℓ t) (K * I.g' ℓ u) u := hga.const_mul K
    have h5 := (h3.sub h4).neg
    rw [hh, hw]
    beta_reduce
    exact h5.congr_deriv (by ring)
  have hcont : ∀ c d, s ≤ c → ContinuousOn h (Icc c d) := by
    intro c d hc t ht
    have hrt : I.r ℓ ≤ t := hs.trans (hc.trans ht.1)
    have c1 := (hg t hrt).continuousWithinAt
    have c2 := (hg' t hrt).continuousWithinAt
    have : ContinuousWithinAt h (Ici (I.r ℓ)) t := by
      rw [hh]
      exact ((continuousWithinAt_id.sub continuousWithinAt_const).mul c2).sub
        (continuousWithinAt_const.mul c1)
    exact this.mono (fun u hu => mem_Ici.2 (hs.trans (hc.trans hu.1)))
  have hint : ∀ c d, s ≤ c → IntegrableOn w (Icc c d) := by
    intro c d hc
    have h1 : IntegrableOn w (Ioc c d) := by
      apply intervalIntegral.integrableOn_deriv_of_nonneg ((hcont c d hc).neg)
      · intro u hu; exact hD u (lt_of_le_of_lt hc hu.1)
      · intro u hu; exact hwnn u (hc.trans hu.1.le)
    exact (integrableOn_Icc_iff_integrableOn_Ioc).2 h1
  refine ⟨hcont a b hsa, hint a b hsa, hwnn, ?_⟩
  intro t ht
  have htb : t ≤ b := ht.2
  have hst : s ≤ t := hsa.trans ht.1
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le htb ((hcont t b hst).neg)
    (fun u hu => hD u (lt_of_le_of_lt hst hu.1))
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le htb).2
      ((hint t b hst).mono_set Ioc_subset_Icc_self))
  rw [intervalIntegral.integral_of_le htb] at this
  rw [this]; simp only [Pi.neg_apply]; ring

end GFCSBilAux

namespace GFCSBilAux
open GenCostSched.GFCS

theorem gen {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (B : Finset (Fin m)) (ρ : Fin m → ℝ) (hB : ∀ j ∈ B, I.r j ≤ s)
    (y : Fin m → ℝ → ℝ) (hy : IsOffIntSched s B ρ y) (T : ℝ) (hsT : s ≤ T)
    (hT : ∀ j t, T < t → y j t = 0) :
    (∀ j, Integrable (fun t => I.g j t * y j t)) ∧
    (∀ j, Integrable (fun t => (t - s) * I.g' j t * y j t)) ∧
    (offCost I.g y).toReal = ∑ j, ∫ t, I.g j t * y j t := by
  have hfint := (BH_int I hI s B ρ hB y hy).2.2
  obtain ⟨y1, y2, y3, y4, y5, y6, _⟩ := hy
  have hy01 : ∀ j t, ‖y j t‖ ≤ 1 := by
    intro j t; rcases y2 j t with h | h <;> simp [h]
  have hout : ∀ j t, t ∉ Icc s T → y j t = 0 := by
    intro j t ht
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · exact y3 j t h
    · exact hT j t h
  have hgint : ∀ j, Integrable (fun t => I.g j t * y j t) := by
    intro j
    by_cases hj : j ∈ B
    · have hcont : ContinuousOn (I.g j) (Icc s T) := by
        intro t ht
        exact ((hI j).2.2.2.2.2 t ((hB j hj).trans ht.1)).continuousWithinAt.mono
          (fun u hu => mem_Ici.2 ((hB j hj).trans hu.1))
      have h1 := (hcont.integrableOn_Icc (μ := volume)).integrable_indicator measurableSet_Icc
      have h2 : Integrable (fun t => (Icc s T).indicator (I.g j) t * y j t) :=
        h1.mul_bdd (c := 1) (y1 j).aestronglyMeasurable (Filter.Eventually.of_forall (hy01 j))
      refine h2.congr (Filter.Eventually.of_forall (fun t => ?_))
      by_cases ht : t ∈ Icc s T
      · simp [indicator_of_mem ht]
      · simp [indicator_of_notMem ht, hout j t ht]
    · have : (fun t => I.g j t * y j t) = fun _ => 0 := by funext t; simp [y4 j hj t]
      rw [this]; exact integrable_zero _ _ _
  have hgnn : ∀ j t, 0 ≤ I.g j t * y j t := by
    intro j t
    rcases y2 j t with h | h
    · simp [h]
    · rw [h, mul_one]
      have hj : j ∈ B := by by_contra hc; rw [y4 j hc t] at h; exact zero_ne_one h
      have ht : s ≤ t := by by_contra hc; rw [y3 j t (lt_of_not_ge hc)] at h; exact zero_ne_one h
      exact (hI j).2.2.1 t ((hB j hj).trans ht)
  refine ⟨hgint, ?_, ?_⟩
  · intro j
    set c : ℝ → ℝ := (Icc s T).indicator (fun t => t - s) with hc
    have hcm : Measurable c := (measurable_id.sub measurable_const).indicator measurableSet_Icc
    have h1 : Integrable (fun t => c t * (I.g' j t * y j t)) := by
      refine (hfint j).bdd_mul (c := |T - s|) hcm.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun t => ?_)
      simp only [hc]
      by_cases h : t ∈ Icc s T
      · rw [indicator_of_mem h, Real.norm_eq_abs, abs_of_nonneg (by linarith [h.1]),
          abs_of_nonneg (by linarith)]
        linarith [h.2]
      · rw [indicator_of_notMem h]; simp
    refine h1.congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [hc]
    by_cases h : t ∈ Icc s T
    · rw [indicator_of_mem h]; ring
    · rw [indicator_of_notMem h, hout j t h]; simp
  · unfold offCost
    rw [ENNReal.toReal_sum (fun j _ => by
      rw [← ofReal_integral_eq_lintegral_ofReal (hgint j)
        (Filter.Eventually.of_forall (hgnn j))]; exact ENNReal.ofReal_ne_top)]
    apply Finset.sum_congr rfl
    intro j _
    rw [← ofReal_integral_eq_lintegral_ofReal (hgint j) (Filter.Eventually.of_forall (hgnn j)),
      ENNReal.toReal_ofReal (integral_nonneg (hgnn j))]

end GFCSBilAux

open GenCostSched.GFCS GFCSBilAux in
theorem solution {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j)
    (h2 : I.TwiceDiff) (K : ℝ) (hK : I.CurvBound K) (s : ℝ) (A : Finset (Fin m))
    (ρ : Fin m → ℝ) (k : Fin m) (hk : k ∉ A) (hA : ∀ j ∈ A, I.r j ≤ s) (hrk : I.r k = s)
    (hρ : ∀ j ∈ A, 0 < ρ j) (hρk : ρ k = I.v k) (x x' : Fin m → ℝ → ℝ)
    (hx : IsOptIntegral I.g s A ρ x) (hx' : IsOptIntegral I.g s (insert k A) ρ x')
    (hpost : postpones s A x x') :
    ∫ t in Ici s, (betaHat I.g' x' t - betaHat I.g' x t) ≤
      K * ((offCost I.g x').toReal - (offCost I.g x).toReal) := by
  have hA' : ∀ j ∈ insert k A, I.r j ≤ s := by
    intro j hj
    rcases Finset.mem_insert.1 hj with rfl | hj
    · exact hrk.le
    · exact hA j hj
  obtain ⟨x1, x2, x3, x4, x5, x6, ⟨Tx, hTx⟩⟩ := hx.1
  obtain ⟨x'1, x'2, x'3, x'4, x'5, x'6, ⟨Tx', hTx'⟩⟩ := hx'.1
  set T := max (max Tx Tx') s with hTdef
  have hsT : s ≤ T := le_max_right _ _
  have hT : ∀ j t, T < t → x j t = 0 := fun j t ht =>
    hTx j t (lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) ht)
  have hT' : ∀ j t, T < t → x' j t = 0 := fun j t ht =>
    hTx' j t (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) ht)
  have hout : ∀ j t, t ∉ Icc s T → x j t = 0 := by
    intro j t ht
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · exact x3 j t h
    · exact hT j t h
  have hout' : ∀ j t, t ∉ Icc s T → x' j t = 0 := by
    intro j t ht
    simp only [mem_Icc, not_and_or, not_le] at ht
    rcases ht with h | h
    · exact x'3 j t h
    · exact hT' j t h
  obtain ⟨gx, px, cx⟩ := gen I hI s A ρ hA x hx.1 T hsT hT
  obtain ⟨gx', px', cx'⟩ := gen I hI s (insert k A) ρ hA' x' hx'.1 T hsT hT'
  have BHx := BH_int I hI s A ρ hA x hx.1
  have BHx' := BH_int I hI s (insert k A) ρ hA' x' hx'.1
  rw [integral_sub BHx'.1 BHx.1, eq_24 I hI s (insert k A) ρ hA' x' hx'.1,
    eq_24 I hI s A ρ hA x hx.1, cx, cx']
  have hIci : ∀ (y : Fin m → ℝ → ℝ), (∀ j t, t < s → y j t = 0) → ∀ j,
      ∫ t in Ici s, (t - s) * I.g' j t * y j t = ∫ t, (t - s) * I.g' j t * y j t := by
    intro y hy j
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    simp [hy j t (lt_of_not_ge (fun h => ht (mem_Ici.2 h)))]
  simp_rw [hIci x x3, hIci x' x'3]
  have hrewr : ∀ (y : Fin m → ℝ → ℝ) j, Integrable (fun t => (t - s) * I.g' j t * y j t) →
      Integrable (fun t => I.g j t * y j t) →
      (∫ t, (t - s) * I.g' j t * y j t) - K * ∫ t, I.g j t * y j t =
        ∫ t, ((t - s) * I.g' j t - K * I.g j t) * y j t := by
    intro y j h1 h3
    rw [← integral_const_mul, ← integral_sub h1 (h3.const_mul K)]
    congr 1; funext t; ring
  have key : ∀ j, (∫ t, (t - s) * I.g' j t * x' j t) - K * ∫ t, I.g j t * x' j t ≤
      (∫ t, (t - s) * I.g' j t * x j t) - K * ∫ t, I.g j t * x j t := by
    intro j
    rw [hrewr x' j (px' j) (gx' j), hrewr x j (px j) (gx j)]
    set h : ℝ → ℝ := fun t => (t - s) * I.g' j t - K * I.g j t with hh
    set w : ℝ → ℝ := fun t => (K - 1) * I.g' j t - (t - s) * I.g'' j t with hw
    by_cases hjA : j ∈ A
    · obtain ⟨hc, hwi, hwnn, hrep⟩ := hprops I j (hI j) h2 K hK s (hA j hjA) h w hh hw s T le_rfl hsT
      have h01 : ∀ (y : Fin m → ℝ → ℝ), (∀ j t, y j t = 0 ∨ y j t = 1) → ∀ t, 0 ≤ y j t ∧ y j t ≤ 1 := by
        intro y hy t; rcases hy j t with h | h <;> simp [h]
      exact dom h w s T hwi (fun u hu => hwnn u hu.1) hc hrep (x j) (x' j) (x1 j) (x'1 j)
        (h01 x x2) (h01 x' x'2) (hout j) (hout' j)
        (by rw [x'6 j (Finset.mem_insert_of_mem hjA), x6 j hjA]) (hpost j hjA)
    · by_cases hjk : j = k
      · subst hjk
        have hx0 : ∀ t, x j t = 0 := x4 j hk
        simp only [hx0, mul_zero, integral_zero]
        apply integral_nonpos
        intro t
        simp only [Pi.zero_apply]
        rcases x'2 j t with h0 | h1
        · simp [h0]
        · rw [h1, mul_one]
          have hts : s ≤ t := by
            by_contra hc; rw [x'3 j t (lt_of_not_ge hc)] at h1; exact zero_ne_one h1
          obtain ⟨_, _, hwnn, hrep⟩ :=
            hprops I j (hI j) h2 K hK s hrk.le h w hh hw s t le_rfl hts
          have e := hrep s ⟨le_rfl, hts⟩
          have hnn : 0 ≤ ∫ u in Ioc s t, w u :=
            setIntegral_nonneg measurableSet_Ioc (fun u hu => hwnn u hu.1.le)
          have hs0 : h s = 0 := by
            simp only [hh, sub_self, zero_mul, zero_sub, neg_eq_zero, mul_eq_zero]
            right; rw [← hrk]; exact (hI j).2.2.2.2.1
          linarith
      · have hx0 : ∀ t, x j t = 0 := x4 j hjA
        have hx'0 : ∀ t, x' j t = 0 := x'4 j (by
          intro hh'; rcases Finset.mem_insert.1 hh' with h | h
          · exact hjk h
          · exact hjA h)
        simp [hx0, hx'0]
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => key j)
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  linarith
