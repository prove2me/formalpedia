-- Prove2me | solution 1 for GenCostSched.GFCS.eq_24
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T13:48:54.246458+00:00
-- url     : https://prove2.me/submissions/9b05ea96-81fd-486b-b3e6-2377a05b297c

import Mathlib
import Definitions.Def_GenCostSched_GFCS_Model

open MeasureTheory Set
open scoped ENNReal

namespace GFCSEq24Aux
open GenCostSched.GFCS

variable {n : ℕ}

theorem mem_aliveOld {I : Instance n} {y : Fin n → ℝ → ℝ} {k j : Fin n} :
    j ∈ I.aliveOld y k ↔ j < k ∧ 0 < I.residual y k j := by
  simp [Instance.aliveOld]

theorem tailFrom_of_le {m : ℕ} {s t : ℝ} (x : Fin m → ℝ → ℝ) (j : Fin m) (h : s ≤ t) :
    tailFrom s x j t = x j t := by
  simp [tailFrom, indicator_of_mem (mem_Ici.2 h)]

theorem tailFrom_of_lt {m : ℕ} {s t : ℝ} (x : Fin m → ℝ → ℝ) (j : Fin m) (h : t < s) :
    tailFrom s x j t = 0 := by
  simp [tailFrom, indicator_of_notMem (show t ∉ Ici s from fun h' => absurd (mem_Ici.1 h') (not_le.2 h))]

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


/-- Tonelli for the tail integral: `∫_s^∞ ∫_{(t,∞)} f = ∫_s^∞ (t - s) f(t)` for a nonnegative
integrable `f` vanishing outside `[s, T]`. -/
theorem tail_fubini (f : ℝ → ℝ) (hf : Integrable f) (hnn : ∀ t, 0 ≤ f t) (s T : ℝ)
    (hlo : ∀ t, t < s → f t = 0) (hhi : ∀ t, T < t → f t = 0) :
    IntegrableOn (fun t => ∫ τ in Ioi t, f τ) (Ici s) ∧
      ∫ t in Ici s, (∫ τ in Ioi t, f τ) = ∫ t in Ici s, (t - s) * f t := by
  set φ : ℝ → ℝ := fun t => ∫ τ in Ioi t, f τ with hφ
  have hanti : Antitone φ := by
    intro t t' htt
    apply setIntegral_mono_set hf.integrableOn
    · exact Filter.Eventually.of_forall (fun τ => hnn τ)
    · exact (Ioi_subset_Ioi htt).eventuallyLE
  have hφnn : ∀ t, 0 ≤ φ t := fun t => setIntegral_nonneg measurableSet_Ioi (fun τ _ => hnn τ)
  have hφz : ∀ t, T ≤ t → φ t = 0 := by
    intro t ht
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro τ hτ; exact hhi τ (lt_of_le_of_lt ht hτ)
  have hφint : IntegrableOn φ (Ici s) := by
    have hbd : IntegrableOn φ (Icc s T) := by
      refine Measure.integrableOn_of_bounded (M := φ s) (by simp)
        hanti.measurable.aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall (fun t ht => ?_))
      rw [Real.norm_of_nonneg (hφnn t)]
      exact hanti ht.1
    refine hbd.of_forall_sdiff_eq_zero measurableSet_Ici ?_
    intro t ht
    apply hφz
    by_contra hc
    exact ht.2 ⟨mem_Ici.1 ht.1, le_of_not_ge hc⟩
  refine ⟨hφint, ?_⟩
  -- the right side is integrable
  set c : ℝ → ℝ := fun t => if t ∈ Icc s T then t - s else 0 with hc
  have hcm : Measurable c := by
    apply Measurable.ite measurableSet_Icc (measurable_id.sub measurable_const) measurable_const
  have hRint : Integrable (fun t => (t - s) * f t) := by
    have h1 : Integrable (fun t => c t * f t) := by
      refine hf.bdd_mul (c := |T - s|) hcm.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun t => ?_)
      simp only [hc]
      split_ifs with h
      · rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [h.1]), abs_of_nonneg (by linarith [h.1, h.2])]
        linarith [h.2]
      · simp
    refine h1.congr (Filter.Eventually.of_forall (fun t => ?_))
    simp only [hc]
    split_ifs with h
    · rfl
    · simp only [mem_Icc, not_and_or, not_le] at h
      rcases h with h | h
      · simp [hlo t h]
      · simp [hhi t h]
  have hRnn : ∀ t ∈ Ici s, 0 ≤ (t - s) * f t := fun t ht =>
    mul_nonneg (by linarith [mem_Ici.1 ht]) (hnn t)
  -- compare in ℝ≥0∞
  set F : ℝ → ℝ≥0∞ := fun τ => ENNReal.ofReal (f τ) with hF
  have hFm : AEMeasurable F := hf.aemeasurable.ennreal_ofReal
  have hL : ENNReal.ofReal (∫ t in Ici s, φ t) = ∫⁻ t in Ici s, ∫⁻ τ in Ioi t, F τ := by
    rw [ofReal_integral_eq_lintegral_ofReal hφint
      (Filter.Eventually.of_forall (fun t => hφnn t))]
    apply setLIntegral_congr_fun measurableSet_Ici
    intro t _
    exact ofReal_integral_eq_lintegral_ofReal hf.integrableOn
      (Filter.Eventually.of_forall (fun τ => hnn τ))
  have hR : ENNReal.ofReal (∫ t in Ici s, (t - s) * f t) =
      ∫⁻ τ, F τ * ENNReal.ofReal (τ - s) := by
    rw [ofReal_integral_eq_lintegral_ofReal hRint.integrableOn
      ((ae_restrict_iff' measurableSet_Ici).2 (Filter.Eventually.of_forall hRnn)),
      ← lintegral_indicator measurableSet_Ici]
    congr 1; funext τ
    by_cases h : s ≤ τ
    · rw [indicator_of_mem (mem_Ici.2 h), ENNReal.ofReal_mul (by linarith), mul_comm]
    · rw [indicator_of_notMem (fun h' => h (mem_Ici.1 h'))]
      simp [hF, hlo τ (lt_of_not_ge h)]
  set G : ℝ → ℝ → ℝ≥0∞ := fun t τ =>
    ({p : ℝ × ℝ | s ≤ p.1 ∧ p.1 < p.2}).indicator (fun p => F p.2) (t, τ) with hG
  have hGm : AEMeasurable (Function.uncurry G) (volume.prod volume) := by
    have hS : MeasurableSet {p : ℝ × ℝ | s ≤ p.1 ∧ p.1 < p.2} :=
      (measurableSet_le measurable_const measurable_fst).inter
        (measurableSet_lt measurable_fst measurable_snd)
    have : Function.uncurry G =
        ({p : ℝ × ℝ | s ≤ p.1 ∧ p.1 < p.2}).indicator (fun p => F p.2) := by
      funext p; simp [hG, Function.uncurry]
    rw [this]
    exact (hFm.comp_snd).indicator hS
  have hswap : ∫⁻ t in Ici s, ∫⁻ τ in Ioi t, F τ = ∫⁻ τ, F τ * ENNReal.ofReal (τ - s) := by
    have e1 : ∫⁻ t in Ici s, ∫⁻ τ in Ioi t, F τ = ∫⁻ t, ∫⁻ τ, G t τ := by
      rw [← lintegral_indicator measurableSet_Ici]
      congr 1; funext t
      by_cases h : s ≤ t
      · rw [indicator_of_mem (mem_Ici.2 h), ← lintegral_indicator measurableSet_Ioi]
        congr 1; funext τ
        by_cases h' : t < τ
        · simp [hG, h, h']
        · simp [hG, h, h']
      · rw [indicator_of_notMem (fun h' => h (mem_Ici.1 h'))]
        symm
        simp [hG, h]
    rw [e1, lintegral_lintegral_swap hGm]
    congr 1; funext τ
    have : (fun t => G t τ) = (Ico s τ).indicator (fun _ => F τ) := by
      funext t
      by_cases h : s ≤ t ∧ t < τ
      · rw [indicator_of_mem (show t ∈ Ico s τ from h)]; simp [hG, h]
      · rw [indicator_of_notMem (show t ∉ Ico s τ from h)]; simp [hG, h]
    rw [this, lintegral_indicator_const measurableSet_Ico, Real.volume_Ico, mul_comm]
  rw [hswap] at hL
  have := hL.trans hR.symm
  exact (ENNReal.ofReal_eq_ofReal_iff (setIntegral_nonneg measurableSet_Ici (fun t _ => hφnn t))
    (setIntegral_nonneg measurableSet_Ici hRnn)).1 this

end GFCSEq24Aux

open GenCostSched.GFCS GFCSEq24Aux in
theorem solution {m : ℕ} (I : Instance m) (hI : ∀ j, I.JobStanding j) (s : ℝ)
    (A : Finset (Fin m)) (ρ : Fin m → ℝ) (hA : ∀ j ∈ A, I.r j ≤ s)
    (x : Fin m → ℝ → ℝ) (hx : IsOffIntSched s A ρ x) :
    ∫ t in Ici s, betaHat I.g' x t = ∑ ℓ, ∫ t in Ici s, (t - s) * I.g' ℓ t * x ℓ t := by
  have hint := (BH_int I hI s A ρ hA x hx).2.2
  obtain ⟨x1, x2, x3, x4, x5, x6, ⟨T, hT⟩⟩ := hx
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
  have hTF := fun ℓ => tail_fubini (fun τ => I.g' ℓ τ * x ℓ τ) (hint ℓ) (hfnn ℓ) s T
    (fun t ht => by simp [x3 ℓ t ht]) (fun t ht => by simp [hT ℓ t ht])
  unfold betaHat
  rw [integral_finset_sum _ (fun ℓ _ => (hTF ℓ).1)]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [(hTF ℓ).2]
  congr 1; funext t; ring
