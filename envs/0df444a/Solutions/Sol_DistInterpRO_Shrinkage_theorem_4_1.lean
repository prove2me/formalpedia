-- Prove2me | solution 1 for DistInterpRO.Shrinkage.theorem_4_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:36:59.648013+00:00
-- url     : https://prove2.me/submissions/98479618-582b-43d4-abc3-9c99017e3923

import Mathlib
import Definitions.Def_DistInterpRO_Shrinkage_Model

open MeasureTheory
open scoped Pointwise

namespace DistInterpRO.Shrinkage

theorem aux_t41_taylor {m : ℕ} {F : EuclideanSpace ℝ (Fin m) → ℝ} {h : ℝ}
    (hF : HasBoundedHessian F h) (x y : EuclideanSpace ℝ (Fin m)) :
    |F (x + y) - F x - fderiv ℝ F x y| ≤ h / 2 * ‖y‖ ^ 2 := by
  obtain ⟨hF1, hF2, hF3⟩ := hF
  set K := h * ‖y‖ ^ 2 with hK
  have hl : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x + t • y) y t := by
    intro t
    simpa using ((hasDerivAt_id t).smul_const y).const_add x
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => F (x + t • y)) (fderiv ℝ F (x + t • y) y) t := by
    intro t
    exact (hF1 (x + t • y)).hasFDerivAt.comp_hasDerivAt t (hl t)
  have hg1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => fderiv ℝ F (x + t • y) y)
      (fderiv ℝ (fderiv ℝ F) (x + t • y) y y) t := by
    intro t
    have h1 := (hF2 (x + t • y)).hasFDerivAt.comp_hasDerivAt t (hl t)
    have h2 := h1.clm_apply (hasDerivAt_const t y)
    simpa using h2
  -- Step A
  have hA : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖fderiv ℝ F (x + t • y) y - fderiv ℝ F (x + (0:ℝ) • y) y‖
      ≤ K * (t - 0) := by
    refine norm_image_sub_le_of_norm_deriv_le_segment'
      (f := fun t : ℝ => fderiv ℝ F (x + t • y) y) (fun t _ => (hg1 t).hasDerivWithinAt) ?_
    intro t _
    simpa [Real.norm_eq_abs] using hF3 (x + t • y) y
  -- Step B
  have hφ : ∀ t : ℝ, HasDerivAt (fun t : ℝ => F (x + t • y) - F x - t * fderiv ℝ F x y)
      (fderiv ℝ F (x + t • y) y - fderiv ℝ F x y) t := by
    intro t
    exact ((hg t).sub_const (F x)).sub (hasDerivAt_mul_const (fderiv ℝ F x y))
  have hB := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (f := fun t : ℝ => F (x + t • y) - F x - t * fderiv ℝ F x y)
    (f' := fun t : ℝ => fderiv ℝ F (x + t • y) y - fderiv ℝ F x y)
    (a := 0) (b := 1) (B := fun t : ℝ => K / 2 * t ^ 2) (B' := fun t => K * t)
    (fun t _ => (hφ t).continuousAt.continuousWithinAt) (fun t _ => (hφ t).hasDerivWithinAt)
    (by simp) ?_ ?_ (x := 1) (by simp)
  · calc |F (x + y) - F x - fderiv ℝ F x y| ≤ K / 2 := by simpa using hB
      _ = h / 2 * ‖y‖ ^ 2 := by rw [hK]; ring
  · intro t
    have := (hasDerivAt_pow 2 t).const_mul (K / 2)
    refine this.congr_deriv ?_
    rw [show (2:ℕ) - 1 = 1 from rfl]
    push_cast
    ring
  · intro t ht
    have := hA t (Set.Ico_subset_Icc_self ht)
    simpa using this

theorem aux_t41_integrable {m : ℕ} {F : EuclideanSpace ℝ (Fin m) → ℝ} (hFc : Continuous F)
    {x₀ : EuclideanSpace ℝ (Fin m)} {Δ : Set (EuclideanSpace ℝ (Fin m))} (hΔc : IsCompact Δ)
    {p : ℝ} {μ : Measure (EuclideanSpace ℝ (Fin m))} (hμ : μ ∈ scenarioSet x₀ Δ p) :
    Integrable F μ ∧ ∀ᵐ x ∂μ, x ∈ (fun x => x₀ + x) '' Δ := by
  obtain ⟨hprob, -, hS1⟩ := hμ
  have hS : IsCompact ((fun x => x₀ + x) '' Δ) :=
    hΔc.image (continuous_const.add continuous_id)
  have hcompl : μ ((fun x => x₀ + x) '' Δ)ᶜ = 0 :=
    (prob_compl_eq_zero_iff hS.isClosed.measurableSet).mpr hS1
  have hae : ∀ᵐ x ∂μ, x ∈ (fun x => x₀ + x) '' Δ := by
    rw [ae_iff]; exact hcompl
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hFc.continuousOn
  exact ⟨Integrable.mono' (integrable_const M) hFc.aestronglyMeasurable
    (hae.mono fun x hx => hM x hx), hae⟩

theorem aux_t41_intlb {m : ℕ} {F : EuclideanSpace ℝ (Fin m) → ℝ} (hFc : Continuous F)
    {x₀ : EuclideanSpace ℝ (Fin m)} {Δ : Set (EuclideanSpace ℝ (Fin m))} (hΔc : IsCompact Δ)
    {α : ℝ} (hα1 : α < 1) {k : ℝ} (hk : k ≤ 0)
    (hpt : ∀ x ∈ (fun x => x₀ + x) '' Δ, x ≠ x₀ → F x₀ + k ≤ F x)
    {μ : Measure (EuclideanSpace ℝ (Fin m))} (hμ : μ ∈ scenarioSet x₀ Δ (1 - α)) :
    F x₀ + α * k ≤ ∫ x, F x ∂μ := by
  obtain ⟨hint, hae⟩ := aux_t41_integrable hFc hΔc hμ
  obtain ⟨hprob, hx₀, -⟩ := hμ
  have hr : 1 - α ≤ μ.real {x₀} := by
    have := ENNReal.toReal_mono (measure_ne_top μ _) hx₀
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  set ℓ : EuclideanSpace ℝ (Fin m) → ℝ :=
    fun x => (F x₀ + k) - k * ({x₀} : Set (EuclideanSpace ℝ (Fin m))).indicator 1 x with hℓ
  have hind : Integrable (({x₀} : Set (EuclideanSpace ℝ (Fin m))).indicator
      (1 : EuclideanSpace ℝ (Fin m) → ℝ)) μ :=
    (integrable_const (1:ℝ)).indicator (measurableSet_singleton x₀)
  have hℓint : Integrable ℓ μ := (integrable_const _).sub (hind.const_mul k)
  have hℓval : ∫ x, ℓ x ∂μ = F x₀ + k - k * μ.real {x₀} := by
    rw [hℓ, integral_sub (integrable_const _) (hind.const_mul k), integral_const,
      integral_const_mul, integral_indicator_one (measurableSet_singleton x₀)]
    simp
  have hle : ∫ x, ℓ x ∂μ ≤ ∫ x, F x ∂μ := by
    refine integral_mono_ae hℓint hint ?_
    filter_upwards [hae] with x hx
    by_cases hxx : x = x₀
    · subst hxx; simp [hℓ]
    · have := hpt x hx hxx
      simp only [hℓ]
      rw [Set.indicator_of_notMem (show x ∉ ({x₀} : Set _) from hxx)]
      linarith
  rw [hℓval] at hle
  nlinarith [mul_nonneg_of_nonpos_of_nonpos hk (by linarith : 1 - μ.real {x₀} - α ≤ 0)]

end DistInterpRO.Shrinkage

open DistInterpRO.Shrinkage

theorem solution {m : ℕ} {V : Type*} (f : V → EuclideanSpace ℝ (Fin m) → ℝ)
    (x₀ : EuclideanSpace ℝ (Fin m)) (Δ : Set (EuclideanSpace ℝ (Fin m))) (hΔc : IsCompact Δ)
    (hΔ0 : (0 : EuclideanSpace ℝ (Fin m)) ∈ Δ)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (h : ℝ) (hh : 0 ≤ h) (hf : ∀ v, HasBoundedHessian (f v) h) :
    ∀ v : V,
      (∃ x ∈ α • Δ, ∀ y ∈ α • Δ, f v (x₀ + x) ≤ f v (x₀ + y)) ∧
      drspValue (f v) x₀ Δ (1 - α) - α * devRadius Δ ^ 2 * h ≤
        (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ∧
      (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), f v (x₀ + x)) ≤
        drspValue (f v) x₀ Δ (1 - α) + α * devRadius Δ ^ 2 * h := by
  intro v
  have hF := hf v
  set F := f v with hFdef
  have hFc : Continuous F := hF.1.continuous
  have hT := aux_t41_taylor hF
  set D := devRadius Δ with hD
  have hbdd : BddAbove ((fun x => ‖x‖) '' Δ) := (hΔc.image continuous_norm).bddAbove
  have hnormD : ∀ y ∈ Δ, ‖y‖ ≤ D := fun y hy => le_csSup hbdd (Set.mem_image_of_mem _ hy)
  have hD0 : 0 ≤ D := by simpa using hnormD 0 hΔ0
  have hsqD : ∀ y ∈ Δ, ‖y‖ ^ 2 ≤ D ^ 2 := fun y hy =>
    pow_le_pow_left₀ (norm_nonneg y) (hnormD y hy) 2
  -- minimizer over αΔ
  have hαΔc : IsCompact (α • Δ) := hΔc.smul α
  have h0αΔ : (0 : EuclideanSpace ℝ (Fin m)) ∈ α • Δ := ⟨0, hΔ0, smul_zero α⟩
  obtain ⟨xs, hxs, hxsmin⟩ := hαΔc.exists_isMinOn ⟨0, h0αΔ⟩
    (hFc.comp (continuous_const.add continuous_id)).continuousOn
  have hmin : ∀ y ∈ α • Δ, F (x₀ + xs) ≤ F (x₀ + y) := fun y hy => hxsmin hy
  have hinf : (⨅ x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))), F (x₀ + x)) = F (x₀ + xs) := by
    have : Nonempty (α • Δ : Set (EuclideanSpace ℝ (Fin m))) := ⟨⟨xs, hxs⟩⟩
    have hb : BddBelow (Set.range fun x : (α • Δ : Set (EuclideanSpace ℝ (Fin m))) =>
        F (x₀ + x)) := by
      refine ⟨F (x₀ + xs), ?_⟩
      rintro _ ⟨x, rfl⟩
      exact hmin x x.2
    apply le_antisymm
    · exact ciInf_le hb ⟨xs, hxs⟩
    · exact le_ciInf fun x => hmin x x.2
  refine ⟨⟨xs, hxs, hmin⟩, ?_⟩
  rw [hinf]
  obtain ⟨ys, hys, rfl⟩ := Set.mem_smul_set.mp hxs
  -- linear minimizer
  set L := fderiv ℝ F x₀ with hL
  obtain ⟨yc, hyc, hycmin⟩ := hΔc.exists_isMinOn ⟨0, hΔ0⟩ L.continuous.continuousOn
  have hcle : ∀ y ∈ Δ, L yc ≤ L y := fun y hy => hycmin hy
  have hc0 : L yc ≤ 0 := by simpa using hcle 0 hΔ0
  set k := L yc - h / 2 * D ^ 2 with hk
  have hk0 : k ≤ 0 := by nlinarith
  have hpt : ∀ x ∈ (fun x => x₀ + x) '' Δ, x ≠ x₀ → F x₀ + k ≤ F x := by
    rintro _ ⟨y, hy, rfl⟩ _
    have h1 := (abs_le.mp (hT x₀ y)).1
    have h2 := hcle y hy
    have h3 := hsqD y hy
    have h4 : h / 2 * ‖y‖ ^ 2 ≤ h / 2 * D ^ 2 := mul_le_mul_of_nonneg_left h3 (by linarith)
    simp only
    linarith
  have hlb : ∀ μ ∈ scenarioSet x₀ Δ (1 - α), F x₀ + α * k ≤ ∫ x, F x ∂μ :=
    fun μ hμ => aux_t41_intlb hFc hΔc hα1 hk0 hpt hμ
  -- the two-point measure
  have hx₀S : x₀ ∈ (fun x => x₀ + x) '' Δ := ⟨0, hΔ0, add_zero x₀⟩
  have hysS : x₀ + ys ∈ (fun x => x₀ + x) '' Δ := ⟨ys, hys, rfl⟩
  set μ₂ : Measure (EuclideanSpace ℝ (Fin m)) :=
    ENNReal.ofReal (1 - α) • Measure.dirac x₀ + ENNReal.ofReal α • Measure.dirac (x₀ + ys)
    with hμ₂
  have hsum : ENNReal.ofReal (1 - α) + ENNReal.ofReal α = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hα0.le, sub_add_cancel, ENNReal.ofReal_one]
  have hμ₂mem : μ₂ ∈ scenarioSet x₀ Δ (1 - α) := by
    refine ⟨⟨?_⟩, ?_, ?_⟩
    · simp [hμ₂, hsum]
    · simp only [hμ₂, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply_of_mem (Set.mem_singleton x₀), mul_one]
      exact le_self_add
    · simp only [hμ₂, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
        Measure.dirac_apply_of_mem hx₀S, Measure.dirac_apply_of_mem hysS, mul_one]
      exact hsum
  have : Nonempty (scenarioSet x₀ Δ (1 - α)) := ⟨⟨μ₂, hμ₂mem⟩⟩
  have hbddb : BddBelow (Set.range fun μ : scenarioSet x₀ Δ (1 - α) =>
      ∫ x, F x ∂(μ : Measure (EuclideanSpace ℝ (Fin m)))) := by
    refine ⟨F x₀ + α * k, ?_⟩
    rintro _ ⟨μ, rfl⟩
    exact hlb μ μ.2
  have hint₂ := (aux_t41_integrable hFc hΔc hμ₂mem).1
  have hval₂ : ∫ x, F x ∂μ₂ = (1 - α) * F x₀ + α * F (x₀ + ys) := by
    rw [hμ₂, integral_add_measure hint₂.left_of_add_measure hint₂.right_of_add_measure,
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
      ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hα0.le]
    simp [smul_eq_mul]
  have hN := hsqD ys hys
  have hN0 := sq_nonneg ‖ys‖
  have hαs : α ^ 2 ≤ α := by nlinarith
  have hsmul_norm : ‖α • ys‖ ^ 2 = α ^ 2 * ‖ys‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα0]; ring
  have hLs : ∀ y, L (α • y) = α * L y := fun y => by rw [map_smul, smul_eq_mul]
  have e1 : α ^ 2 * ‖ys‖ ^ 2 ≤ α * D ^ 2 := by
    calc α ^ 2 * ‖ys‖ ^ 2 ≤ α * ‖ys‖ ^ 2 := mul_le_mul_of_nonneg_right hαs hN0
      _ ≤ α * D ^ 2 := mul_le_mul_of_nonneg_left hN hα0.le
  refine ⟨?_, ?_⟩
  · -- lower bound
    have hdr : drspValue F x₀ Δ (1 - α) ≤ ∫ x, F x ∂μ₂ :=
      ciInf_le hbddb ⟨μ₂, hμ₂mem⟩
    rw [hval₂] at hdr
    have t1 := (abs_le.mp (hT x₀ ys)).2
    have t2 := (abs_le.mp (hT x₀ (α • ys))).1
    rw [hsmul_norm, hLs] at t2
    have e2 : h * (α ^ 2 * ‖ys‖ ^ 2) ≤ h * (α * D ^ 2) := mul_le_mul_of_nonneg_left e1 hh
    have e3 : h * (α * ‖ys‖ ^ 2) ≤ h * (α * D ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN hα0.le) hh
    nlinarith
  · -- upper bound
    have hαyc : α • yc ∈ α • Δ := Set.smul_mem_smul_set hyc
    have hup : ∀ μ ∈ scenarioSet x₀ Δ (1 - α),
        F (x₀ + α • yc) - α * D ^ 2 * h ≤ ∫ x, F x ∂μ := by
      intro μ hμ
      have i1 := hlb μ hμ
      have t2 := (abs_le.mp (hT x₀ (α • yc))).2
      have hN' := hsqD yc hyc
      have hsn : ‖α • yc‖ ^ 2 = α ^ 2 * ‖yc‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα0]; ring
      rw [hsn, hLs] at t2
      have e1' : α ^ 2 * ‖yc‖ ^ 2 ≤ α * D ^ 2 :=
        calc α ^ 2 * ‖yc‖ ^ 2 ≤ α * ‖yc‖ ^ 2 := mul_le_mul_of_nonneg_right hαs (sq_nonneg _)
          _ ≤ α * D ^ 2 := mul_le_mul_of_nonneg_left hN' hα0.le
      have e2 : h * (α ^ 2 * ‖yc‖ ^ 2) ≤ h * (α * D ^ 2) := mul_le_mul_of_nonneg_left e1' hh
      rw [hk] at i1
      nlinarith
    have : F (x₀ + α • ys) - α * D ^ 2 * h ≤ drspValue F x₀ Δ (1 - α) :=
      le_ciInf fun μ => le_trans (by linarith [hmin _ hαyc]) (hup μ μ.2)
    linarith
