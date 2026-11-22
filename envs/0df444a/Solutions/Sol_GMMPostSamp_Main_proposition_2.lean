-- Prove2me | solution 1 for GMMPostSamp.Main.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-22T19:49:46.91766+00:00
-- url     : https://prove2.me/submissions/7834fd00-9b8b-411b-a5a6-8dc11bb657e0

import Mathlib

open MeasureTheory ProbabilityTheory

theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (m : Ω → Ω → ℝ) (hm : Measurable fun p : Ω × Ω => m p.1 p.2)
    (hm_self : ∀ ω, m ω ω = 0) (hm_symm : ∀ ω ω', m ω ω' = m ω' ω)
    (hm_tri : ∀ ω ω' ω'', m ω ω'' ≤ m ω ω' + m ω' ω'')
    (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (π : Measure Ω) [IsProbabilityMeasure π] (F : Kernel Ω Ω') [IsMarkovKernel F]
    (A : Kernel Ω' Ω) [IsMarkovKernel A]
    (hA : ((π ⊗ₘ F) ⊗ₘ A.comap Prod.snd measurable_snd) {p | ε < m p.2 p.1.1} ≤
      ENNReal.ofReal δ)
    (post : Kernel Ω' Ω) [IsMarkovKernel post]
    (hpost : (π ⊗ₘ F).map Prod.swap = (F ∘ₘ π) ⊗ₘ post) :
    ((π ⊗ₘ F) ⊗ₘ post.comap Prod.snd measurable_snd) {p | 2 * ε < m p.2 p.1.1} ≤
      ENNReal.ofReal (2 * δ) := by
  set μ := π ⊗ₘ F with hμ
  -- measurable sets
  have hE1 : MeasurableSet {p : (Ω × Ω') × Ω | ε < m p.2 p.1.1} :=
    measurableSet_lt measurable_const
      (hm.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
  have hT : MeasurableSet {p : (Ω × Ω') × Ω | 2 * ε < m p.2 p.1.1} :=
    measurableSet_lt measurable_const
      (hm.comp (measurable_snd.prodMk (measurable_fst.comp measurable_fst)))
  have hD : MeasurableSet {q : Ω × Ω | ε < m q.1 q.2} :=
    measurableSet_lt measurable_const hm
  -- h and g
  set h : Ω × Ω' → ENNReal := fun x => A x.2 {a | ε < m a x.1} with hh
  set g : Ω' → ENNReal := fun φ => (A ×ₖ post) φ {q : Ω × Ω | ε < m q.1 q.2} with hg
  have hh_meas : Measurable h := by
    have := Kernel.measurable_kernel_prodMk_left (κ := A.comap Prod.snd measurable_snd) hE1
    exact this
  have hg_meas : Measurable g := Kernel.measurable_coe _ hD
  have hA' : ∫⁻ x, h x ∂μ ≤ ENNReal.ofReal δ := by
    rw [Measure.compProd_apply hE1] at hA
    exact hA
  have hT' : (μ ⊗ₘ post.comap Prod.snd measurable_snd) {p | 2 * ε < m p.2 p.1.1} =
      ∫⁻ x, post x.2 {w | 2 * ε < m w x.1} ∂μ := by
    rw [Measure.compProd_apply hT]
    rfl
  have hg1 : ∀ φ, g φ = ∫⁻ a, post φ {w | ε < m a w} ∂A φ := by
    intro φ
    simp only [hg, Kernel.prod_apply]
    rw [Measure.prod_apply hD]
    rfl
  have hg2 : ∀ φ, g φ = ∫⁻ w, A φ {a | ε < m a w} ∂post φ := by
    intro φ
    simp only [hg, Kernel.prod_apply]
    rw [Measure.prod_apply_symm hD]
    rfl
  -- pointwise bound
  have hpt : ∀ x : Ω × Ω', post x.2 {w | 2 * ε < m w x.1} ≤ g x.2 + h x := by
    intro x
    have hmeasA : MeasurableSet {a | ε < m a x.1} :=
      measurableSet_lt measurable_const (hm.comp (measurable_id.prodMk measurable_const))
    calc post x.2 {w | 2 * ε < m w x.1}
        = ∫⁻ _a, post x.2 {w | 2 * ε < m w x.1} ∂A x.2 := by
          rw [lintegral_const, measure_univ, mul_one]
      _ ≤ ∫⁻ a, (post x.2 {w | ε < m a w} + {a | ε < m a x.1}.indicator 1 a) ∂A x.2 := by
          apply lintegral_mono
          intro a
          dsimp only
          by_cases ha : ε < m a x.1
          · rw [Set.indicator_of_mem (s := {a | ε < m a x.1}) ha]
            exact le_add_left (by simpa using prob_le_one)
          · rw [Set.indicator_of_notMem (s := {a | ε < m a x.1}) ha]
            refine le_add_right (measure_mono ?_)
            intro w hw
            simp only [Set.mem_setOf_eq] at hw ⊢
            have h1 := hm_tri w a x.1
            rw [hm_symm w a] at h1
            push_neg at ha
            linarith
      _ = g x.2 + h x := by
          rw [lintegral_add_right _ (measurable_one.indicator hmeasA),
            lintegral_indicator_one hmeasA, hg1]
  -- integral of g ∘ snd equals integral of h
  have hgh : ∫⁻ x, g x.2 ∂μ = ∫⁻ x, h x ∂μ := by
    have e1 : ∫⁻ x, g x.2 ∂μ = ∫⁻ φ, g φ ∂(F ∘ₘ π) := by
      rw [← Measure.snd_compProd π F, Measure.snd, lintegral_map hg_meas measurable_snd]
    have hhs : Measurable fun y : Ω' × Ω => h y.swap := hh_meas.comp measurable_swap
    have e2 : ∫⁻ x, h x ∂μ = ∫⁻ y, h y.swap ∂((F ∘ₘ π) ⊗ₘ post) := by
      rw [← hpost, lintegral_map hhs measurable_swap]
      rfl
    rw [e1, e2, Measure.lintegral_compProd hhs]
    refine lintegral_congr fun φ => ?_
    rw [hg2]
    rfl
  calc (μ ⊗ₘ post.comap Prod.snd measurable_snd) {p | 2 * ε < m p.2 p.1.1}
      = ∫⁻ x, post x.2 {w | 2 * ε < m w x.1} ∂μ := hT'
    _ ≤ ∫⁻ x, (g x.2 + h x) ∂μ := lintegral_mono hpt
    _ = ∫⁻ x, g x.2 ∂μ + ∫⁻ x, h x ∂μ := lintegral_add_right _ hh_meas
    _ ≤ ENNReal.ofReal δ + ENNReal.ofReal δ := by
          rw [hgh]; exact add_le_add hA' hA'
    _ = ENNReal.ofReal (2 * δ) := by
          rw [← ENNReal.ofReal_add hδ0.le hδ0.le]; ring_nf
