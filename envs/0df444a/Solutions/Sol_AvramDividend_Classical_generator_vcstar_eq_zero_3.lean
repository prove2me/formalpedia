-- Prove2me | solution 3 for AvramDividend.Classical.generator_vcstar_eq_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:08:28.490215+00:00
-- url     : https://prove2.me/submissions/a3b4f21c-12b7-43a5-923d-64da945b7fe8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_interior_harmonicity_of_scale_harmonicity
import Theorems.Thm_AvramDividend_Classical_generator_eq_of_agree_below
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-!
Avram, Lemma 4: `(Γ v_{c*} - q v_{c*})(x) = 0` on `(0, c*)`.

Route.  On `(0, c*)` the barrier value agrees with the scaled q-scale function
below the cap, and the spectrally negative generator is local on the downward
ray, so the conclusion is equivalent to scale-function q-harmonicity there.
The transfer is carried out by the Proved theorem
`vcstar_interior_harmonicity_of_scale_harmonicity`, whose input is
`X.GeneratorIntegrable W x` and `X.generator W x - q * W x = 0` on
`Ioo 0 (cstar W).toReal`.  That input is exactly the conclusion of
`scaleFunction_generator_q_harmonic_of_nonzero_factor`.

Three cases are separated.

* `cstar W = ⊤`.  Then `(cstar W).toReal = 0`, so `Ioo 0 (cstar W).toReal` is
  empty and the statement is vacuous.  The hypotheses do not exclude `⊤`, so
  this case must be discharged explicitly.

* `deriv W (cstar W).toReal = 0`.  The barrier normaliser `scaleDeriv W a` is
  then zero, so the barrier value vanishes identically on `(-∞, a]`; both the
  generator and the generator domain are then trivial at every `x ∈ Ioo 0 a`.
  This branch is closed using only Proved results.

* `deriv W (cstar W).toReal ≠ 0`.  The barrier normalisation factor
  `divE 1 (scaleDeriv W a)` is then non-zero and scale-function q-harmonicity
  is exactly the content of `scaleFunction_generator_q_harmonic_of_nonzero_factor`.
-/

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioo 0 (cstar W).toReal))
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by
  have hne_zero : cstar W ≠ 0 := ne_of_gt hc
  by_cases htop : cstar W = ⊤
  · intro x hx
    have htop_toReal : (cstar W).toReal = 0 := by
      rw [htop]
      exact ENNReal.toReal_top
    have hx' : x ∈ Ioo (0 : ℝ) 0 := by
      have hx' := hx
      rw [htop_toReal] at hx'
      exact hx'
    obtain ⟨h1, h2⟩ := Set.mem_Ioo.mp hx'
    exact (lt_irrefl 0 (h1.trans h2)).elim
  · have ha : 0 < (cstar W).toReal := ENNReal.toReal_pos hne_zero htop
    have ha0 : (cstar W).toReal ≠ 0 := ne_of_gt ha
    have hsd : scaleDeriv W (cstar W).toReal =
        ((deriv W (cstar W).toReal : ℝ) : EReal) := by
      simp [scaleDeriv, ha0]
    have hsd_ne_top : scaleDeriv W (cstar W).toReal ≠ ⊤ := by
      rw [hsd]
      exact EReal.coe_ne_top _
    have hsd_toReal : (scaleDeriv W (cstar W).toReal).toReal =
        deriv W (cstar W).toReal := by
      rw [hsd]
      exact EReal.toReal_coe _
    have hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) =
        (deriv W (cstar W).toReal)⁻¹ := by
      rw [divE, if_neg hsd_ne_top, hsd_toReal, one_div]
    by_cases hder : deriv W (cstar W).toReal = 0
    · have hu (z : ℝ) : divE (W z) (scaleDeriv W (cstar W).toReal) = 0 := by
        rw [divE, if_neg hsd_ne_top, hsd_toReal, hder, div_zero]
      have hagree0 : ∀ z : ℝ, z < (cstar W).toReal → vcstar W z = 0 := by
        intro z hz
        have hval := vcstar_eq_scaledW_le_cstar_of_support
          W hW.1 z (le_of_lt hz)
        rw [hval, hu z]
      intro x hx
      have hlocal :=
        generator_eq_of_agree_below X (vcstar W) (fun _ : ℝ => (0 : ℝ))
          (cstar W).toReal x hx.2 hagree0
      refine ⟨hlocal.1.mpr ?_, ?_⟩
      · change IntegrableOn
          (SpectrallyNegativeLevy.generatorIntegrand (fun _ : ℝ => (0 : ℝ)) x)
          (Iio (0 : ℝ)) X.ν
        have hzero_integrand :
            SpectrallyNegativeLevy.generatorIntegrand (fun _ : ℝ => (0 : ℝ)) x =
              (fun _ : ℝ => (0 : ℝ)) := by
          funext y
          simp [SpectrallyNegativeLevy.generatorIntegrand]
        rw [hzero_integrand]
        exact integrableOn_zero
      · rw [hlocal.2]
        have hgen0 : X.generator (fun _ : ℝ => (0 : ℝ)) x = 0 := by
          simp [SpectrallyNegativeLevy.generator,
            SpectrallyNegativeLevy.generatorIntegrand, iteratedDeriv_const]
        rw [hgen0, hagree0 x hx.2]
        ring
    · have hk0 : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0 := by
        rw [hk]
        intro h
        exact hder (inv_eq_zero.mp h)
      have hscale :=
        scaleFunction_generator_q_harmonic_of_nonzero_factor
          X hX q hq W hW h_smooth hc hk0
      exact vcstar_interior_harmonicity_of_scale_harmonicity
        X q W hW ha hscale
