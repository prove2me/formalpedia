-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.perron_integrand_continuous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:45:14.774852+00:00
-- url     : https://prove2.me/submissions/088a2535-7912-4a92-b9d7-59e30ccab979

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_Perron
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSgen
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronChi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology ArithmeticFunction
open scoped LSeries.notation
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
variable {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {y : ℝ} (hy : 0 < y) {σ₀ : ℝ} (hσ : 1 < σ₀) :
    Continuous (fun t : ℝ => Fchi χ y ((σ₀ : ℂ) + t * I)) := by
  have hU : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hz : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 1 < s.re} := fun s hs =>
    (DirichletCharacter.differentiableAt_LFunction χ s
      (Or.inl (by rintro rfl; simp at hs))).differentiableWithinAt
  have hdz : ContinuousOn (deriv (DirichletCharacter.LFunction χ)) {s : ℂ | 1 < s.re} :=
    (hz.deriv hU).continuousOn
  have hline : Continuous (fun t : ℝ => (σ₀ : ℂ) + t * I) := by fun_prop
  have hmem : ∀ t : ℝ, (σ₀ : ℂ) + t * I ∈ {s : ℂ | 1 < s.re} := by intro t; simp [hσ]
  have c1 : Continuous (fun t : ℝ => deriv (DirichletCharacter.LFunction χ) ((σ₀ : ℂ) + t * I)) :=
    hdz.comp_continuous hline hmem
  have c2 : Continuous (fun t : ℝ => DirichletCharacter.LFunction χ ((σ₀ : ℂ) + t * I)) :=
    hz.continuousOn.comp_continuous hline hmem
  have hne : ∀ t : ℝ, DirichletCharacter.LFunction χ ((σ₀ : ℂ) + t * I) ≠ 0 := fun t => by
    have h1 : 1 < ((σ₀ : ℂ) + t * I).re := by simp [hσ]
    rw [DirichletCharacter.LFunction_eq_LSeries χ h1]
    exact DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ h1
  have c3 : Continuous (fun t : ℝ => (y : ℂ) ^ ((σ₀ : ℂ) + t * I)) :=
    hline.const_cpow (Or.inl (by exact_mod_cast hy.ne'))
  have hw0 : ∀ t : ℝ, ((σ₀ : ℂ) + t * I) * ((σ₀ : ℂ) + t * I - 1) ≠ 0 := by
    intro t
    apply mul_ne_zero
    · intro h; have := congrArg Complex.re h; simp at this; linarith
    · intro h; have := congrArg Complex.re h; simp at this; linarith
  unfold Fchi negLD
  exact ((c1.div c2 hne).neg.mul c3).div (hline.mul (hline.sub continuous_const)) hw0
end Formalism.ZeroFreeDirichlet
