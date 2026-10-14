-- Prove2me | solution 1 for DbarRegularity.homogeneousSingularIntegral_lp
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T19:43:32.365486+00:00
-- url     : https://prove2.me/submissions/296562c3-268c-48e5-a209-4b243daa6bfa

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Theorems.Thm_DbarRegularity_truncatedSingularIntegral_lp
import Theorems.Thm_DbarRegularity_continuousOn_compl_zero_of_dini
import Theorems.Thm_DbarRegularity_exists_norm_le_of_dini
import Theorems.Thm_DbarRegularity_setIntegral_annulus_div_norm_pow_eq_zero
import Theorems.Thm_DbarRegularity_hormander_div_norm_pow_of_dini
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2



namespace DbarRegularity

open MeasureTheory Metric Filter Topology Set
open scoped ENNReal NNReal ContDiff

theorem homogeneousSingularIntegral_lp_aux {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hmean : ∫ x : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, Ω x ∂(volume.toSphere) = 0)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0,
      (∀ ε : ℝ, 0 < ε → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y in {y | ε ≤ ‖y‖}, Ω y / ((‖y‖ ^ d : ℝ) : ℂ) * f (x - y))
            (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume) ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        ∃ g : EuclideanSpace ℝ (Fin d) → ℂ, MemLp g (ENNReal.ofReal p) volume ∧
          Tendsto (fun ε : ℝ => eLpNorm
              ((fun x => ∫ y in {y | ε ≤ ‖y‖}, Ω y / ((‖y‖ ^ d : ℝ) : ℂ) * f (x - y)) - g)
              (ENNReal.ofReal p) volume)
            (𝓝[>] 0) (𝓝 0) ∧
          eLpNorm g (ENNReal.ofReal p) volume ≤ A * eLpNorm f (ENNReal.ofReal p) volume := by
  set K : EuclideanSpace ℝ (Fin d) → ℂ := fun y => Ω y / ((‖y‖ ^ d : ℝ) : ℂ) with hKdef
  have hcomm : ∀ (f : EuclideanSpace ℝ (Fin d) → ℂ) (ε : ℝ),
      (fun x => ∫ y in {y | ε ≤ ‖y‖}, Ω y / ((‖y‖ ^ d : ℝ) : ℂ) * f (x - y)) =
        fun x => ∫ y in {y | ε ≤ ‖y‖}, f (x - y) * K y := by
    intro f ε; funext x; congr 1; funext y; rw [mul_comm]
  obtain ⟨M, hM⟩ := exists_norm_le_of_dini Ω hhom hdini
  have hK3 : ∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0 :=
    fun R₁ R₂ h₁ _ => setIntegral_annulus_div_norm_pow_eq_zero Ω hhom hmean R₁ R₂ h₁
  -- the kernel data
  have hdata : ∃ B : ℝ, AEStronglyMeasurable K volume ∧ (∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ d) ∧
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B) := by
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · refine ⟨0, ?_, fun x hx => absurd (Subsingleton.elim x 0) hx,
        fun y hy => absurd (Subsingleton.elim y 0) hy⟩
      have : K = fun _ => K 0 := by funext x; rw [Subsingleton.elim x 0]
      rw [this]; exact aestronglyMeasurable_const
    obtain ⟨H, hH⟩ := hormander_div_norm_pow_of_dini hd Ω hhom hdini M hM
    refine ⟨max M H, ?_, fun x hx => ?_, fun y hy => (hH y hy).trans ?_⟩
    · have hc : ContinuousOn K {0}ᶜ := by
        refine (continuousOn_compl_zero_of_dini Ω hhom hdini).div ?_ ?_
        · exact (Complex.continuous_ofReal.comp (continuous_norm.pow d)).continuousOn
        · intro x hx
          have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
          exact_mod_cast pow_ne_zero d this
      have h1 := hc.aestronglyMeasurable (μ := volume) (measurableSet_singleton 0).compl
      haveI : NeZero d := ⟨hd.ne'⟩
      rwa [restrict_compl_singleton] at h1
    · have hx0 : 0 < ‖x‖ ^ d := pow_pos (norm_pos_iff.mpr hx) d
      simp only [hKdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
      exact div_le_div_of_nonneg_right ((hM x).trans (le_max_left _ _)) hx0.le
    · exact ENNReal.ofReal_le_ofReal (le_max_right _ _)
  obtain ⟨B, hKm, hK1, hK2⟩ := hdata
  obtain ⟨A, hA1, hA2⟩ := truncatedSingularIntegral_lp K B hKm hK1 hK2 hK3 p hp
  refine ⟨A, fun ε hε f hf => ?_, fun f hf => ?_⟩
  · rw [hcomm f ε]; exact hA1 ε hε f hf
  · obtain ⟨g, hg, hT, hgA⟩ := hA2 f hf
    refine ⟨g, hg, ?_, hgA⟩
    simpa only [hcomm f] using hT

end DbarRegularity

open DbarRegularity

open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal ContDiff

theorem solution {d : ℕ} (Ω : EuclideanSpace ℝ (Fin d) → ℂ)
    (hhom : ∀ x, ∀ t : ℝ, 0 < t → Ω (t • x) = Ω x)
    (hmean : ∫ x : sphere (0 : EuclideanSpace ℝ (Fin d)) 1, Ω x ∂(volume.toSphere) = 0)
    (hdini : ∫⁻ δ in Set.Ioc (0 : ℝ) 1,
      (⨆ (x : EuclideanSpace ℝ (Fin d)) (x' : EuclideanSpace ℝ (Fin d)) (_ : ‖x‖ = 1)
        (_ : ‖x'‖ = 1) (_ : ‖x - x'‖ ≤ δ), ‖Ω x - Ω x'‖ₑ) / ENNReal.ofReal δ < ⊤)
    (p : ℝ) (hp : 1 < p) :
    ∃ A : ℝ≥0,
      (∀ ε : ℝ, 0 < ε → ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        eLpNorm (fun x => ∫ y in {y | ε ≤ ‖y‖}, Ω y / ((‖y‖ ^ d : ℝ) : ℂ) * f (x - y))
            (ENNReal.ofReal p) volume
          ≤ A * eLpNorm f (ENNReal.ofReal p) volume) ∧
      ∀ f : EuclideanSpace ℝ (Fin d) → ℂ, MemLp f (ENNReal.ofReal p) volume →
        ∃ g : EuclideanSpace ℝ (Fin d) → ℂ, MemLp g (ENNReal.ofReal p) volume ∧
          Tendsto (fun ε : ℝ => eLpNorm
              ((fun x => ∫ y in {y | ε ≤ ‖y‖}, Ω y / ((‖y‖ ^ d : ℝ) : ℂ) * f (x - y)) - g)
              (ENNReal.ofReal p) volume)
            (𝓝[>] 0) (𝓝 0) ∧
          eLpNorm g (ENNReal.ofReal p) volume ≤ A * eLpNorm f (ENNReal.ofReal p) volume :=
  homogeneousSingularIntegral_lp_aux Ω hhom hmean hdini p hp
