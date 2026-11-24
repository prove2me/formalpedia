-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B1.intZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:38:34.198468+00:00
-- url     : https://prove2.me/submissions/56ec5587-e70f-4541-99be-a2ccc6497e2c

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralZeroFrequencyInvariant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B1
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
namespace Formalism.FourierDecayAlt.P.B1
theorem _root_.solution : IntRdZeroInv := by
  intro n μ _ X h hinv hC1 hI hRI
  set E : ℝ → Matrix (Fin n) (Fin n) ℂ := fun t => NormedSpace.exp ((t : ℂ) • X) with hE
  have hEcont : Continuous E := by
    letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
    letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
    letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
    have h1 : Continuous fun t : ℝ => ((t : ℂ) • X) := by fun_prop
    exact NormedSpace.exp_continuous.comp h1
  have hEadd : ∀ s t : ℝ, E (s + t) = E s * E t := by
    intro s t
    simp only [hE]
    rw [← Matrix.exp_add_of_commute]
    · congr 1; push_cast; rw [add_smul]
    · exact ((Commute.refl X).smul_left _).smul_right _
  have hE0 : E 0 = 1 := by simp [hE]
  set k : (Fin n → Fin n → ℂ) → ℂ := fun g => RdV X h (Matrix.of g) with hk
  set Ψ : (Fin n → Fin n → ℂ) × ℝ → (Fin n → Fin n → ℂ) := fun p => rmulF (E p.2) p.1 with hΨd
  have hΨc : Continuous Ψ := by
    have : Continuous fun p : (Fin n → Fin n → ℂ) × ℝ => (Matrix.of p.1 : Matrix (Fin n) (Fin n) ℂ) * E p.2 :=
      Continuous.matrix_mul continuous_fst (hEcont.comp continuous_snd)
    exact this
  have hΨ : Measurable Ψ := hΨc.measurable
  have hR : ∀ s : ℝ, Measurable (rmulF (E s)) := fun s => hΨ.comp measurable_prodMk_right
  set ν : Measure ℝ := volume.restrict (Set.Ioc 0 1) with hν
  have hq : Measure.QuasiMeasurePreserving Ψ (μ.prod ν) μ := by
    refine ⟨hΨ, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
    rw [Measure.map_apply hΨ hs, Measure.prod_apply_symm (hΨ hs)]
    have : ∀ y : ℝ, μ ((fun x => (x, y)) ⁻¹' (Ψ ⁻¹' s)) = 0 := by
      intro y
      have e : (fun x => (x, y)) ⁻¹' (Ψ ⁻¹' s) = rmulF (E y) ⁻¹' s := rfl
      rw [e, ← Measure.map_apply (hR y) hs, hinv y, h0]
    simp [this]
  have hkR : ∀ s : ℝ, Integrable (fun g => k (rmulF (E s) g)) μ := by
    intro s
    have : Integrable k (μ.map (rmulF (E s))) := by rw [hinv s]; exact hRI
    exact this.comp_measurable (hR s)
  have hkI : ∀ s : ℝ, (∫ g, k (rmulF (E s) g) ∂μ) = ∫ g, k g ∂μ := by
    intro s
    have hm : AEStronglyMeasurable k (μ.map (rmulF (E s))) := by rw [hinv s]; exact hRI.1
    rw [← integral_map (hR s).aemeasurable hm, hinv s]
  have hkN : ∀ s : ℝ, (∫ g, ‖k (rmulF (E s) g)‖ ∂μ) = ∫ g, ‖k g‖ ∂μ := by
    intro s
    have hm : AEStronglyMeasurable (fun g => ‖k g‖) (μ.map (rmulF (E s))) := by rw [hinv s]; exact hRI.1.norm
    rw [← integral_map (hR s).aemeasurable hm, hinv s]
  have hint : Integrable (fun p => k (Ψ p)) (μ.prod ν) := by
    have hm : AEStronglyMeasurable (fun p => k (Ψ p)) (μ.prod ν) := hRI.1.comp_quasiMeasurePreserving hq
    rw [integrable_prod_iff' hm]
    refine ⟨Filter.Eventually.of_forall fun s => hkR s, ?_⟩
    have : (fun y : ℝ => ∫ x, ‖k (Ψ (x, y))‖ ∂μ) = fun _ => ∫ g, ‖k g‖ ∂μ := by
      funext y; exact hkN y
    rw [this]
    exact integrable_const _
  have hswap := integral_integral_swap (f := fun g s => k (Ψ (g, s))) (μ := μ) (ν := ν) hint
  have hrhs : (∫ s, ∫ g, k (Ψ (g, s)) ∂μ ∂ν) = ∫ g, k g ∂μ := by
    have : (fun s : ℝ => ∫ g, k (Ψ (g, s)) ∂μ) = fun _ => ∫ g, k g ∂μ := by
      funext s; exact hkI s
    rw [this]
    simp [hν]
  have hftc : ∀ᵐ g ∂μ, (∫ s, k (Ψ (g, s)) ∂ν) = h (Matrix.of (rmulF (E 1) g)) - h (Matrix.of g) := by
    filter_upwards [hC1] with g hg
    set φ : ℝ → ℂ := fun t => h (Matrix.of g * E t) with hφ
    have hd : ∀ s, deriv φ s = k (Ψ (g, s)) := by
      intro s
      have e1 : k (Ψ (g, s)) = deriv (fun t : ℝ => φ (s + t)) 0 := by
        simp only [hk, RdV, hΨd, hφ]
        congr 1
        funext t
        rw [hEadd, ← mul_assoc]
        rfl
      rw [e1, deriv_comp_const_add, add_zero]
    have hf := intervalIntegral.integral_deriv_eq_sub (f := φ) (a := 0) (b := 1)
      (fun x _ => (hg.differentiable (by norm_num)) x)
      ((hg.continuous_deriv (le_refl _)).intervalIntegrable _ _)
    rw [intervalIntegral.integral_of_le zero_le_one] at hf
    have e2 : (∫ s, k (Ψ (g, s)) ∂ν) = ∫ s in Set.Ioc 0 1, deriv φ s := by
      rw [hν]; congr 1; funext s; exact (hd s).symm
    rw [e2, hf]
    simp only [hφ, hE0, mul_one]
    rfl
  have hhI : (∫ g, h (Matrix.of (rmulF (E 1) g)) ∂μ) = ∫ g, h (Matrix.of g) ∂μ := by
    have hm : AEStronglyMeasurable (fun g => h (Matrix.of g)) (μ.map (rmulF (E 1))) := by rw [hinv 1]; exact hI.1
    rw [← integral_map (hR 1).aemeasurable hm, hinv 1]
  have hhR : Integrable (fun g => h (Matrix.of (rmulF (E 1) g))) μ := by
    have : Integrable (fun g => h (Matrix.of g)) (μ.map (rmulF (E 1))) := by rw [hinv 1]; exact hI
    exact this.comp_measurable (hR 1)
  have hl : (∫ g, ∫ s, k (Ψ (g, s)) ∂ν ∂μ) = 0 := by
    rw [integral_congr_ae hftc, integral_sub hhR hI, hhI, sub_self]
  rw [← hrhs, ← hswap, hl]
end Formalism.FourierDecayAlt.P.B1
