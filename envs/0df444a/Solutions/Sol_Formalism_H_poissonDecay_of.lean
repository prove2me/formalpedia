-- Prove2me | solution 1 for Formalism.H.poissonDecay_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:19.739224+00:00
-- url     : https://prove2.me/submissions/e2061632-ccf4-425a-9ad9-1d68fed558ec

import Definitions.Def_Formalism_LatticeTheta_LatticeSummableDecay
import Definitions.Def_Formalism_LatticeTheta_LatticeThetaProofs_Assembly
import Theorems.Thm_Formalism_H_norm_exp_two_pi_I_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Asymptotics Complex
open scoped FourierTransform RealInnerProductSpace SchwartzMap
noncomputable section
open Formalism Formalism.H
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace Formalism.H
theorem _root_.solution (hD : DualIsLattice V) (h1 : LatticeSummableDecay V)
    (h2 : Periodization V) (h3 : UnfoldCoeff V) (h4 : LatticeFourierSeries V) : PoissonDecay V := by
  intro Λ _ _ f hf b hb hfO hFO x
  obtain ⟨hdd, hdz⟩ := hD Λ
  haveI := hdd
  haveI : IsZLattice ℝ (dual Λ) := hdz

  have hphase : (fun v : V => (𝓕 f : V → ℂ) v * Complex.exp (2 * Real.pi * Complex.I * (⟪v, x⟫ : ℝ)))
      =O[cocompact V] (fun v => ‖v‖ ^ (-b)) := by
    refine (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun v => ?_)).trans hFO
    rw [norm_mul, norm_exp_two_pi_I_mul, mul_one, one_mul]
  have hsum := h1 (dual Λ) _ b hb hphase
  refine ⟨hsum, ?_⟩
  obtain ⟨hint, hper, hcont, hinv⟩ := h2 Λ f hf b hb hfO

  let B := Module.Free.chooseBasis ℤ Λ
  have hD' := ZLattice.isAddFundamentalDomain B (volume : Measure V)
  have hcoef : ∀ μ : dual Λ,
      ∫ y in ZSpan.fundamentalDomain (B.ofZLatticeBasis ℝ Λ), (∑' l : Λ, f ((l : V) + y)) *
        Complex.exp (-(2 * Real.pi * Complex.I * (⟪(μ : V), y⟫ : ℝ))) = (𝓕 f : V → ℂ) μ :=
    fun μ => h3 Λ f hint _ hD' μ μ.2
  have hFs : Summable (fun μ : dual Λ => (𝓕 f : V → ℂ) μ) := h1 (dual Λ) _ b hb hFO
  have hG := h4 Λ (fun y => ∑' l : Λ, f ((l : V) + y)) hcont
    (fun l y => by simpa using hinv l y) _ hD' (by simpa only [hcoef] using hFs) x
  simp only [hcoef] at hG
  have hval : (ZLattice.covolume Λ : ℂ)⁻¹ * ∑' μ : dual Λ, (𝓕 f : V → ℂ) μ *
      Complex.exp (2 * Real.pi * Complex.I * (⟪(μ : V), x⟫ : ℝ)) = ∑' l : Λ, f ((l : V) + x) := by
    rw [← tsum_mul_left, ← hG.tsum_eq]
    congr 1; funext μ; ring
  rw [hval]
  exact (hper x).hasSum
end Formalism.H
