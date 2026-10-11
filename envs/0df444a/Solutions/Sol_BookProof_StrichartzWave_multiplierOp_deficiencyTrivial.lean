-- Prove2me | solution 1 for BookProof.StrichartzWave.multiplierOp_deficiencyTrivial
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:27:38.535187+00:00
-- url     : https://prove2.me/submissions/98b14edc-0d8c-4291-a052-0ca2e8cf5f29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.multiplierOp_deficiencyTrivial
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_integral_conj_mul_multiplier_sub_eq_zero
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (m : V → ℝ) (hm : Function.HasTemperateGrowth m)
    {z : ℂ} (hz : z.im ≠ 0) :
    BookProof.FarisLavine.DeficiencyTrivialAt (schwartzDomain V) (opL2 (multiplierOp m)) z := by

  intro u hu
  have hmsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m := hm.1
  have hz1 : ∀ x : V, ((m x : ℝ) : ℂ) - (starRingEnd ℂ) z ≠ 0 := by
    intro x hx
    exact hz (by simpa using congrArg Complex.im hx)
  have hz2 : ∀ x : V, ((m x : ℝ) : ℂ) - z ≠ 0 := by
    intro x hx
    exact hz (by simpa using congrArg Complex.im hx)
  have main : ∀ χ : V → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ →
      ∫ x, χ x • ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x) = 0 := by
    intro χ hχ hχc
    have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => (χ x : ℂ) * (((m x : ℝ) : ℂ) - (starRingEnd ℂ) z)⁻¹) := by
      refine (Complex.ofRealCLM.contDiff.comp hχ).mul (ContDiff.inv ?_ hz1)
      exact (Complex.ofRealCLM.contDiff.comp hmsmooth).sub contDiff_const
    have hsupp : HasCompactSupport
        (fun x => (χ x : ℂ) * (((m x : ℝ) : ℂ) - (starRingEnd ℂ) z)⁻¹) := by
      refine HasCompactSupport.mul_right ?_
      exact hχc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    obtain ⟨ψ, hψcoe⟩ : ∃ ψ : 𝓢(V, ℂ), (ψ : V → ℂ) =
        fun x => (χ x : ℂ) * (((m x : ℝ) : ℂ) - (starRingEnd ℂ) z)⁻¹ :=
      ⟨hsupp.toSchwartzMap hsmooth, rfl⟩
    have key := integral_conj_mul_multiplier_sub_eq_zero m hm z u hu ψ
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hpx : ψ x = (χ x : ℂ) * (((m x : ℝ) : ℂ) - (starRingEnd ℂ) z)⁻¹ := congrFun hψcoe x
    have hc : (starRingEnd ℂ) (ψ x) * (((m x : ℝ) : ℂ) - z) = (χ x : ℂ) := by
      rw [hpx]
      simp only [map_mul, map_inv₀, map_sub, Complex.conj_ofReal, Complex.conj_conj]
      field_simp
      exact mul_div_cancel_right₀ _ (hz2 x)
    change χ x • ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x)
      = (starRingEnd ℂ) (ψ x) * (((m x : ℝ) : ℂ) - z) *
        ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x)
    rw [Complex.real_smul, ← hc]
  have hgloc : LocallyIntegrable
      (fun x => ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x : ℂ)) (volume : Measure V) :=
    (Lp.memLp (𝓕 u : Lp ℂ 2 (volume : Measure V))).locallyIntegrable (by norm_num)
  have hae : ∀ᵐ x ∂(volume : Measure V), ((𝓕 u : Lp ℂ 2 (volume : Measure V)) x : ℂ) = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hgloc (fun χ hχ hχc => main χ hχ hχc)
  have hg0 : (𝓕 u : Lp ℂ 2 (volume : Measure V)) = 0 := Lp.eq_zero_iff_ae_eq_zero.mpr hae
  have hnorm : ‖u‖ = 0 := by
    rw [← MeasureTheory.Lp.norm_fourier_eq u, hg0, norm_zero]
  exact norm_eq_zero.mp hnorm
