-- Prove2me | solution 1 for BookProof.StrichartzWave.potentialOp_deficiencyTrivial
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T11:26:00.026172+00:00
-- url     : https://prove2.me/submissions/b4094a77-c1dc-46b8-8334-3478127564c9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterWaveUnboundedPotential.lean — solution of BookProof.StrichartzWave.potentialOp_deficiencyTrivial
import Mathlib
import Definitions.Def_ChapterWaveUnboundedPotential
import Theorems.Thm_BookProof_StrichartzWave_integral_conj_mul_potential_sub_eq_zero
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterStrichartzWave
open BookProof.StrichartzWave




open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace ENNReal

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

set_option maxHeartbeats 1000000 in
theorem solution (W : V → ℝ) (hW : Function.HasTemperateGrowth W)
    {z : ℂ} (hz : z.im ≠ 0) :
    BookProof.FarisLavine.DeficiencyTrivialAt (schwartzDomain V) (opL2 (potentialOp W)) z := by

  intro u hu
  have hWsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W := hW.1
  have hz1 : ∀ x : V, ((W x : ℝ) : ℂ) - (starRingEnd ℂ) z ≠ 0 := by
    intro x hx
    exact hz (by simpa using congrArg Complex.im hx)
  have hz2 : ∀ x : V, ((W x : ℝ) : ℂ) - z ≠ 0 := by
    intro x hx
    exact hz (by simpa using congrArg Complex.im hx)
  have main : ∀ χ : V → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ → HasCompactSupport χ →
      ∫ x, χ x • (u x) = 0 := by
    intro χ hχ hχc
    have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x => (χ x : ℂ) * (((W x : ℝ) : ℂ) - (starRingEnd ℂ) z)⁻¹) := by
      refine (Complex.ofRealCLM.contDiff.comp hχ).mul (ContDiff.inv ?_ hz1)
      exact (Complex.ofRealCLM.contDiff.comp hWsmooth).sub contDiff_const
    have hsupp : HasCompactSupport
        (fun x => (χ x : ℂ) * (((W x : ℝ) : ℂ) - (starRingEnd ℂ) z)⁻¹) := by
      refine HasCompactSupport.mul_right ?_
      exact hχc.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    obtain ⟨ψ, hψcoe⟩ : ∃ ψ : 𝓢(V, ℂ), (ψ : V → ℂ) =
        fun x => (χ x : ℂ) * (((W x : ℝ) : ℂ) - (starRingEnd ℂ) z)⁻¹ :=
      ⟨hsupp.toSchwartzMap hsmooth, rfl⟩
    have key := integral_conj_mul_potential_sub_eq_zero W hW z u hu ψ
    rw [← key]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    have hpx : ψ x = (χ x : ℂ) * (((W x : ℝ) : ℂ) - (starRingEnd ℂ) z)⁻¹ := congrFun hψcoe x
    have hc : (starRingEnd ℂ) (ψ x) * (((W x : ℝ) : ℂ) - z) = (χ x : ℂ) := by
      rw [hpx]
      simp only [map_mul, map_inv₀, map_sub, Complex.conj_ofReal, Complex.conj_conj]
      field_simp
      exact mul_div_cancel_right₀ _ (hz2 x)
    change χ x • (u x) = (starRingEnd ℂ) (ψ x) * (((W x : ℝ) : ℂ) - z) * (u x)
    rw [Complex.real_smul, ← hc]
  have hloc : LocallyIntegrable (fun x => (u x : ℂ)) (volume : Measure V) :=
    (Lp.memLp u).locallyIntegrable (by norm_num)
  have hae : ∀ᵐ x ∂(volume : Measure V), (u x : ℂ) = 0 :=
    ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun χ hχ hχc => main χ hχ hχc)
  exact Lp.eq_zero_iff_ae_eq_zero.mpr hae
