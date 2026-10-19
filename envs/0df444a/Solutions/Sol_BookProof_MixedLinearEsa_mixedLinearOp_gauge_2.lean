-- Prove2me | solution 2 for BookProof.MixedLinearEsa.mixedLinearOp_gauge
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T06:46:59.914427+00:00
-- url     : https://prove2.me/submissions/1ef7ac7e-277e-4cdd-98d1-697ec4c8aea2

import Definitions.Def_ChapterStrichartzWave
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterMixedLinearEsa
import Definitions.Def_ChapterFourierMultiplierEsa
import Theorems.Thm_BookProof_MixedLinearEsa_hasDerivAt_gaugePhase_line
import Theorems.Thm_BookProof_MixedLinearEsa_hasDerivAt_phaseFun_line
-- Generated from ChapterMixedLinearEsa.lean — theorem BookProof.MixedLinearEsa.mixedLinearOp_gauge
open BookProof.FourierMultiplierEsa
open BookProof.MixedLinearEsa



open MeasureTheory SchwartzMap FourierTransform ComplexInnerProductSpace LineDeriv
open BookProof.StrichartzWave BookProof.FourierMultiplierEsa BookProof.FarisLavine

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
theorem h44_lineF {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (ψ : V → F) (x m : V) (hψ : DifferentiableAt ℝ ψ x) :
    HasDerivAt (fun t : ℝ => ψ (x + t • m)) (fderiv ℝ ψ x m) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => x + t • m) m 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const m).const_add x
  have hψ0 : DifferentiableAt ℝ ψ (x + (0:ℝ) • m) := by simpa using hψ
  have h2 := hψ0.hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
  simp only [zero_smul, add_zero] at h2
  exact h2

theorem solution (b m : V) (hm : m ≠ 0) (φ : 𝓢(V, ℂ))
    (hφ : HasCompactSupport (φ : V → ℂ)) (x : V) :
    (mixedLinearOp b m (gaugeSchwartz b m φ hφ)) x
      = gaugeFun b m x * (momentumOp m φ x) := by
  have hg : Function.HasTemperateGrowth (fun x : V => ((inner ℝ x b : ℝ) : ℂ)) :=
    (Complex.ofRealCLM.comp ((innerSL ℝ).flip b)).hasTemperateGrowth
  have hG : HasDerivAt (fun t : ℝ => gaugeFun b m (x + t • m))
      (gaugeFun b m x * (Complex.I * ((-(inner ℝ x b : ℝ) : ℝ) : ℂ))) 0 :=
    BookProof.MixedLinearEsa.hasDerivAt_phaseFun_line (W := fun x => (inner ℝ x b : ℝ))
      (BookProof.MixedLinearEsa.hasDerivAt_gaugePhase_line b m hm) x
  have hφ' := h44_lineF (φ : V → ℂ) x m (φ.differentiableAt)
  have hψ := h44_lineF ((gaugeSchwartz b m φ hφ : 𝓢(V, ℂ)) : V → ℂ) x m
    ((gaugeSchwartz b m φ hφ).differentiableAt)
  have hprod := hG.mul hφ'
  have hcoe : ∀ y, (gaugeSchwartz b m φ hφ : V → ℂ) y = gaugeFun b m y * φ y := fun y => rfl
  have hfun : (fun t : ℝ => (gaugeSchwartz b m φ hφ : V → ℂ) (x + t • m))
      = (fun t : ℝ => gaugeFun b m (x + t • m) * φ (x + t • m)) := by
    funext t; exact hcoe _
  rw [hfun] at hψ
  have hu := hψ.unique hprod
  simp only [zero_smul, add_zero] at hu
  simp only [mixedLinearOp, posOp, momentumOp, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, lineDerivOpCLM_apply,
    SchwartzMap.lineDerivOp_apply_eq_fderiv, smul_eq_mul,
    SchwartzMap.smulLeftCLM_apply_apply hg]
  rw [hu, hcoe]
  push_cast
  linear_combination (gaugeFun b m x * φ x * ((inner ℝ x b : ℝ) : ℂ)) * Complex.I_sq

