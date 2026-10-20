-- Prove2me | solution 1 for BookProof.ScalaronDensitized.multOp_quadForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T17:50:41.890852+00:00
-- url     : https://prove2.me/submissions/42ffb225-e139-4e59-8448-d263e9544194

-- Generated from ChapterScalaronDensitizedTransfer.lean — theorem BookProof.ScalaronDensitized.multOp_quadForm_eq
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFockContinuum
open BookProof.ChapterLinftyMultiplication
open BookProof.NavierStokesFlow.FockContinuum
open BookProof.ScalaronDensitized



open MeasureTheory Set Filter Topology
open BookProof.Starobinsky BookProof.QuantumGravityDensitized
open BookProof.QuantumGravityHalfDensity
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockContinuum
open BookProof.FarisLavine BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.EsaClosure

noncomputable section

variable (M alpha : ℝ)
variable {X : Type*} [MeasurableSpace X]
open BookProof.ScalaronDensitized in
theorem solution (mu : Measure X) {g : X → ℝ} (hg : Measurable g)
    (f : boundedEnergyCore mu g) :
    quadForm ((boundedEnergyCore mu g).subtype.comp (multOp mu hg)) f
      = ∫ a, g a * ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2 ∂mu := by
  unfold quadForm
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [MeasureTheory.L2.inner_def]
  have h : ∀ᵐ a ∂mu, inner ℂ (((f : Lp ℂ 2 mu) : X → ℂ) a)
      ((((multOp mu hg f : boundedEnergyCore mu g) : Lp ℂ 2 mu)) a)
        = ((g a * ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2 : ℝ) : ℂ) := by
    have hc : (((multOp mu hg f : boundedEnergyCore mu g) : Lp ℂ 2 mu) : X → ℂ)
        =ᵐ[mu] fun x => (g x : ℂ) * ((f : Lp ℂ 2 mu) : X → ℂ) x :=
      (memLp_mul hg f.2).coeFn_toLp
    filter_upwards [hc] with a ha
    rw [ha]
    simp only [RCLike.inner_apply]
    rw [mul_assoc, Complex.mul_conj']
    push_cast
    ring
  rw [integral_congr_ae h, integral_complex_ofReal, Complex.ofReal_re]
