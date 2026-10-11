-- Prove2me | solution 1 for BookProof.ScalaronDensitized.multOp_quadForm_ge
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:07:44.402049+00:00
-- url     : https://prove2.me/submissions/c3895ba6-e9a5-4920-a90d-9c4653899daf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterScalaronDensitizedTransfer.lean — solution of BookProof.ScalaronDensitized.multOp_quadForm_ge
import Mathlib
import Definitions.Def_ChapterScalaronDensitizedTransfer
import Theorems.Thm_BookProof_ScalaronDensitized_integral_norm_sq_eq_norm_sq
import Theorems.Thm_BookProof_ScalaronDensitized_multOp_quadForm_eq
import Definitions.Def_ChapterStarobinskyPotential
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterQuantumGravityHalfDensity
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterLinftyMultiplication
import Definitions.Def_ChapterNavierStokesFockContinuum
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

set_option maxHeartbeats 1000000 in
theorem solution (mu : Measure X) {g : X → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : ∀ a, -c ≤ g a) (f : boundedEnergyCore mu g) :
    -c * ‖(f : Lp ℂ 2 mu)‖ ^ 2
      ≤ quadForm ((boundedEnergyCore mu g).subtype.comp (multOp mu hg)) f := by

  obtain ⟨n, hn⟩ := f.2
  have hsq : Integrable (fun a => ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2) mu := by
    have h := (Lp.memLp (f : Lp ℂ 2 mu)).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa [Real.rpow_natCast] using h
  have hmeas : AEStronglyMeasurable
      (fun a => g a * ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2) mu :=
    hg.aestronglyMeasurable.mul ((Lp.aestronglyMeasurable (f : Lp ℂ 2 mu)).norm.pow 2)
  have hgint : Integrable (fun a => g a * ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2) mu := by
    refine Integrable.mono (hsq.const_mul (n : ℝ)) hmeas ?_
    filter_upwards [hn] with a ha
    by_cases hb : |g a| ≤ (n : ℝ)
    · have h1 : ‖g a * ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2‖
          = |g a| * ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2)]
      rw [h1]
      refine le_trans (mul_le_mul_of_nonneg_right hb (by positivity)) ?_
      exact le_abs_self _
    · rw [ha hb]; simp
  have hmono : ∫ a, -c * ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2 ∂mu
      ≤ ∫ a, g a * ‖((f : Lp ℂ 2 mu) : X → ℂ) a‖ ^ 2 ∂mu := by
    refine integral_mono (hsq.const_mul _) hgint fun a => ?_
    exact mul_le_mul_of_nonneg_right (hc a) (by positivity)
  rw [multOp_quadForm_eq]
  refine le_trans (le_of_eq ?_) hmono
  rw [integral_const_mul, integral_norm_sq_eq_norm_sq]
