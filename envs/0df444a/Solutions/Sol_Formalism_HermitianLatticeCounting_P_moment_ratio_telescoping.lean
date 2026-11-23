-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.moment_ratio_telescoping
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:12:28.514904+00:00
-- url     : https://prove2.me/submissions/fe15a721-4119-4a8d-aa18-a059abfd74ed

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_holder_lintegral_prod_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Finset Real MeasureTheory Formalism.HermitianLatticeCounting.ExpansionTerms
open scoped ENNReal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ)
    (n q : ℕ) (B : ℕ → ℝ) (hm : ∀ i, Measurable (M i)) (hpos : ∀ i ω, 0 < M i ω) (hB : ∀ i, 0 ≤ B i)
    (h : ∀ i < n, ∫⁻ ω, ENNReal.ofReal ((M (i + 1) ω / M i ω) ^ (2 * (n * q))) ∂μ ≤
      ENNReal.ofReal (B i ^ (2 * (n * q)))) :
    ∫⁻ ω, ENNReal.ofReal ((M n ω / M 0 ω) ^ (2 * q)) ∂μ ≤ ENNReal.ofReal (∏ i ∈ range n, B i ^ (2 * q)) := by
  have t : ∀ (m : ℕ) ω, ∏ i ∈ range m, (M (i + 1) ω / M i ω) = M m ω / M 0 ω := by
    intro m ω
    induction m with
    | zero => simp [(hpos 0 ω).ne']
    | succ m ih =>
      rw [prod_range_succ, ih]
      have h1 := (hpos m ω).ne'
      have h2 := (hpos 0 ω).ne'
      field_simp
  have e : ∀ ω, ENNReal.ofReal ((M n ω / M 0 ω) ^ (2 * q)) =
      ∏ i ∈ range n, ENNReal.ofReal ((M (i + 1) ω / M i ω) ^ (2 * q)) := by
    intro ω
    rw [← t n ω, ← Finset.prod_pow, ENNReal.ofReal_prod_of_nonneg]
    intro i _
    have h1 := hpos (i + 1) ω
    have h2 := hpos i ω
    positivity
  simp_rw [e]
  rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (hB i) _)]
  apply holder_lintegral_prod_le
  · intro i _
    exact ENNReal.measurable_ofReal.comp (((hm _).div (hm _)).pow_const _)
  · intro i hi
    rw [card_range]
    have h3 := h i (mem_range.1 hi)
    have e1 : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal (x ^ (2 * q)) ^ n = ENNReal.ofReal (x ^ (2 * (n * q))) := by
      intro x hx
      rw [← ENNReal.ofReal_pow (pow_nonneg hx _), ← pow_mul]
      congr 2
      ring
    rw [e1 _ (hB i)]
    refine le_trans (le_of_eq ?_) h3
    refine lintegral_congr fun ω => e1 _ ?_
    have h1 := hpos (i + 1) ω
    have h2 := hpos i ω
    positivity
end Formalism.HermitianLatticeCounting.P
