-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.chebyshev_moment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:41.732412+00:00
-- url     : https://prove2.me/submissions/556f0360-f58f-4057-a957-1e930f798209

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_BlockMinorSumCounterexample

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
theorem _root_.solution {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (f : Ω → ℝ) (q : ℕ) (H1 la : ℝ)
    (hf : Measurable f) (hH1 : 0 < H1) (hla : 0 < la)
    (h : ∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * q)) ∂μ ≤ ENNReal.ofReal (H1 ^ (2 * q))) :
    μ {ω | la * H1 ≤ f ω} ≤ ENNReal.ofReal (1 / la ^ (2 * q)) := by
  have h0 : 0 < (la * H1) ^ (2 * q) := by positivity
  have h1 : μ {ω | ENNReal.ofReal ((la * H1) ^ (2 * q)) ≤ ENNReal.ofReal (f ω ^ (2 * q))} ≤
      (∫⁻ ω, ENNReal.ofReal (f ω ^ (2 * q)) ∂μ) / ENNReal.ofReal ((la * H1) ^ (2 * q)) :=
    meas_ge_le_lintegral_div (ENNReal.measurable_ofReal.comp (hf.pow_const _)).aemeasurable
      (by simpa using h0) ENNReal.ofReal_ne_top
  have h2 : {ω | la * H1 ≤ f ω} ⊆
      {ω | ENNReal.ofReal ((la * H1) ^ (2 * q)) ≤ ENNReal.ofReal (f ω ^ (2 * q))} := by
    intro ω hω
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) hω _)
  refine (measure_mono h2).trans (h1.trans ?_)
  calc _ ≤ ENNReal.ofReal (H1 ^ (2 * q)) / ENNReal.ofReal ((la * H1) ^ (2 * q)) := by gcongr
    _ = ENNReal.ofReal (H1 ^ (2 * q) / (la * H1) ^ (2 * q)) := (ENNReal.ofReal_div_of_pos h0).symm
    _ = ENNReal.ofReal (1 / la ^ (2 * q)) := by
        congr 1
        rw [mul_pow]
        field_simp
end Formalism.HermitianLatticeCounting.P
