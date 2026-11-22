-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.RealCyclotomicSubfield.conj_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:09:41.87618+00:00
-- url     : https://prove2.me/submissions/f7ffcd61-5df4-4647-807d-1885d1064684

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_RealCyclotomicSubfield

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Polynomial
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Formalism.FrobeniusOrbits.RealCyclotomicSubfield
namespace Formalism.FrobeniusOrbits.RealCyclotomicSubfield
theorem _root_.solution {z : ℂ} {m : ℕ} (hm : m ≠ 0) (hz : z ^ m = 1) : starRingEnd ℂ z = z⁻¹ := by
  have hn : ‖z‖ = 1 := by
    have h1 := congrArg norm hz
    rw [norm_pow, norm_one] at h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hm).mp h1
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hn]
  simp
end Formalism.FrobeniusOrbits.RealCyclotomicSubfield
