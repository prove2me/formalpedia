-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.classSetAssembly_finite_rat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:56.001209+00:00
-- url     : https://prove2.me/submissions/7d540519-185e-46fb-b061-6eecda1b5cd4

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_GenusCovolBound
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IsomAct
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_GenusBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_ClassSetAssembly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (d : ℕ) (hd : 0 < d) (R : ℝ) :
    {q : ℚ | (∃ z : ℤ, (d : ℚ) * q = z) ∧ |(q : ℝ)| ≤ R}.Finite := by
  set N : ℤ := ⌈(d : ℝ) * R⌉
  refine ((Set.finite_Icc (-N) N).image (fun z : ℤ => (z : ℚ) / d)).subset ?_
  rintro q ⟨⟨z, hz⟩, hq⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have hzR : ((z : ℚ) : ℝ) = (d : ℝ) * (q : ℝ) := by
    rw [← hz, Rat.cast_mul, Rat.cast_natCast]
  have hzR' : (z : ℝ) = (d : ℝ) * (q : ℝ) := by exact_mod_cast hzR
  have habs : |(z : ℝ)| ≤ (d : ℝ) * R := by
    rw [hzR', abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ d)]
    exact mul_le_mul_of_nonneg_left hq (by positivity)
  have hN : (d : ℝ) * R ≤ (N : ℝ) := Int.le_ceil _
  have h1 : (z : ℝ) ≤ N := le_trans (le_abs_self _) (habs.trans hN)
  have h2 : -(N : ℝ) ≤ z := by
    have := neg_abs_le (z : ℝ)
    linarith
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · have h3 : ((-N : ℤ) : ℝ) ≤ (z : ℝ) := by push_cast; linarith
    exact_mod_cast h3
  · exact_mod_cast h1
  · show (z : ℚ) / d = q
    rw [← hz]
    field_simp
end Formalism.HermitianLatticesTheory
