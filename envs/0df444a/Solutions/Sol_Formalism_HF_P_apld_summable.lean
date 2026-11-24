-- Prove2me | solution 1 for Formalism.HF.P.apld_summable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:58.8189+00:00
-- url     : https://prove2.me/submissions/026cc3af-e051-43dc-a8c5-5093e345bd9e

import Mathlib
import Definitions.Def_Formalism_DirichletDensity_Statement
import Definitions.Def_Formalism_DirichletDensity_DirichletDensityProofs_APLogDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries
noncomputable section
namespace Formalism.HF.P
variable {q : ℕ} [NeZero q] {a : ZMod q}
private lemma apld_term_lemma (a : ZMod q) (x : ℝ) (n : ℕ) :
    LSeries.term (fun n ↦ (residueClass a n : ℂ)) (x : ℂ) n =
      ((residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [LSeries.term_zero, residueClass_apply_zero, zero_div, Complex.ofReal_zero]
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg n),
      Complex.ofReal_natCast]
end Formalism.HF.P
end
end

set_option autoImplicit false
open Filter Topology ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries
noncomputable section
open Formalism Formalism.HF Formalism.HF.P
variable {q : ℕ} [NeZero q] {a : ZMod q}
namespace Formalism.HF.P
theorem _root_.solution (a : ZMod q) {x : ℝ} (hx : 1 < x) :
    Summable fun n : ℕ ↦ residueClass a n / (n : ℝ) ^ x := by
  have hL : LSeriesSummable (fun n ↦ (residueClass a n : ℂ)) x :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re ((abscissaOfAbsConv_residueClass_le_one a).trans_lt
      (by simp only [Complex.ofReal_re]; exact_mod_cast hx))
  have h2 : Summable (LSeries.term (fun n ↦ (residueClass a n : ℂ)) x) := hL
  have h3 : Summable fun n : ℕ ↦ ((residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
    convert h2 using 1
    funext n
    exact (apld_term_lemma a x n).symm
  exact Complex.summable_ofReal.1 h3
end Formalism.HF.P
