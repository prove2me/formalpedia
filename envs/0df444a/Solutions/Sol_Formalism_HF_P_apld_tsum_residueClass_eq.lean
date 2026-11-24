-- Prove2me | solution 1 for Formalism.HF.P.apld_tsum_residueClass_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:58.837967+00:00
-- url     : https://prove2.me/submissions/13acb263-eeb0-4a8a-92b6-aef4e93668df

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
theorem _root_.solution (ha : IsUnit a) {x : ℝ} (hx : 1 < x) :
    ∑' n, residueClass a n / (n : ℝ) ^ x =
      (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
  have hx' : (x : ℂ) ∈ {s : ℂ | 1 < s.re} := by simpa using hx
  have hLS : LSeries (fun n ↦ (residueClass a n : ℂ)) x =
      ((∑' n, residueClass a n / (n : ℝ) ^ x : ℝ) : ℂ) := by
    unfold LSeries
    rw [Complex.ofReal_tsum]
    exact tsum_congr fun n => apld_term_lemma a x n
  have hE := eqOn_LFunctionResidueClassAux ha hx'
  have hA : LFunctionResidueClassAux a x =
      (((∑' n, residueClass a n / (n : ℝ) ^ x) - (q.totient : ℝ)⁻¹ / (x - 1) : ℝ) : ℂ) := by
    rw [hE]
    simp only [hLS]
    push_cast
    rfl
  rw [hA, Complex.ofReal_re]
  ring
end Formalism.HF.P
