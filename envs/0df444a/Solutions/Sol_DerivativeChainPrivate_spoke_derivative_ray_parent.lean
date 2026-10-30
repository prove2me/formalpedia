-- Prove2me | solution 1 for DerivativeChainPrivate.spoke_derivative_ray_parent
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T01:01:58.519094+00:00
-- url     : https://prove2.me/submissions/2c972816-2fc9-41e2-8e56-e118d2507d13

import Mathlib
import Definitions.Def_DerivativeChainPrivate_SpokeRows
import Theorems.Thm_DerivativeChainPrivate_spoke_derivative_parent_power
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial











theorem spoke_eval_real_power (k r : ℕ) (q : Polynomial ℝ) (w : ℂ) (y : ℝ)
    (hw : w ^ k = (y : ℂ)) :
    (spokePoly k r q).eval w = w ^ r * ((q.eval y : ℝ) : ℂ) := by
  simp only [spokePoly, eval_mul, eval_pow, eval_X, eval_comp, hw]
  exact congrArg (fun z : ℂ => w ^ r * z)
    (Polynomial.eval_map_apply (f := Complex.ofRealHom) (p := q) y)





end DerivativeChainPrivate



set_option autoImplicit false
open DerivativeChainPrivate
open Polynomial



theorem solution (k r : ℕ) (q : Polynomial ℝ)
    (hk : 2 ≤ k) (hr : r < k) (hq : q.Splits) (hqne : q ≠ 0)
    (hdegree : 2 ≤ (_root_.DerivativeChainPrivate.spokePoly k r q).natDegree) (w : ℂ) (hw : w ≠ 0)
    (hz : (_root_.DerivativeChainPrivate.spokePoly k r q).derivative.eval w = 0) :
    ∃ t : ℝ, 1 ≤ t ∧ (_root_.DerivativeChainPrivate.spokePoly k r q).eval ((t : ℂ) * w) = 0 := by
  obtain ⟨y, x, hy, hx, hsign⟩ :=
    _root_.DerivativeChainPrivate.spoke_derivative_parent_power k r q hk hr hq hqne hdegree w hw hz
  have hyne : y ≠ 0 := by
    intro h
    have : w ^ k = 0 := by simp [hy, h]
    exact pow_ne_zero _ hw this
  have hratio : 1 ≤ x / y := by
    rcases hsign with ⟨hypos, hxy⟩ | ⟨hyneg, hxy⟩
    · exact (le_div_iff₀ hypos).mpr (by simpa using hxy)
    · exact (le_div_iff_of_neg hyneg).mpr (by simpa using hxy)
  let t : ℝ := (x / y) ^ ((k : ℝ)⁻¹)
  have ht : 1 ≤ t := Real.one_le_rpow hratio (by positivity)
  have htpow : t ^ k = x / y := Real.rpow_inv_natCast_pow (by linarith) (by omega)
  have hpower : ((t : ℂ) * w) ^ k = (x : ℂ) := by
    rw [mul_pow, ← Complex.ofReal_pow, htpow, hy, ← Complex.ofReal_mul]
    congr 1
    exact div_mul_cancel₀ x hyne
  refine ⟨t, ht, ?_⟩
  rw [_root_.DerivativeChainPrivate.spoke_eval_real_power k r q _ x hpower, hx]
  simp
