-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_sextic_radicand_avoids_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:56:00.790529+00:00
-- url     : https://prove2.me/submissions/22d7f5ad-6a5c-4615-a772-d5bac17232a3

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_sixth_sextic_nonnegative_levels_splits
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (z : ℂ) (hz : 0 < z.im) :
    let H := z^2 + (-85/43 : ℂ)*z + (1445/1806 : ℂ) + (24565/211302 : ℂ)/z
    H.im ≠ 0 ∨ H.re < 0 := by
  let H := z^2 + (-85/43 : ℂ)*z + (1445/1806 : ℂ) + (24565/211302 : ℂ)/z
  change H.im ≠ 0 ∨ H.re < 0
  by_contra! hf
  let t := H.re
  have ht : 0 ≤ t := hf.2
  have hH : H = (t : ℂ) := by apply Complex.ext <;> simp [t,hf.1]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  let p : Polynomial ℝ := 211302*X^3 + (-417690)*X^2 + C (169065-211302*t)*X + 24565
  have hs : p.Splits := sixth_sextic_nonnegative_levels_splits t ht
  have hp : p ≠ 0 := by
    intro h
    have hh := congrArg (fun q : Polynomial ℝ => q.eval 0) h
    norm_num [p] at hh
  have hr : (p.map Complex.ofRealHom).eval z = 0 := by
    simp only [p,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,
      Polynomial.map_X,Polynomial.map_C,Polynomial.map_ofNat,Polynomial.map_neg,
      eval_add,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat,eval_neg]
    change 211302*z^3 + (-417690)*z^2 + (((169065-211302*t : ℝ) : ℂ))*z + 24565 = 0
    push_cast
    calc
      _ = 211302*z*(H-(t : ℂ)) := by dsimp only [H]; field_simp; ring
      _ = 0 := by rw [hH]; ring
  obtain ⟨r,he⟩ := hs.mem_range_of_isRoot hp hr
  have hi := congrArg Complex.im he
  change (0 : ℝ) = z.im at hi
  linarith
