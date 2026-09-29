-- Prove2me | solution 1 for BraidsLinksMCG.puncturedPlane_standardGen_old_loop_mem_left_region_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T00:59:18.335978+00:00
-- url     : https://prove2.me/submissions/642f2913-1dc7-4447-9c08-7b1d82ff8247

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops

set_option autoImplicit false

open BraidsLinksMCG

/-- `Fin.castSucc` does not change the underlying natural number. -/
private lemma castSucc_val (n : ℕ) (j : Fin n) :
    ((j.castSucc : Fin (n + 1)) : ℕ) = (j : ℕ) :=
  rfl

private lemma circle_re (n : ℕ) (j : Fin n) :
    ∀ a : unitInterval,
      (circleFun (n + 1) j.castSucc (a : ℝ)).re
        = ((j : ℕ) : ℝ) + 1 + ((1 / 2 : ℝ) * Real.cos (2 * Real.pi * (a : ℝ))) := by
  intro a
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
  have hexp : Complex.exp (((2 * Real.pi * (a : ℝ) : ℝ) : ℂ) * Complex.I)
      = (Real.cos (2 * Real.pi * (a : ℝ)) : ℂ)
        + (Real.sin (2 * Real.pi * (a : ℝ)) : ℂ) * Complex.I :=
    Complex.exp_ofReal_mul_I _
  rw [circleFun, hexp, hhalf]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero, Complex.natCast_re, Complex.one_re]
  norm_num [castSucc_val (n := n)]

/-- The circular leg of the standard loop has real part `< n + 1`.

The real part is at most `(j : ℝ) + 3 / 2 ≤ (n - 1) + 3 / 2 < n + 1`, using
`j < n` so that `(j : ℕ) + 1 ≤ n`. -/
private lemma circle_mem (n : ℕ) (j : Fin n) (a : unitInterval) :
    (circlePath (n + 1) j.castSucc a).1.re < ((n : ℕ) + 1 : ℝ) := by
  have hle : (j : ℕ) + 1 ≤ n := by omega
  have hleR : ((j : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hle
  have hcos : (1 / 2 : ℝ) * Real.cos (2 * Real.pi * (a : ℝ)) ≤ 1 / 2 := by
    rcases abs_le.mp (Real.abs_cos_le_one (2 * Real.pi * (a : ℝ))) with ⟨hlo, hhi⟩
    nlinarith
  calc (circlePath (n + 1) j.castSucc a).1.re
      = (circleFun (n + 1) j.castSucc (a : ℝ)).re := rfl
    _ = ((j : ℕ) : ℝ) + 1 + ((1 / 2 : ℝ) * Real.cos (2 * Real.pi * (a : ℝ))) :=
      circle_re n j a
    _ < ((n : ℕ) + 1 : ℝ) := by linarith

/-- The approach leg lies in the left piece.

The imaginary part is `t * (1 - t)`, strictly positive for `0 < t < 1`, so
the second disjunct covers the interior. At `t = 0` the point is the base
point `n + 2`, whose distance to `n + 2` vanishes, so the third disjunct holds.
At `t = 1` the point is the half-integer `(j + 1) + 1/2`, whose real part is
at most `n - 1/2 < n + 1`, so the first disjunct holds. -/
private lemma approach_mem (n : ℕ) (j : Fin n) (a : unitInterval) :
    (approachPath (n + 1) j.castSucc a).1.re < ((n : ℕ) + 1 : ℝ) ∨
      0 < (approachPath (n + 1) j.castSucc a).1.im ∨
      dist (approachPath (n + 1) j.castSucc a).1 (((n : ℕ) + 2 : ℕ) : ℂ) < (1 / 2 : ℝ) := by
  by_cases hz : (a : ℝ) = 0
  · right; right
    have hz'' : (approachPath (n + 1) j.castSucc a).1
        = (basePunctured (n + 1) : PuncturedPlane (n + 1)).1 := by
      calc (approachPath (n + 1) j.castSucc a).1
          = (approachPath (n + 1) j.castSucc (0 : unitInterval)).1 := by
            rw [show a = (0 : unitInterval) from Subtype.ext hz]
        _ = (basePunctured (n + 1) : PuncturedPlane (n + 1)).1 :=
          congrArg Subtype.val ((approachPath (n + 1) j.castSucc).source')
    have hval : (basePunctured (n + 1) : PuncturedPlane (n + 1)).1
        = ((n + 2 : ℕ) : ℂ) := by
      show ((n + 1 : ℕ) : ℂ) + 1 = _
      push_cast
      ring_nf
    calc dist (approachPath (n + 1) j.castSucc a).1 (((n + 2 : ℕ) : ℂ))
        = dist ((n + 2 : ℕ) : ℂ) (((n + 2 : ℕ) : ℂ)) := by rw [hz'', hval]
      _ = 0 := dist_self _
      _ < (1 / 2 : ℝ) := by norm_num
  ·
    rw [show (approachPath (n + 1) j.castSucc a).1
        = approachFun (n + 1) j.castSucc (a : ℝ) from rfl, approachFun_im]
    rcases eq_or_lt_of_le a.2.2 with hone | hlt
    · left
      -- `t = 1`: the real part is `(j : ℝ) + 3 / 2 ≤ n - 1/2 < n + 1`.
      have hle : (j : ℕ) + 1 ≤ n := by omega
      have hleR : ((j : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hle
      have hre : (approachFun (n + 1) j.castSucc 1).re
          = ((j : ℕ) : ℝ) + 1 + (1 / 2 : ℝ) := by
        simp only [approachFun, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
          Complex.I_re, Complex.ofReal_im, castSucc_val (n := n)]
        push_cast
        ring_nf
      rw [show (a : ℝ) = 1 from hone, hre]
      linarith
    · right; left
      exact mul_pos (lt_of_le_of_ne a.2.1 (Ne.symm hz)) (by linarith)

theorem solution (n : ℕ) (j : Fin n) (t : unitInterval) :
    (standardLoop (n + 1) j.castSucc t).1.re < ((n : ℕ) + 1 : ℝ) ∨
      0 < (standardLoop (n + 1) j.castSucc t).1.im ∨
      dist (standardLoop (n + 1) j.castSucc t).1 (((n : ℕ) + 2 : ℕ) : ℂ) < (1 / 2 : ℝ) := by
  unfold standardLoop
  rw [Path.trans_apply]
  split_ifs with h
  · exact approach_mem n j _
  · rw [Path.trans_apply]
    split_ifs with h'
    · left; exact circle_mem n j _
    · exact approach_mem n j _
