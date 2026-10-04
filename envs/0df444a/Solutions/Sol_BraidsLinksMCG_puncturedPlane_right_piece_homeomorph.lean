-- Prove2me | solution 1 for BraidsLinksMCG.puncturedPlane_right_piece_homeomorph
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T12:12:09.438785+00:00
-- url     : https://prove2.me/submissions/aad088d0-eaab-4347-bf4f-55c2fbdbee53

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

namespace P067d089f

open BraidsLinksMCG Complex

lemma fwd_pos (n : ℕ) (x : ℝ) (hx : ((n : ℝ) + 1) - 3 / 4 < x) :
    0 < 1 + 4 / 3 * (x - ((n : ℝ) + 1)) := by linarith

lemma fwd_ne (n : ℕ) (z : {z : PuncturedPlane (n + 1) | ((n : ℝ) + 1) - 3 / 4 < z.1.re}) :
    ((Real.log (1 + 4 / 3 * (z.1.1.re - ((n : ℝ) + 1))) : ℂ) + (z.1.1.im : ℂ) * I) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp at hre him
  have hp := fwd_pos n z.1.1.re z.2
  have hre' : z.1.1.re = (n : ℝ) + 1 := by
    rcases hre with h' | h' | h'
    · linarith
    · linarith
    · linarith
  apply z.1.2 ⟨n, by omega⟩
  apply Complex.ext
  · simp [hre']
  · simp [him]

lemma bwd_mem (n : ℕ) (u : {w : ℂ // w ≠ 0}) :
    ∀ j : Fin (n + 1),
      ((((3 / 4 * (Real.exp u.1.re - 1) + ((n : ℝ) + 1)) : ℝ) : ℂ) + (u.1.im : ℂ) * I) ≠
        ((j : ℕ) + 1 : ℂ) := by
  intro j h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [Complex.exp_ofReal_re] at hre him
  have hj := j.isLt
  have hpos := Real.exp_pos u.1.re
  -- j + 1 > n + 1/4, so j = n
  have hjn : (j : ℕ) = n := by
    have h2 : ((n : ℝ) + 1) - 3 / 4 < (j : ℝ) + 1 := by
      have : -3 / 4 < 3 / 4 * (Real.exp u.1.re - 1) := by nlinarith
      linarith
    have h3 : (n : ℝ) < (j : ℝ) + 1 := by linarith
    have h4 : n < (j : ℕ) + 1 := by exact_mod_cast h3
    omega
  rw [hjn] at hre
  have he : Real.exp u.1.re = 1 := by linarith
  have hr : u.1.re = 0 := by simpa using he
  apply u.2
  exact Complex.ext (by simp [hr]) (by simp [him])

noncomputable def homeo (n : ℕ) :
    {z : PuncturedPlane (n + 1) | ((n : ℝ) + 1) - 3 / 4 < z.1.re} ≃ₜ {w : ℂ // w ≠ 0} where
  toFun z := ⟨(Real.log (1 + 4 / 3 * (z.1.1.re - ((n : ℝ) + 1))) : ℂ) + (z.1.1.im : ℂ) * I,
    fwd_ne n z⟩
  invFun u := ⟨⟨(((3 / 4 * (Real.exp u.1.re - 1) + ((n : ℝ) + 1)) : ℝ) : ℂ) + (u.1.im : ℂ) * I,
    bwd_mem n u⟩, by
      show ((n : ℝ) + 1) - 3 / 4 < _
      have hpos := Real.exp_pos u.1.re
      simp [Complex.exp_ofReal_re]
      linarith⟩
  left_inv z := by
    have hp := fwd_pos n z.1.1.re z.2
    apply Subtype.ext; apply Subtype.ext
    apply Complex.ext
    · simp [Real.exp_log hp]; ring
    · simp
  right_inv u := by
    apply Subtype.ext
    apply Complex.ext
    · have hpos := Real.exp_pos u.1.re
      have : 1 + 4 / 3 * (3 / 4 * (Real.exp u.1.re - 1) + ((n : ℝ) + 1) - ((n : ℝ) + 1))
          = Real.exp u.1.re := by ring
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, sub_zero, add_zero]
      rw [this, Real.log_exp]
    · simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous fun z : {z : PuncturedPlane (n + 1) |
        ((n : ℝ) + 1) - 3 / 4 < z.1.re} => z.1.1 :=
      continuous_subtype_val.comp continuous_subtype_val
    apply Continuous.add
    · apply Complex.continuous_ofReal.comp
      apply Continuous.log
      · exact continuous_const.add (continuous_const.mul
          ((Complex.continuous_re.comp hc).sub continuous_const))
      · intro z; exact (fwd_pos n z.1.1.re z.2).ne'
    · exact (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hc)).mul continuous_const
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    have hc : Continuous fun u : {w : ℂ // w ≠ 0} => u.1 := continuous_subtype_val
    apply Continuous.add
    · apply Complex.continuous_ofReal.comp
      exact (continuous_const.mul ((Real.continuous_exp.comp (Complex.continuous_re.comp hc)).sub
        continuous_const)).add continuous_const
    · exact (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hc)).mul continuous_const

end P067d089f

open BraidsLinksMCG in
theorem solution (n : ℕ) :
    Nonempty
      ({z : PuncturedPlane (n + 1) | ((n : ℝ) + 1) - 3 / 4 < z.1.re} ≃ₜ
        {w : ℂ // w ≠ 0}) := by
  exact ⟨P067d089f.homeo n⟩
