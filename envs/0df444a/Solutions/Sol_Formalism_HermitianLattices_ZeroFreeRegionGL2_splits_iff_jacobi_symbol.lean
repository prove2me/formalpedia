-- Prove2me | solution 1 for Formalism.HermitianLattices.ZeroFreeRegionGL2.splits_iff_jacobi_symbol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:55.993569+00:00
-- url     : https://prove2.me/submissions/6e6c1ff0-2ba1-4f67-8c52-f320a20c0ba0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SecondEstimateOfIntervalHypothesis
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_WeightedVonMangoldtSumIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.ZeroFreeRegionGL2
theorem _root_.solution : SplitsIffJacobi := by
  intro d p hp hd
  have h4 : 4 * ((d + 1) / 4) = d + 1 := by omega
  refine ⟨fun hp2 => ?_, ?_⟩
  · have := Fact.mk hp
    have h4' : (4 : ZMod p) * (((d + 1) / 4 : ℕ) : ZMod p) = (d : ZMod p) + 1 := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ZMod p) h4
    have two : (2 : ZMod p) ≠ 0 := by
      intro h
      have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.natCast_eq_zero_iff] at this
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
    have four : (4 : ZMod p) ≠ 0 := by
      have : (4 : ZMod p) = 2 * 2 := by norm_num
      rw [this]; exact mul_ne_zero two two
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    have cast : (((-(d : ℤ)) : ℤ) : ZMod p) = -(d : ZMod p) := by push_cast; rfl
    unfold SplitsIn
    constructor
    · rintro ⟨r, s, hrs, hr, hs⟩
      have sqr : (2 * r - 1) * (2 * r - 1) = -(d : ZMod p) := by linear_combination 4 * hr - h4'
      have sqs : (2 * s - 1) * (2 * s - 1) = -(d : ZMod p) := by linear_combination 4 * hs - h4'
      have hne : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
        rw [cast]; intro h0
        rw [h0] at sqr sqs
        have a := mul_self_eq_zero.1 sqr
        have b := mul_self_eq_zero.1 sqs
        apply hrs
        have : 2 * (r - s) = 0 := by linear_combination a - b
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h two
        · exact sub_eq_zero.1 h
      rw [legendreSym.eq_one_iff p hne, cast]
      exact ⟨2 * r - 1, sqr.symm⟩
    · intro h
      have hne : (((-(d : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
        intro h0
        rw [(legendreSym.eq_zero_iff p _).2 h0] at h; exact absurd h (by norm_num)
      obtain ⟨t, ht⟩ := (legendreSym.eq_one_iff p hne).1 h
      rw [cast] at ht hne
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact hne (by simpa using ht)
      have hr2 : 2 * ((1 + t) / 2) = 1 + t := by field_simp
      have hs2 : 2 * ((1 - t) / 2) = 1 - t := by field_simp
      refine ⟨(1 + t) / 2, (1 - t) / 2, ?_, ?_, ?_⟩
      · intro he
        have e : 1 + t = 1 - t := by rw [← hr2, ← hs2, he]
        have : 2 * t = 0 := by linear_combination e
        rcases mul_eq_zero.1 this with h | h
        · exact two h
        · exact ht0 h
      · apply (mul_eq_zero.1 (?_ : (4 : ZMod p) * _ = 0)).resolve_left four
        linear_combination (2 * ((1 + t) / 2) + t - 1) * hr2 + h4' - ht
      · apply (mul_eq_zero.1 (?_ : (4 : ZMod p) * _ = 0)).resolve_left four
        linear_combination (2 * ((1 - t) / 2) - t - 1) * hs2 + h4' - ht
  · unfold SplitsIn
    constructor
    · rintro ⟨r, -, -, hr, -⟩
      by_contra h
      have hodd : ((d + 1) / 4) % 2 = 1 := by omega
      have : (((d + 1) / 4 : ℕ) : ZMod 2) = 1 := by
        rw [← ZMod.natCast_mod, hodd]; rfl
      rw [this] at hr
      revert hr; revert r; decide
    · intro h
      have : (((d + 1) / 4 : ℕ) : ZMod 2) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 (by omega)
      exact ⟨0, 1, by decide, by simp [this], by simp [this]⟩
end Formalism.HermitianLattices.ZeroFreeRegionGL2
