-- Prove2me | solution 1 for D1Bound5.pellPairChecks_sound
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:33:57.151181+00:00
-- url     : https://prove2.me/submissions/b242318c-275e-4d8b-9a13-cb8f27948981

import Mathlib.Data.List.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_PellMatchingCheck_Definitions

section
namespace D1Bound5







theorem pellScalarMaskBool_of_square (c : ℤ) (k mask : ℕ)
    (hvalid : PellScalarMaskValid c k mask) (z r : ℤ)
    (hr : c*r*r = z) : pellScalarMaskBool k mask z = true := by
  unfold pellScalarMaskBool
  rw [← hr]
  simpa only [Int.cast_mul] using hvalid (r : ZMod (k+1))









theorem pellDefaultMasks_valid (d : ℤ) : pellDefaultMasks.Valid d := by
  change PellScalarMaskValid 1 0 1 ∧ PellScalarMaskValid d 0 1
  letI : Subsingleton (ZMod 1) := ZMod.subsingleton_iff.mpr rfl
  constructor
  all_goals
    intro r
    have hr : r = (0 : ZMod 1) := Subsingleton.elim _ _
    subst r
    norm_num [pellDefaultMasks]



theorem pellSelectMasks_valid (d : ℤ) (ms : List PellSquareMasks)
    (hvalid : ∀ m ∈ ms, m.Valid d) (n : ℕ) : (pellSelectMasks ms n).Valid d := by
  induction ms generalizing n with
  | nil => exact pellDefaultMasks_valid d
  | cons m ms ih =>
      cases n with
      | zero => exact hvalid m (by simp)
      | succ n => exact ih (fun m hm => hvalid m (by simp [hm])) n



theorem _root_.solution (d : ℤ) (ms : List PellSquareMasks)
    (hvalid : ∀ m ∈ ms, m.Valid d) (x : ℤ) (ys : List ℤ)
    (ws : List (ℕ × ℕ)) (hcheck : pellPairChecks ms x ys ws = true)
    (y : ℤ) (hy : y ∈ ys) :
    (¬∃ r : ℤ, r*r = x*y+1) ∧ (¬∃ r : ℤ, d*r*r = x*y-1) := by
  induction ys generalizing ws with
  | nil => simp at hy
  | cons z zs ih =>
      cases ws with
      | nil => simp [pellPairChecks] at hcheck
      | cons w ws =>
          simp only [pellPairChecks, Bool.and_eq_true] at hcheck
          rcases List.mem_cons.mp hy with rfl | hy
          · constructor
            · rintro ⟨r,hr⟩
              have hh := pellScalarMaskBool_of_square 1 _ _
                (pellSelectMasks_valid d ms hvalid w.1).1 _ r
                (by simpa using hr)
              simpa only [hh, Bool.not_true, Bool.false_eq_true] using hcheck.1.1
            · rintro ⟨r,hr⟩
              have hh := pellScalarMaskBool_of_square d _ _
                (pellSelectMasks_valid d ms hvalid w.2).2 _ r hr
              simpa only [hh, Bool.not_true, Bool.false_eq_true] using hcheck.1.2
          · exact ih ws hcheck.2 hy



















end D1Bound5
end
