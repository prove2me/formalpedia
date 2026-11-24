-- Prove2me | solution 1 for Formalism.HC.Der.sq_odd_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:51:56.782999+00:00
-- url     : https://prove2.me/submissions/0caec417-cc26-4fe8-aa13-cd2c77fa097f

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HC.Der
theorem _root_.solution {d : ℤ} {l : ℕ} (hl : l.Prime) (hl2 : l ≠ 2) (hj : jacobiSym (-d) l = 1) (k : ℕ) :
    ∃ s : ℤ, (l : ℤ) ^ (k + 1) ∣ s ^ 2 + d := by
  haveI := Fact.mk hl
  have hl2' : (2 : ZMod l) ≠ 0 := by
    intro h
    have h' : ((2 : ℤ) : ZMod l) = 0 := by exact_mod_cast h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
    have h'' : l ∣ 2 := by exact_mod_cast h'
    exact hl2 ((Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp h'')
  rw [← jacobiSym.legendreSym.to_jacobiSym] at hj
  have hd0 : ((-d : ℤ) : ZMod l) ≠ 0 := by
    intro h
    rw [(legendreSym.eq_zero_iff l (-d)).mpr h] at hj
    norm_num at hj
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff l hd0).mp hj
  induction k with
  | zero =>
    refine ⟨(r.val : ℤ), ?_⟩
    rw [zero_add, pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    push_cast at hr
    linear_combination (-1 : ZMod l) * hr
  | succ k ih =>
    obtain ⟨s, t, ht⟩ := ih
    have hs0 : (s : ZMod l) ≠ 0 := by
      intro h
      have h1 : ((s ^ 2 + d : ℤ) : ZMod l) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ht]
        exact Dvd.dvd.mul_right (dvd_pow_self _ (Nat.succ_ne_zero k)) t
      push_cast at h1
      rw [h] at h1
      apply hd0
      push_cast
      linear_combination -h1
    have h2s : (2 * (s : ZMod l)) ≠ 0 := mul_ne_zero hl2' hs0
    obtain ⟨c, hc'⟩ := ZMod.intCast_surjective (n := l) (-(t : ZMod l) * (2 * (s : ZMod l))⁻¹)
    have hc : ((t + 2 * s * c : ℤ) : ZMod l) = 0 := by
      push_cast
      rw [hc']
      have hi : (2 * (s : ZMod l)) * (2 * (s : ZMod l))⁻¹ = 1 := mul_inv_cancel₀ h2s
      linear_combination (-(t : ZMod l)) * hi
    obtain ⟨w, hw⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ l).mp hc
    refine ⟨s + (l : ℤ) ^ (k + 1) * c, w + (l : ℤ) ^ k * c ^ 2, ?_⟩
    linear_combination ht + (l : ℤ) ^ (k + 1) * hw
end Formalism.HC.Der
