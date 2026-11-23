-- Prove2me | solution 1 for Formalism.FG.ShiftFEAux.main
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:45:33.996424+00:00
-- url     : https://prove2.me/submissions/a859c68e-c853-4b1d-9902-35cafb8966c2

import Definitions.Def_Formalism_FormalGroupWitt_Statement
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_ShiftFE
import Theorems.Thm_Formalism_FG_ShiftFEAux_eq_zero_of_pow_eq_one
import Theorems.Thm_Formalism_FG_ShiftFEAux_coeff_shiftLog_single
import Theorems.Thm_Formalism_FG_ShiftFEAux_coeff_shiftLog_zero
import Theorems.Thm_Formalism_FG_ShiftFEAux_map_shiftLog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u
open Formalism Formalism.FG
open Formalism.FG.ShiftFEAux
open MvPowerSeries
variable {K : Type*} [Field K] {l m : ℕ}
namespace Formalism.FG.ShiftFEAux
theorem _root_.solution [CharZero K] (hl : l.Prime) [NeZero m] (σ : K →+* K) (j : ZMod m) :
    shiftLog K l m j - (l : K)⁻¹ • ∑ k, shiftMat K m j k •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLog K l m k)) = MvPowerSeries.X j := by
  have hl2 : 2 ≤ l := hl.two_le
  have hsum : ∑ k, shiftMat K m j k •
        MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
          (MvPowerSeries.map σ (shiftLog K l m k)) =
      MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero) (shiftLog K l m (j - 1)) := by
    simp [shiftMat, map_shiftLog]
  rw [hsum]
  ext n
  simp only [map_sub, map_smul, smul_eq_mul, coeff_X]
  by_cases hA : ∃ e : ℕ, n = Finsupp.single (j - (e : ZMod m)) ((l ^ 2) ^ e)
  · obtain ⟨e, rfl⟩ := hA
    rw [coeff_shiftLog_single hl2]
    obtain _ | e := e
    · simp only [Nat.cast_zero, sub_zero, pow_zero, inv_one, if_true]
      rw [coeff_expand_of_not_dvd (i := j)]
      · ring
      · rw [Finsupp.single_eq_same, Nat.dvd_one]
        intro h
        nlinarith
    · have hne : Finsupp.single (j - ((e + 1 : ℕ) : ZMod m)) ((l ^ 2) ^ (e + 1)) ≠
          Finsupp.single j 1 := by
        intro h
        have hd := congrArg Finsupp.degree h
        simp only [Finsupp.degree_single] at hd
        exact absurd (eq_zero_of_pow_eq_one hl2 hd) (Nat.succ_ne_zero e)
      rw [if_neg hne]
      have hn : Finsupp.single (j - ((e + 1 : ℕ) : ZMod m)) ((l ^ 2) ^ (e + 1)) =
          (l ^ 2) • Finsupp.single ((j - 1) - (e : ZMod m)) ((l ^ 2) ^ e) := by
        rw [Finsupp.smul_single, smul_eq_mul, ← pow_succ']
        congr 1
        push_cast
        ring
      rw [hn, coeff_expand_smul, coeff_shiftLog_single hl2]
      ring
  · push Not at hA
    rw [coeff_shiftLog_zero j n hA, if_neg (by simpa using hA 0)]
    suffices h : coeff n (MvPowerSeries.expand (l ^ 2) (pow_ne_zero 2 hl.ne_zero)
        (shiftLog K l m (j - 1))) = 0 by rw [h]; ring
    by_cases hd : ∀ i, l ^ 2 ∣ n i
    · have hn : n = (l ^ 2) • Finsupp.mapRange (fun x => x / l ^ 2) (Nat.zero_div _) n := by
        ext i
        simp [Nat.mul_div_cancel' (hd i)]
      rw [hn, coeff_expand_smul]
      apply coeff_shiftLog_zero
      intro e he
      apply hA (e + 1)
      rw [hn, he, Finsupp.smul_single, smul_eq_mul, ← pow_succ']
      congr 1
      push_cast
      ring
    · push Not at hd
      obtain ⟨i, hi⟩ := hd
      exact coeff_expand_of_not_dvd _ _ _ hi
end Formalism.FG.ShiftFEAux
