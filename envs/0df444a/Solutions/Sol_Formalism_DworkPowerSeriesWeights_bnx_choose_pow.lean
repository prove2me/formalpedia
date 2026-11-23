-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.bnx_choose_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:57:59.921625+00:00
-- url     : https://prove2.me/submissions/b86ded7c-c9f8-4fc3-ba4a-e6369c1edd27

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_FormalGroupWitt_WeightInvariance
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_SwappedParitySeriesBinomialForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open MvPowerSeries Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution {l : ℕ} (hl : l.Prime) (e : ℕ) (he : 1 ≤ e) :
    0 < l ^ (e - 1) ∧ l ^ (e - 1) < l ^ e ∧ (l ^ e).choose (l ^ (e - 1)) ≠ 0 ∧
      ¬ l ^ 2 ∣ (l ^ e).choose (l ^ (e - 1)) := by
  have hlp := hl.pos
  have hk0 : 0 < l ^ (e - 1) := pow_pos hlp _
  have hN : l ^ e = l * l ^ (e - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hlt : l ^ (e - 1) < l ^ e := by
    rw [hN]
    have := hl.two_le
    nlinarith
  refine ⟨hk0, hlt, (Nat.choose_pos hlt.le).ne', ?_⟩
  have hnd : ∀ f i, i ≤ l ^ f - 1 → ¬ l ∣ (l ^ f - 1).choose i := by
    haveI := Fact.mk hl
    intro f
    induction f with
    | zero =>
      intro i hi
      have hi0 : i = 0 := by
        rw [pow_zero] at hi
        omega
      subst hi0
      rw [Nat.choose_zero_right]
      exact hl.not_dvd_one
    | succ f ih =>
      intro i hi hd
      have hA : 1 ≤ l ^ f := Nat.one_le_pow _ _ hlp
      have hsplit : l ^ (f + 1) - 1 = (l - 1) + l * (l ^ f - 1) := by
        rw [pow_succ']
        have h4 : l * l ^ f = l * (l ^ f - 1) + l := by
          rw [Nat.mul_sub_one]
          have : l ≤ l * l ^ f := by nlinarith
          omega
        rw [h4]
        omega
      have hm1 : (l ^ (f + 1) - 1) % l = l - 1 := by
        rw [hsplit, Nat.add_mul_mod_self_left]
        exact Nat.mod_eq_of_lt (by omega)
      have hd1 : (l ^ (f + 1) - 1) / l = l ^ f - 1 := by
        rw [hsplit, Nat.add_mul_div_left _ _ hlp, Nat.div_eq_of_lt (by omega), zero_add]
      have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := l ^ (f + 1) - 1) (k := i) (p := l)
      rw [hm1, hd1] at h
      have h2 : l ∣ (l - 1).choose (i % l) * (l ^ f - 1).choose (i / l) :=
        Nat.modEq_zero_iff_dvd.1 (h.symm.trans (Nat.modEq_zero_iff_dvd.2 hd))
      rcases (Nat.Prime.dvd_mul hl).1 h2 with h3 | h3
      · have hi' : i % l ≤ l - 1 := by
          have := Nat.mod_lt i hlp
          omega
        have h4 := Nat.choose_mul_factorial_mul_factorial hi'
        have h5 : l ∣ (l - 1).factorial := by
          rw [← h4]
          exact Dvd.dvd.mul_right (Dvd.dvd.mul_right h3 _) _
        rw [hl.dvd_factorial] at h5
        omega
      · refine ih (i / l) ?_ h3
        have h6 : i / l ≤ (l ^ (f + 1) - 1) / l := Nat.div_le_div_right hi
        rw [hd1] at h6
        exact h6
  intro hdiv
  have hid : (l ^ e - 1 + 1) * (l ^ e - 1).choose (l ^ (e - 1) - 1) =
      (l ^ e - 1 + 1).choose (l ^ (e - 1) - 1 + 1) * (l ^ (e - 1) - 1 + 1) := by
    first
    | exact Nat.add_one_mul_choose_eq _ _
    | exact Nat.succ_mul_choose_eq' _ _
    | exact (Nat.choose_mul_succ_eq _ _).symm
  have e1 : l ^ e - 1 + 1 = l ^ e := by omega
  have e2 : l ^ (e - 1) - 1 + 1 = l ^ (e - 1) := by omega
  rw [e1, e2] at hid
  have hC : (l ^ e).choose (l ^ (e - 1)) = l * (l ^ e - 1).choose (l ^ (e - 1) - 1) := by
    apply Nat.eq_of_mul_eq_mul_right hk0
    rw [← hid, hN]
    ring
  rw [hC, pow_two] at hdiv
  have h7 : l ∣ (l ^ e - 1).choose (l ^ (e - 1) - 1) := by
    first
    | exact Nat.dvd_of_mul_dvd_mul_left hlp hdiv
    | exact (Nat.mul_dvd_mul_iff_left hlp).1 hdiv
  exact hnd e _ (by omega) h7
end Formalism.DworkPowerSeriesWeights
