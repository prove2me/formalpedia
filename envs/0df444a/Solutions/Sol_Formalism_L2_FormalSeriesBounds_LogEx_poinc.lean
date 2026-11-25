-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.LogEx.poinc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:10:46.935547+00:00
-- url     : https://prove2.me/submissions/74aa23f0-474c-4d61-83ed-2cc0693af991

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PoincEx
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_LogEx_poinc_ex

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.LogEx
namespace Formalism.L2.FormalSeriesBounds.LogEx
theorem _root_.solution {σ : Type} [Fintype σ] {K : Type} [Field K] [CharZero K] (ω : σ → MvPowerSeries σ K)
    (hω : ∀ j l, MvPowerSeries.pderiv K j (ω l) = MvPowerSeries.pderiv K l (ω j)) :
    ∃ g : MvPowerSeries σ K, MvPowerSeries.constantCoeff g = 0 ∧ ∀ j, MvPowerSeries.pderiv K j g = ω j := by
  classical
  obtain ⟨g, hg⟩ := poinc_ex (fun μ : σ →₀ ℕ => ((μ.degree : ℕ) : K)⁻¹ *
    ∑ l, if μ l = 0 then 0 else coeff (μ - Finsupp.single l 1) (ω l))
  refine ⟨g, ?_, fun j => ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, hg]
    simp
  · ext ν
    rw [coeff_pderiv, hg]
    have hdeg : (((ν + Finsupp.single j 1).degree : ℕ) : K) = (ν.degree : K) + 1 := by
      simp
    have hterm : ∀ l, (if (ν + Finsupp.single j 1 : σ →₀ ℕ) l = 0 then 0 else
        coeff (ν + Finsupp.single j 1 - Finsupp.single l 1) (ω l)) * ((ν j : K) + 1) =
        coeff ν (ω j) * (((ν + Finsupp.single j 1 : σ →₀ ℕ) l : ℕ) : K) := by
      intro l
      by_cases hlj : l = j
      · subst hlj
        have h0 : (ν + Finsupp.single l 1 : σ →₀ ℕ) l ≠ 0 := by simp
        rw [if_neg h0, add_tsub_cancel_right]
        simp
      · have hl : (ν + Finsupp.single j 1 : σ →₀ ℕ) l = ν l := by
          simp [Ne.symm hlj]
        by_cases hνl : ν l = 0
        · rw [if_pos (by rw [hl]; exact hνl), hl, hνl]
          simp
        · rw [if_neg (by rw [hl]; exact hνl), hl]
          have h1 := congrArg (coeff (ν - Finsupp.single l 1)) (hω j l)
          rw [coeff_pderiv, coeff_pderiv] at h1
          have e1 : ν - Finsupp.single l 1 + Finsupp.single j 1 = ν + Finsupp.single j 1 - Finsupp.single l 1 := by
            ext t
            simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
            split_ifs with h2 h3 h3 <;> (try subst h2) <;> (try subst h3) <;> omega
          have e2 : ν - Finsupp.single l 1 + Finsupp.single l 1 = ν := by
            ext t
            simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
            split_ifs with h2 <;> (try subst h2) <;> omega
          have e3 : (ν - Finsupp.single l 1 : σ →₀ ℕ) j = ν j := by
            simp [Finsupp.tsub_apply, hlj]
          have e4 : (((ν - Finsupp.single l 1 : σ →₀ ℕ) l : ℕ) : K) + 1 = (ν l : K) := by
            have : (ν - Finsupp.single l 1 : σ →₀ ℕ) l + 1 = ν l := by
              rw [Finsupp.tsub_apply, Finsupp.single_eq_same]
              omega
            exact_mod_cast this
          rw [e1, e2, e3, e4] at h1
          rw [h1]
    have hsum : ∑ l, (((ν + Finsupp.single j 1 : σ →₀ ℕ) l : ℕ) : K) = (ν.degree : K) + 1 := by
      rw [← hdeg, Finsupp.degree_eq_sum]
      push_cast
      rfl
    have hne : (ν.degree : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero ν.degree
    have hS : (∑ l, (if (ν + Finsupp.single j 1 : σ →₀ ℕ) l = 0 then 0 else
        coeff (ν + Finsupp.single j 1 - Finsupp.single l 1) (ω l))) * ((ν j : K) + 1) =
        coeff ν (ω j) * ((ν.degree : K) + 1) := by
      rw [Finset.sum_mul, ← hsum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => hterm l
    rw [mul_assoc, hS, hdeg, mul_comm (coeff ν (ω j)), ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
end Formalism.L2.FormalSeriesBounds.LogEx
