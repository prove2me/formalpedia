-- Prove2me | solution 1 for Formalism.L2.Th1.E.Ser.rootInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:59:12.859717+00:00
-- url     : https://prove2.me/submissions/82105ad5-ce59-4dcd-8f6f-ad81754d1b7a

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementU
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_sub
import Theorems.Thm_Formalism_L2_Th1_E_Ser_intS_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.E.Ser
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.L2.Th1.E.Ser
theorem _root_.solution {N : ℕ} {g : K⟦X⟧} (hN : ‖(N : K)‖ = 1) (h0 : constantCoeff g = 1)
    (hg : IntS (g ^ N)) : IntS g := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [coeff_zero_eq_constantCoeff_apply, h0]; simp
    · set A : K⟦X⟧ := PowerSeries.mk (fun i => if i < n then coeff i g else 0) with hA
      have hAint : IntS A := by
        intro i
        rw [hA, coeff_mk]
        split_ifs with hi
        · exact ih i hi
        · simp
      have hA0 : constantCoeff A = 1 := by
        rw [← coeff_zero_eq_constantCoeff_apply, hA, coeff_mk, if_pos hn,
          coeff_zero_eq_constantCoeff_apply, h0]
      have hdvd : (X : K⟦X⟧) ^ n ∣ g - A := by
        rw [X_pow_dvd_iff]
        intro m hm
        rw [map_sub, hA, coeff_mk, if_pos hm, sub_self]
      obtain ⟨B, hB⟩ := hdvd
      have hB0 : constantCoeff B = coeff n g := by
        have h1 : coeff (0 + n) (X ^ n * B) = coeff 0 B := coeff_X_pow_mul B n 0
        rw [← hB, zero_add, map_sub, hA, coeff_mk, if_neg (lt_irrefl n), sub_zero,
          coeff_zero_eq_constantCoeff_apply] at h1
        exact h1.symm
      set S : K⟦X⟧ := ∑ i ∈ range N, g ^ i * A ^ (N - 1 - i) with hS
      have hS0 : constantCoeff S = (N : K) := by
        rw [hS, map_sum]
        simp [h0, hA0]
      have hfac : g ^ N - A ^ N = X ^ n * (B * S) := by
        rw [← (Commute.all g A).geom_sum₂_mul N, hB, ← hS]
        ring
      have h2 : coeff n (g ^ N - A ^ N) = coeff n g * (N : K) := by
        have h1 : coeff (0 + n) (X ^ n * (B * S)) = coeff 0 (B * S) := coeff_X_pow_mul _ n 0
        have h4 : constantCoeff (B * S) = coeff n g * (N : K) := by rw [map_mul, hB0, hS0]
        rw [zero_add, coeff_zero_eq_constantCoeff_apply, h4] at h1
        rw [hfac, h1]
      have h3 : ‖coeff n (g ^ N - A ^ N)‖ ≤ 1 := intS_sub hg (intS_pow hAint N) n
      rwa [h2, norm_mul, hN, mul_one] at h3
end Formalism.L2.Th1.E.Ser
