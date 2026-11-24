-- Prove2me | solution 1 for Formalism.LT.PadicP.ltLog_funEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:49:32.335013+00:00
-- url     : https://prove2.me/submissions/165c4a3b-d837-4c92-8a64-7c089706e359

import Definitions.Def_Formalism_TorsionNormIteration_InvIntegralOfClass
import Definitions.Def_Formalism_FormalGroupLog_LogDeterminesLaw
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_IsHomOfSubstEqSmul
import Theorems.Thm_Formalism_LT_PadicP_coeff_ltLog
import Theorems.Thm_Formalism_LT_PadicP_isPow_mul_iff
import Theorems.Thm_Formalism_LT_PadicP_isPow_iff_of_not_dvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open PowerSeries
namespace Formalism.LT.PadicP
open Formalism.G
section LtLog
variable {p : ℕ} [hp : Fact p.Prime]
private theorem coeff_subst_X_pow_lemma (f : PowerSeries ℚ_[p]) (n : ℕ) :
    coeff n (f.subst ((X : PowerSeries ℚ_[p]) ^ p)) = if p ∣ n then coeff (n / p) f else 0 := by
  have ha : HasSubst ((X : PowerSeries ℚ_[p]) ^ p) :=
    HasSubst.of_constantCoeff_zero' (by simp [hp.out.ne_zero])
  change MvPowerSeries.coeff (Finsupp.single () n) _ = _
  rw [coeff_subst ha]
  change ∑ᶠ d, coeff d f • coeff n (((X : PowerSeries ℚ_[p]) ^ p) ^ d) = _
  simp_rw [← pow_mul, coeff_X_pow]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [finsum_eq_single _ m]
    · rw [if_pos rfl, smul_eq_mul, mul_one, Nat.mul_div_cancel_left m hp.out.pos]
    · intro d hd
      rw [if_neg (fun h' => hd (Nat.eq_of_mul_eq_mul_left hp.out.pos h').symm), smul_zero]
  · refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    rw [if_neg (fun h' => h ⟨d, h'⟩), smul_zero]
end LtLog
end Formalism.LT.PadicP
namespace Formalism.LT
end Formalism.LT
end
end

set_option autoImplicit false
noncomputable section
open PowerSeries
open Formalism Formalism.LT Formalism.LT.PadicP
open Formalism.G
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.LT.PadicP
theorem _root_.solution :
    ltLog p - (p : ℚ_[p])⁻¹ • (ltLog p).subst ((X : PowerSeries ℚ_[p]) ^ p) = X := by
  ext n
  rw [map_sub, PowerSeries.coeff_smul, smul_eq_mul, coeff_subst_X_pow_lemma, coeff_X]
  simp only [coeff_ltLog]
  by_cases hd : p ∣ n
  · obtain ⟨m, rfl⟩ := hd
    have hne : p * m ≠ 1 := by
      intro h
      have h1 := Nat.le_of_dvd one_pos ⟨m, h.symm⟩
      have := hp.out.two_le
      omega
    rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.out.pos, if_neg hne]
    by_cases hk : ∃ k, p ^ k = m
    · rw [if_pos ((isPow_mul_iff m).mpr hk), if_pos hk, Nat.cast_mul, mul_inv, sub_self]
    · rw [if_neg (fun h => hk ((isPow_mul_iff m).mp h)), if_neg hk, mul_zero, sub_zero]
  · rw [if_neg hd, mul_zero, sub_zero]
    by_cases h1 : n = 1
    · subst h1
      rw [if_pos ⟨0, pow_zero p⟩, if_pos rfl, Nat.cast_one, inv_one]
    · rw [if_neg (fun h => h1 ((isPow_iff_of_not_dvd n hd).mp h)), if_neg h1]
end Formalism.LT.PadicP
