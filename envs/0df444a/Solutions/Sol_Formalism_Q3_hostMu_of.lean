-- Prove2me | solution 1 for Formalism.Q3.hostMu_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:11.704907+00:00
-- url     : https://prove2.me/submissions/dfb04690-99a2-4709-8ab3-dd8abeb2a284

import Mathlib
import Definitions.Def_Formalism_CMTypeGalois_StatementField
import Definitions.Def_Formalism_CMTypeGalois_CMTypeFrobenius_HostMu
import Theorems.Thm_Formalism_Q3_CMRootsOfUnity_no_prime_root
import Theorems.Thm_Formalism_Q3_CMRootsOfUnity_no_four
import Theorems.Thm_Formalism_Q3_CMRootsOfUnity_no_three

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Polynomial
noncomputable section
open Formalism Formalism.Q3
open CMRootsOfUnity
namespace Formalism.Q3
theorem _root_.solution (hK : MQKummer) (hH : HostGalois) : HostMu := by
  intro q hq hq3 E _ _ α hα ζ ⟨n, hn, hζn⟩
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hζn⟩
  have hmpos : 0 < orderOf ζ := orderOf_pos_iff.2 hfin
  have hprim : IsPrimitiveRoot ζ (orderOf ζ) := IsPrimitiveRoot.orderOf ζ
  have hodd : ∀ {p : ℕ}, p.Prime → p ∣ orderOf ζ → p = 2 := by
    intro p hp hpm
    obtain ⟨k, hk⟩ := hpm
    have hη : IsPrimitiveRoot (ζ ^ k) p := hprim.pow hmpos (by rw [hk, mul_comm])
    by_contra hp2
    by_cases hp3 : p = 3
    · subst hp3
      exact no_three hK hq hq3 hα (ζ ^ k) hη
    · exact no_prime_root hH hq hα p hp hp2 hp3 (ζ ^ k) hη
  have h4 : ¬ 4 ∣ orderOf ζ := by
    rintro ⟨k, hk⟩
    exact no_four hK hq hα (ζ ^ k) (hprim.pow hmpos (by rw [hk, mul_comm]))
  have hm2 : orderOf ζ ∣ 2 := by
    have hpow := Nat.eq_prime_pow_of_unique_prime_dvd hmpos.ne' hodd
    rw [hpow] at h4 ⊢
    rcases h : (orderOf ζ).primeFactorsList.length with _ | _ | a
    · simp
    · simp
    · exfalso
      rw [h] at h4
      exact h4 (by
        have : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [this]
        exact pow_dvd_pow 2 (by omega))
  have hζ2 : ζ * ζ = 1 := by
    rw [← sq]
    exact (hprim.pow_eq_one_iff_dvd 2).2 hm2
  exact mul_self_eq_one_iff.1 hζ2
end Formalism.Q3
