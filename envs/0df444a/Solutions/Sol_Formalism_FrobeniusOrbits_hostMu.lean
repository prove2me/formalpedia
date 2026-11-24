-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostMu
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:30:41.631244+00:00
-- url     : https://prove2.me/submissions/bf0f483d-d59f-4efe-bee0-aa49ea493b5f

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_FrobMulInertia
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_MuCardLeTwo
import Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_no_odd
import Theorems.Thm_Formalism_FrobeniusOrbits_Mu_mu_no_four
import Theorems.Thm_Formalism_FrobeniusOrbits_HostHyp_toHypOdd
import Theorems.Thm_Formalism_TwoAdicCyclotomicDecomposition_HypQD_toHypOdd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
open Mu
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostMu := by
  intro e q d hq hq3 L _ _ ζ a b h x hx
  obtain ⟨m, hm, hxm⟩ := hx
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, hxm⟩
  have hn0 : 0 < orderOf x := orderOf_pos_iff.mpr hfin
  have hxo : IsPrimitiveRoot x (orderOf x) := IsPrimitiveRoot.orderOf x
  have hcoe : ∀ (y : hostE ζ a b) (k : ℕ), IsPrimitiveRoot y k → IsPrimitiveRoot (y : L) k :=
    fun y k hy => IsPrimitiveRoot.coe_submonoidClass_iff.mpr hy
  have h2 : x ^ 2 = 1 := by
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (orderOf x) with ⟨k, hk⟩ | ⟨p, hp, hpn, hodd⟩
    · by_cases hk2 : 2 ≤ k
      · exfalso
        have hsplit : orderOf x = 2 ^ (k - 2) * 4 := by
          rw [hk, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
          congr 1
          omega
        have hy := IsPrimitiveRoot.pow hn0 hxo hsplit
        exact mu_no_four hq.toHypOdd h ((x ^ (2 ^ (k - 2)) : hostE ζ a b) : L)
          (x ^ (2 ^ (k - 2))).2 (hcoe _ _ hy)
      · have hd : orderOf x ∣ 2 := by
          rw [hk]
          exact (pow_dvd_pow 2 (by omega : k ≤ 1)).trans (by norm_num)
        exact orderOf_dvd_iff_pow_eq_one.mp hd
    · exfalso
      obtain ⟨c, hc⟩ := hpn
      have hy := IsPrimitiveRoot.pow hn0 hxo (show orderOf x = c * p by rw [hc, mul_comm])
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact (Nat.not_even_iff_odd.mpr hodd) even_two
      exact mu_no_odd hq hq3 h p hp hp2 _ (hcoe _ _ hy)
  exact mul_self_eq_one_iff.mp (by rw [← sq]; exact h2)
end Formalism.FrobeniusOrbits
