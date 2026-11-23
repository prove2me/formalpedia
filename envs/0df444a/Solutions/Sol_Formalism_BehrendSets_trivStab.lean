-- Prove2me | solution 1 for Formalism.BehrendSets.trivStab
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:21:47.541864+00:00
-- url     : https://prove2.me/submissions/2483da23-40ed-4f16-96a0-ccdf5393e15a

import Definitions.Def_Formalism_BehrendSets_StatementE
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TotientLeOfIsPrimitiveRoot
import Theorems.Thm_Formalism_BehrendSets_Stab_sub_one_le_of_pow_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Module Matrix
open Formalism Formalism.BehrendSets
namespace Formalism.BehrendSets
theorem _root_.solution : TrivStab := by
  intro E _ _ k g hg hdeg Γ hfin hp
  have := Fact.mk hg
  by_contra hne
  have hcard : g ∣ Nat.card Γ := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self g hn0
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' g hcard
  have hA : orderOf (x : GL (Fin k) E) = g := by rw [Subgroup.orderOf_coe]; exact hx
  have hMg : ((x : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) ^ g = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hA, pow_orderOf_eq_one, Units.val_one]
  have hM1 : ((x : GL (Fin k) E) : Matrix (Fin k) (Fin k) E) ≠ 1 := by
    intro h
    have h1 : (x : GL (Fin k) E) = 1 := Units.ext h
    rw [h1, orderOf_one] at hA
    exact hg.one_lt.ne hA
  have := Stab.sub_one_le_of_pow_eq_one hg _ hMg hM1
  omega
end Formalism.BehrendSets
