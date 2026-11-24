-- Prove2me | solution 1 for Formalism.HC.Der.root_eq_of_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:31:27.639737+00:00
-- url     : https://prove2.me/submissions/58813970-84ee-40eb-9421-1883f9204491

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycLift
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RootEqOfSubMem
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
namespace Formalism.HC.Der
theorem _root_.solution {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) [hP : P.IsPrime] {m : ℕ}
    (hm : (m : S) ∉ P) {x y : S} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ P) : x = y := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (by simp)
  have hgeom := geom_sum₂_mul x y m
  rw [hx, hy, sub_self] at hgeom
  rcases mul_eq_zero.1 hgeom with hG | hG
  · exfalso
    have hq : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.2 hxy
    have h1 := congrArg (Ideal.Quotient.mk P) hG
    rw [map_sum, map_zero] at h1
    simp only [map_mul, map_pow, hq] at h1
    have h2 : ∀ i ∈ Finset.range m, (Ideal.Quotient.mk P y) ^ i * (Ideal.Quotient.mk P y) ^ (m - 1 - i) =
        (Ideal.Quotient.mk P y) ^ (m - 1) := by
      intro i hi
      rw [← pow_add]
      congr 1
      rw [Finset.mem_range] at hi
      omega
    rw [Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    rcases mul_eq_zero.1 h1 with h3 | h3
    · apply hm
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
      exact h3
    · have h4 : (Ideal.Quotient.mk P y) ^ m = 1 := by rw [← map_pow, hy, map_one]
      have h5 : (Ideal.Quotient.mk P y) ^ m = 0 := by
        rw [show m = m - 1 + 1 by omega, pow_succ, h3, zero_mul]
      rw [h4] at h5
      exact one_ne_zero h5
  · exact sub_eq_zero.1 hG
end Formalism.HC.Der
