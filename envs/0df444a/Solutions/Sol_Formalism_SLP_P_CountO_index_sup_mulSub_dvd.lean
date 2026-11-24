-- Prove2me | solution 1 for Formalism.SLP.P.CountO.index_sup_mulSub_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:49:07.35814+00:00
-- url     : https://prove2.me/submissions/610a2794-46e9-422d-8c72-30531f5c890e

import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SubgroupIndexCounts_CountO
import Theorems.Thm_Formalism_SLP_P_CountO_nsmul_mem_mulSub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.SLP Formalism.SLP.P
open Formalism.SLP.P.CountO
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
namespace Formalism.SLP.P.CountO
theorem _root_.solution (N : Submodule R X) {a b : ℕ} (hab : a.Coprime b)
    (ha : 0 < a) (hb : 0 < b) (hN : N.toAddSubgroup.index = a * b) :
    (N ⊔ mulSub R X a).toAddSubgroup.index ∣ a := by
  set K := N ⊔ mulSub R X a with hK
  have hle : N.toAddSubgroup ≤ K.toAddSubgroup := Submodule.toAddSubgroup_mono le_sup_left
  have hdvd : K.toAddSubgroup.index ∣ a * b := hN ▸ AddSubgroup.index_dvd_of_le hle
  have hne : K.toAddSubgroup.index ≠ 0 :=
    fun h => (Nat.mul_pos ha hb).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  have hcop : Nat.Coprime K.toAddSubgroup.index b := by
    apply Nat.coprime_of_dvd
    intro q hq hqK hqb
    have : Fact q.Prime := ⟨hq⟩
    have : Finite (X ⧸ K.toAddSubgroup) := Nat.finite_of_card_ne_zero hne
    obtain ⟨z, hz⟩ := exists_prime_addOrderOf_dvd_card' (G := X ⧸ K.toAddSubgroup) q hqK
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    have hax : a • (x : X ⧸ K.toAddSubgroup) = 0 := by
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
      exact Submodule.mem_sup_right (nsmul_mem_mulSub a x)
    have hqa : q ∣ a := hz ▸ addOrderOf_dvd_of_nsmul_eq_zero hax
    have h1 : q ∣ Nat.gcd a b := Nat.dvd_gcd hqa hqb
    rw [hab.gcd_eq_one, Nat.dvd_one] at h1
    exact hq.one_lt.ne' h1
  exact hcop.dvd_of_dvd_mul_right hdvd
end Formalism.SLP.P.CountO
