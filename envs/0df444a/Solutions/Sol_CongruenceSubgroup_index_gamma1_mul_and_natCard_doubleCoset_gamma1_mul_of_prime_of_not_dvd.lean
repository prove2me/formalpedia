-- Prove2me | solution 1 for CongruenceSubgroup.index_gamma1_mul_and_natCard_doubleCoset_gamma1_mul_of_prime_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/77e038f2-841d-5e25-ad45-42f9ae7ceded

import Mathlib
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Theorems.Thm_CongruenceSubgroup_index_gamma1_mul_eq_of_prime_of_not_dvd
import Theorems.Thm_CongruenceSubgroup_two_mul_index_gamma1_sup_zpowers_neg_one
import Theorems.Thm_DoubleCoset_natCard_quotient_eq_natCard_quotient_map_of_surjective
import Theorems.Thm_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_eq_two_mul_of_five_le
import Theorems.Thm_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_mul_of_coprime
import Theorems.Thm_CongruenceSubgroup_natCard_doubleCoset_gamma1_map_T_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_index_gamma1_mul_and_natCard_doubleCoset_gamma1_mul_of_prime_of_not_dvd

set_option autoImplicit false

open scoped MatrixGroups

namespace CongruenceSubgroup p2m_export "CongruenceSubgroup" "Gamma1_mem Gamma1 index_gamma1_mul_eq_of_prime_of_not_dvd two_mul_index_gamma1_sup_zpowers_neg_one natCard_doubleCoset_gamma1_map_T_eq_two_mul_of_five_le natCard_doubleCoset_gamma1_map_T_mul_of_coprime natCard_doubleCoset_gamma1_map_T_of_prime" end CongruenceSubgroup
p2m_open_scoped "CongruenceSubgroup" in

theorem CongruenceSubgroup.ker_map_le_gamma1 (N : ℕ) [NeZero N] :
    ((Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod N)))).ker ≤ CongruenceSubgroup.Gamma1 N := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have h := fun i j => congrArg (fun A : SL(2, ZMod N) => (A : Matrix (Fin 2) (Fin 2) (ZMod N)) i j) hg
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.SpecialLinearGroup.coe_one, eq_intCast] at h
  rw [CongruenceSubgroup.Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · simpa using h 0 0
  · simpa using h 1 1
  · simpa using h 1 0

theorem solution
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (p : ℕ) [Fact p.Prime] (hpM : ¬ p ∣ M) :
    (CongruenceSubgroup.Gamma1 (M * p) ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index =
      (p ^ 2 - 1) * (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index ∧
    Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 (M * p) : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) =
      2 * (p - 1) * Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
  have hMp5 : 5 ≤ M * p := le_trans hM (Nat.le_mul_of_pos_right M hp.pos)
  refine ⟨?_, ?_⟩
  ·
    have h1 := CongruenceSubgroup.index_gamma1_mul_eq_of_prime_of_not_dvd M p hpM
    have h2 := CongruenceSubgroup.two_mul_index_gamma1_sup_zpowers_neg_one (M * p) (by omega)
    have h3 := CongruenceSubgroup.two_mul_index_gamma1_sup_zpowers_neg_one M (by omega)
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    rw [h2, h1, ← h3]; ring
  ·
    have c2Mp := DoubleCoset.natCard_quotient_eq_natCard_quotient_map_of_surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod (M * p)))) (ModularCurve.surjective_specialLinearGroup_map_zmod (M * p)) (CongruenceSubgroup.Gamma1 (M * p))
      (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) (CongruenceSubgroup.ker_map_le_gamma1 (M * p))
    have c2M := DoubleCoset.natCard_quotient_eq_natCard_quotient_map_of_surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod M))) (ModularCurve.surjective_specialLinearGroup_map_zmod M) (CongruenceSubgroup.Gamma1 M)
      (Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) (CongruenceSubgroup.ker_map_le_gamma1 M)
    have c3Mp := CongruenceSubgroup.natCard_doubleCoset_gamma1_map_T_eq_two_mul_of_five_le (M * p) hMp5
    have c3M := CongruenceSubgroup.natCard_doubleCoset_gamma1_map_T_eq_two_mul_of_five_le M hM
    have c4 := CongruenceSubgroup.natCard_doubleCoset_gamma1_map_T_mul_of_coprime M p
      ((Nat.coprime_comm).mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpM))
    have c5 := CongruenceSubgroup.natCard_doubleCoset_gamma1_map_T_of_prime p
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    rw [c2Mp, ← c3Mp, c4, c3M, c5, c2M]
    ring

end S_CongruenceSubgroup_index_gamma1_mul_and_natCard_doubleCoset_gamma1_mul_of_prime_of_not_dvd
end P2MW
export P2MW.S_CongruenceSubgroup_index_gamma1_mul_and_natCard_doubleCoset_gamma1_mul_of_prime_of_not_dvd (solution)
