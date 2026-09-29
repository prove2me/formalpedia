-- Prove2me | solution 1 for CongruenceSubgroup.exists_mem_Gamma_mem_Gamma0_intCast_apply_eq_of_coprime_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/180f11dc-04e3-52d6-a981-fb38cb42bb71

import Mathlib
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_intCast_apply_eq_of_coprime_of_dvd

set_option autoImplicit false

open scoped MatrixGroups

namespace P2MtkDiamondLift

theorem crt_fst {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h x).1 = ZMod.castHom (dvd_mul_right m n) (ZMod m) x := by
  show (ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n) x).1 = _
  rw [ZMod.castHom_apply, ZMod.castHom_apply, Prod.fst_zmod_cast]

theorem crt_snd {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h x).2 = ZMod.castHom (dvd_mul_left n m) (ZMod n) x := by
  show (ZMod.castHom (show m.lcm n ∣ m * n by simp [Nat.lcm_dvd_iff]) (ZMod m × ZMod n) x).2 = _
  rw [ZMod.castHom_apply, ZMod.castHom_apply, Prod.snd_zmod_cast]

end P2MtkDiamondLift

theorem solution
    (q M' : ℕ) [NeZero q] [NeZero M'] (hqM' : Nat.Coprime q M') (ℓ : ℕ) (hℓ : ℓ ∣ M') (d : (ZMod ℓ)ˣ) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma q ∧ γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      ((γ 1 1 : ℤ) : ZMod ℓ) = (d : ZMod ℓ) := by
  classical
  haveI : NeZero (q * M') := ⟨mul_ne_zero (NeZero.ne q) (NeZero.ne M')⟩

  obtain ⟨u, hu⟩ := ZMod.unitsMap_surjective (n := ℓ) hℓ d

  set e := ZMod.chineseRemainder hqM' with he
  set w : ZMod (q * M') := e.symm (1, (u : ZMod M')) with hw
  set w' : ZMod (q * M') := e.symm (1, ((u⁻¹ : (ZMod M')ˣ) : ZMod M')) with hw'
  have hww' : w' * w = 1 := by
    apply e.injective
    rw [map_mul, hw, hw', e.apply_symm_apply, e.apply_symm_apply, map_one, Prod.mk_mul_mk, one_mul,
      Units.inv_mul, Prod.mk_one_one]

  let X : SL(2, ZMod (q * M')) := ⟨!![w', 0; 0, w], by rw [Matrix.det_fin_two_of]; simp [hww']⟩
  obtain ⟨γ, hγ⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod (q * M') X
  have hent : ∀ i j : Fin 2, ((γ i j : ℤ) : ZMod (q * M')) = X i j := by
    intro i j
    have := congrArg (fun Y : SL(2, ZMod (q * M')) => Y i j) hγ
    simpa using this
  have e00 : ((γ 0 0 : ℤ) : ZMod (q * M')) = w' := hent 0 0
  have e01 : ((γ 0 1 : ℤ) : ZMod (q * M')) = 0 := hent 0 1
  have e10 : ((γ 1 0 : ℤ) : ZMod (q * M')) = 0 := hent 1 0
  have e11 : ((γ 1 1 : ℤ) : ZMod (q * M')) = w := hent 1 1

  have castq : ∀ (x : ℤ) (y : ZMod (q * M')), ((x : ℤ) : ZMod (q * M')) = y →
      ((x : ℤ) : ZMod q) = (e y).1 := by
    intro x y hxy
    rw [P2MtkDiamondLift.crt_fst, ← hxy, map_intCast]
  have castM : ∀ (x : ℤ) (y : ZMod (q * M')), ((x : ℤ) : ZMod (q * M')) = y →
      ((x : ℤ) : ZMod M') = (e y).2 := by
    intro x y hxy
    rw [P2MtkDiamondLift.crt_snd, ← hxy, map_intCast]
  have hw1 : (e w).1 = 1 := by rw [hw, e.apply_symm_apply]
  have hw'1 : (e w').1 = 1 := by rw [hw', e.apply_symm_apply]
  have hw2 : (e w).2 = (u : ZMod M') := by rw [hw, e.apply_symm_apply]
  refine ⟨γ, ?_, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma_mem]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := castq _ _ e00; rw [hw'1] at this; exact_mod_cast this
    · have := castq _ _ e01; rw [map_zero, Prod.fst_zero] at this; exact_mod_cast this
    · have := castq _ _ e10; rw [map_zero, Prod.fst_zero] at this; exact_mod_cast this
    · have := castq _ _ e11; rw [hw1] at this; exact_mod_cast this
  · rw [CongruenceSubgroup.Gamma0_mem]
    have := castM _ _ e10; rw [map_zero, Prod.snd_zero] at this; exact_mod_cast this
  · have hM : ((γ 1 1 : ℤ) : ZMod M') = (u : ZMod M') := by rw [castM _ _ e11, hw2]
    have := congrArg (ZMod.castHom hℓ (ZMod ℓ)) hM
    rw [map_intCast] at this
    rw [this, ← hu, ZMod.unitsMap_def]
    simp

end S_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_intCast_apply_eq_of_coprime_of_dvd
end P2MW
export P2MW.S_CongruenceSubgroup_exists_mem_Gamma_mem_Gamma0_intCast_apply_eq_of_coprime_of_dvd (solution)
