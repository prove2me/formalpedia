-- Prove2me | solution 1 for Formalism.HC.D7.exists_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:07:15.213638+00:00
-- url     : https://prove2.me/submissions/6972e545-edd9-4327-b388-682217967253

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_HC_D7_cop_2q
import Theorems.Thm_Formalism_HC_D7_cop_2d
import Theorems.Thm_Formalism_HC_D7_cop_qd
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_two_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH
namespace Formalism.HC.D7
theorem _root_.solution (x y z : ℕ) (hx : Nat.Coprime x (2 ^ (e + 2))) (hy : Nat.Coprime y q) (hz : Nat.Coprime z d) :
    ∃ u : (ZMod (2 ^ (e + 2) * q * d))ˣ, (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ x [MOD 2 ^ (e + 2)] ∧
      (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD q] ∧ (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ z [MOD d] := by
  have h2q := cop_2q e hH
  have h2qd : Nat.Coprime (2 ^ (e + 2) * q) d := Nat.Coprime.mul (cop_2d e hH) (cop_qd hH)
  obtain ⟨n, hn1, hn2⟩ := Nat.chineseRemainder h2q x y
  obtain ⟨m, hm12, hm3⟩ := Nat.chineseRemainder h2qd n z
  have hm1 : m ≡ x [MOD 2 ^ (e + 2)] := (hm12.of_dvd (dvd_mul_right _ _)).trans hn1
  have hm2 : m ≡ y [MOD q] := (hm12.of_dvd (dvd_mul_left _ _)).trans hn2
  have c1 : Nat.Coprime m (2 ^ (e + 2)) := by
    unfold Nat.Coprime
    rw [hm1.gcd_eq]
    exact hx
  have c2 : Nat.Coprime m q := by
    unfold Nat.Coprime
    rw [hm2.gcd_eq]
    exact hy
  have c3 : Nat.Coprime m d := by
    unfold Nat.Coprime
    rw [hm3.gcd_eq]
    exact hz
  have cN : Nat.Coprime m (2 ^ (e + 2) * q * d) := (c1.mul_right c2).mul_right c3
  refine ⟨ZMod.unitOfCoprime m cN, ?_, ?_, ?_⟩ <;> rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  · exact ((Nat.mod_modEq m _).of_dvd (two_dvd e q d)).trans hm1
  · exact ((Nat.mod_modEq m _).of_dvd (q_dvd e q d)).trans hm2
  · exact ((Nat.mod_modEq m _).of_dvd (d_dvd e q d)).trans hm3
end Formalism.HC.D7
