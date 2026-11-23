-- Prove2me | solution 1 for Formalism.HC.Der.Rd.KK_gcd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:17:02.702461+00:00
-- url     : https://prove2.me/submissions/a544edd8-e3ee-41b1-b9de-e4f1f8d5490d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_RdArith
import Theorems.Thm_Formalism_HC_Der_Rd_mem_ker_iff
import Theorems.Thm_Formalism_HC_Der_Rd_mem_KK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ArithmeticFunction Finset
noncomputable section
namespace Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
private theorem coe_unitsMap_eq_natCast_val_of_dvd {d : ℕ} (hd : d ∣ N) (u : (ZMod N)ˣ) :
    ((ZMod.unitsMap hd u : (ZMod d)ˣ) : ZMod d) = (((u : ZMod N).val : ℕ) : ZMod d) := by
  rw [← ZMod.cast_eq_val]
  first
  | rfl
  | exact ZMod.unitsMap_val hd u
  | simp [ZMod.unitsMap_def]
private theorem mem_KK_iff_mem_ker_unitsMap {f : ℕ} (hf : f ∣ N) {u : (ZMod N)ˣ} :
    u ∈ KK N f ↔ u ∈ (ZMod.unitsMap hf).ker := by
  rw [mem_KK, mem_ker_iff hf]
end Formalism.HC.Der.Rd
end
end

set_option autoImplicit false
open ArithmeticFunction Finset
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der Formalism.HC.Der.Rd
variable {N : ℕ} [NeZero N]
namespace Formalism.HC.Der.Rd
theorem _root_.solution (U : Subgroup (ZMod N)ˣ) {a b : ℕ} (ha : a ∣ N) (hb : b ∣ N) (h1 : ∀ u ∈ KK N a, u ∈ U)
    (h2 : ∀ u ∈ KK N b, u ∈ U) : ∀ u ∈ KK N (Nat.gcd a b), u ∈ U := by
  intro u hu
  rw [mem_KK] at hu
  have hL : Nat.lcm a b ∣ N := Nat.lcm_dvd ha hb
  obtain ⟨k, hka, hkb⟩ := Nat.chineseRemainder' (hu.symm : 1 ≡ (u : ZMod N).val [MOD Nat.gcd a b])
  have hca : Nat.Coprime k a := by
    unfold Nat.Coprime
    rw [hka.gcd_eq, Nat.gcd_one_left]
  have hub : Nat.Coprime (u : ZMod N).val b :=
    Nat.Coprime.coprime_dvd_right hb (ZMod.val_coe_unit_coprime u)
  have hcb : Nat.Coprime k b := by
    unfold Nat.Coprime
    rw [hkb.gcd_eq]
    exact hub
  have hcop : Nat.Coprime k (Nat.lcm a b) :=
    Nat.Coprime.coprime_dvd_right (Nat.lcm_dvd_mul a b) (Nat.Coprime.mul_right hca hcb)
  obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hL (ZMod.unitOfCoprime k hcop)
  have hvk : (v : ZMod N).val ≡ k [MOD Nat.lcm a b] := by
    have h3 := congrArg (fun w : (ZMod (Nat.lcm a b))ˣ => (w : ZMod (Nat.lcm a b))) hv
    simp only [ZMod.coe_unitOfCoprime] at h3
    rw [coe_unitsMap_eq_natCast_val_of_dvd] at h3
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h3
  have hva : v ∈ U := h1 v (by
    rw [mem_KK]
    exact (hvk.of_dvd (Nat.dvd_lcm_left a b)).trans hka)
  have hvb : v⁻¹ * u ∈ U := h2 _ (by
    rw [mem_KK_iff_mem_ker_unitsMap hb, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one]
    apply Units.ext
    rw [coe_unitsMap_eq_natCast_val_of_dvd, coe_unitsMap_eq_natCast_val_of_dvd, ZMod.natCast_eq_natCast_iff]
    exact (hvk.of_dvd (Nat.dvd_lcm_right a b)).trans hkb)
  have h4 := mul_mem hva hvb
  rwa [mul_inv_cancel_left] at h4
end Formalism.HC.Der.Rd
