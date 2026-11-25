-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.hostDecompConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:17:41.836039+00:00
-- url     : https://prove2.me/submissions/f390d0ef-711d-4363-9023-77553bb0370c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Galois
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_CoprimeTwoPow
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_Decomp
import Theorems.Thm_Formalism_FrobeniusOrbits_hostDecomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition Formalism.FrobeniusOrbits.Galois
open Decomp
namespace Formalism.FrobeniusOrbits
theorem _root_.solution : HostDecompConj := by
  intro e q d hyp L _ _ ζ a b h σ hσ p hp P _ _
  have hm1 : (-1 : ℤˣ) ≠ 1 := by
    intro h1
    have h2 := congrArg Units.val h1
    simp at h2
  have hq8 : q % 8 = 3 := hyp.2.2.1
  have hd16 : d % 16 = 7 := hyp.2.2.2.1
  have hcq : Nat.Coprime q (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hyp.1 Nat.prime_two).mpr (by omega))
  have hcd : Nat.Coprime d (2 ^ (e + 2)) :=
    Nat.Coprime.pow_right _ ((Nat.coprime_primes hyp.2.1 Nat.prime_two).mpr (by omega))
  have HD := hostDecomp e q d hyp L ζ a b h (ZMod.unitOfCoprime q hcq) (ZMod.unitOfCoprime d hcd)
    (ZMod.coe_unitOfCoprime q hcq) (ZMod.coe_unitOfCoprime d hcd) σ
  rw [hσ] at HD
  have hnotPsi : cc e ∉ Psi e := by
    intro hmem
    have h3 : chD e (cc e) = -1 := by
      first
        | rfl
        | simp [chD, cc, c0]
    exact hm1 (h3.symm.trans (MonoidHom.mem_ker.mp hmem))
  rcases hp with rfl | rfl | ⟨rfl, he2⟩
  · haveI : P.LiesOver (span {(2 : ℤ)}) := by
      have h' : P.LiesOver (span {((2 : ℕ) : ℤ)}) := inferInstance
      simpa using h'
    rw [HD.1 P]
    exact hnotPsi
  · rw [HD.2.1 P]
    rintro ⟨h1, -⟩
    exact hm1 h1
  · rw [HD.2.2 P]
    rintro ⟨k, hk1, hk2⟩
    have hk1' : (-1 : ℤˣ) = (-1) ^ k := hk1
    obtain ⟨j, rfl⟩ : Odd k := by
      rcases Nat.even_or_odd k with hev | hod
      · rw [hev.neg_one_pow] at hk1'
        exact absurd hk1' hm1
      · exact hod
    have hk3 : ((ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) : HGrp e) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hk2.symm
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff] at hk3
    obtain ⟨i, hi⟩ := hk3
    have hpm : (ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) = 1 ∨
        (ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) = -1 := by
      rw [← hi]
      rcases Int.even_or_odd i with hev | hod
      · left
        exact hev.neg_one_zpow
      · right
        exact hod.neg_one_zpow
    have h16 : 16 ∣ 2 ^ (e + 2) := by
      have h4 := Nat.pow_dvd_pow 2 (show 4 ≤ e + 2 by omega)
      simpa using h4
    have hd7 : ((p : ℕ) : ZMod 16) = 7 := by
      rw [← ZMod.natCast_mod, hd16]
      all_goals first | rfl | decide
    have h49 : (7 : ZMod 16) ^ 2 = 1 := by decide
    have h7 : (7 : ZMod 16) ^ (2 * j + 1) = 7 := by
      rw [pow_succ, pow_mul, h49, one_pow, one_mul]
    have hval : ZMod.castHom h16 (ZMod 16)
        ((ZMod.unitOfCoprime p hcd ^ (2 * j + 1) : (ZMod (2 ^ (e + 2)))ˣ) : ZMod (2 ^ (e + 2))) = 7 := by
      rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, map_pow, map_natCast, hd7, h7]
    rcases hpm with h1 | h1
    · rw [h1, Units.val_one, map_one] at hval
      exact absurd hval (by decide)
    · rw [h1, Units.val_neg, Units.val_one, map_neg, map_one] at hval
      exact absurd hval (by decide)
end Formalism.FrobeniusOrbits
