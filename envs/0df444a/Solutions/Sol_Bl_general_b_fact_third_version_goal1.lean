-- Prove2me | solution 1 for Bl.general_b_fact_third_version.goal1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:43:11.711809+00:00
-- url     : https://prove2.me/submissions/4c7b16f2-5a60-4db5-93b5-ca659959753a

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactThirdVersion_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_third_version
namespace Bl.general_b_fact_third_version
theorem _root_.solution :
  ∀ {E : Type} [inst : Field.{0} E] [@NumberField.{0} E inst] {V : Type} [inst_2 : AddCommGroup.{0} V]
  [inst_3 :
    @Module.{0, 0} E V
      (@DivisionSemiring.toSemiring.{0} E (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2)]
  [inst_4 :
    @Module.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
      (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
        (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
          (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2)]
  [inst_5 :
    @IsScalarTower.{0, 0, 0} (@NumberField.RingOfIntegers.{0} E inst) E V
      (@Algebra.toSMul.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) E
        (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
          (@NumberField.instCommRingRingOfIntegers.{0} E inst))
        (@DivisionSemiring.toSemiring.{0} E (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
        (@NumberField.RingOfIntegers.instAlgebra_1.{0} E inst))
      (@SMulZeroClass.toSMul.{0, 0} E V
        (@AddZero.toZero.{0} V
          (@AddZeroClass.toAddZero.{0} V
            (@AddMonoid.toAddZeroClass.{0} V
              (@SubNegMonoid.toAddMonoid.{0} V
                (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} E V
          (@AddMonoid.toAddZeroClass.{0} V
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
          (@DistribMulAction.toDistribSMul.{0, 0} E V
            (@Semiring.toMonoid.{0} E
              (@DivisionSemiring.toSemiring.{0} E
                (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst))))
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
            (@Module.toDistribMulAction.{0, 0} E V
              (@DivisionSemiring.toSemiring.{0} E (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3))))
      (@SMulZeroClass.toSMul.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
        (@AddZero.toZero.{0} V
          (@AddZeroClass.toAddZero.{0} V
            (@AddMonoid.toAddZeroClass.{0} V
              (@SubNegMonoid.toAddMonoid.{0} V
                (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
        (@DistribSMul.toSMulZeroClass.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
          (@AddMonoid.toAddZeroClass.{0} V
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
          (@DistribMulAction.toDistribSMul.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
            (@Semiring.toMonoid.{0} (@NumberField.RingOfIntegers.{0} E inst)
              (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@NumberField.instCommRingRingOfIntegers.{0} E inst))))
            (@SubNegMonoid.toAddMonoid.{0} V (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
            (@Module.toDistribMulAction.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
              (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4))))]
  (Λ :
    @Submodule.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
      (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
        (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
          (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
      (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4),
  @Submodule.IsLattice.{0, 0, 0} (@NumberField.RingOfIntegers.{0} E inst)
      (@NumberField.instCommRingRingOfIntegers.{0} E inst) E (@Field.toCommRing.{0} E inst)
      (@NumberField.RingOfIntegers.instAlgebra_1.{0} E inst) V (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4
      inst_3 inst_5 inst_5 Λ →
    ∀ (v : V),
      @Exists.{1} Nat fun (m : Nat) ↦
        And (@Ne.{1} Nat m (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))
          (@Membership.mem.{0, 0} V
            (@Submodule.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
              (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
              (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)
            (@SetLike.instMembership.{0, 0}
              (@Submodule.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
                (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                    (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4)
              V
              (@Submodule.setLike.{0, 0} (@NumberField.RingOfIntegers.{0} E inst) V
                (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                  (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} E inst)
                    (@NumberField.instCommRingRingOfIntegers.{0} E inst)))
                (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_4))
            Λ
            (@HSMul.hSMul.{0, 0, 0} E V V
              (@instHSMul.{0, 0} E V
                (@SMulZeroClass.toSMul.{0, 0} E V
                  (@AddZero.toZero.{0} V
                    (@AddZeroClass.toAddZero.{0} V
                      (@AddMonoid.toAddZeroClass.{0} V
                        (@SubNegMonoid.toAddMonoid.{0} V
                          (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))))
                  (@DistribSMul.toSMulZeroClass.{0, 0} E V
                    (@AddMonoid.toAddZeroClass.{0} V
                      (@SubNegMonoid.toAddMonoid.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2))))
                    (@DistribMulAction.toDistribSMul.{0, 0} E V
                      (@Semiring.toMonoid.{0} E
                        (@DivisionSemiring.toSemiring.{0} E
                          (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst))))
                      (@SubNegMonoid.toAddMonoid.{0} V
                        (@AddGroup.toSubNegMonoid.{0} V (@AddCommGroup.toAddGroup.{0} V inst_2)))
                      (@Module.toDistribMulAction.{0, 0} E V
                        (@DivisionSemiring.toSemiring.{0} E
                          (@Semifield.toDivisionSemiring.{0} E (@Field.toSemifield.{0} E inst)))
                        (@AddCommGroup.toAddCommMonoid.{0} V inst_2) inst_3)))))
              (@Nat.cast.{0} E
                (@AddMonoidWithOne.toNatCast.{0} E
                  (@AddGroupWithOne.toAddMonoidWithOne.{0} E
                    (@Ring.toAddGroupWithOne.{0} E (@DivisionRing.toRing.{0} E (@Field.toDivisionRing.{0} E inst)))))
                m)
              v)) := by
  intro E _ _ V _ _ _ _ Λ hΛ v
  have key : ∀ c : E, ∃ m : ℕ, m ≠ 0 ∧ ∃ a : NumberField.RingOfIntegers E,
      (m : E) * c = algebraMap (NumberField.RingOfIntegers E) E a := by
    intro c
    have hc : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (IsAlgebraic.of_finite ℚ c)
    obtain ⟨m, s, hm, h⟩ := hc.exists_nsmul_eq (NumberField.RingOfIntegers E)
    exact ⟨m, hm, s, by rw [← h, nsmul_eq_mul]⟩
  have h1 : ∀ (k : ℕ) (w : V), w ∈ Λ → (k : E) • w ∈ Λ := fun k w hw => by
    rw [Nat.cast_smul_eq_nsmul]; exact Λ.nsmul_mem hw k
  let S : Submodule E V :=
    { carrier := {w | ∃ m : ℕ, m ≠ 0 ∧ (m : E) • w ∈ Λ}
      add_mem' := by
        rintro a b ⟨m, hm, ha⟩ ⟨n, hn, hb⟩
        refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
        rw [Nat.cast_mul, smul_add]
        refine Λ.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact h1 _ _ ha
        · rw [mul_smul]; exact h1 _ _ hb
      zero_mem' := ⟨1, one_ne_zero, by simp⟩
      smul_mem' := by
        rintro c w ⟨m, hm, hw⟩
        obtain ⟨n, hn, a, ha⟩ := key c
        refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
        have e : ((n * m : ℕ) : E) • (c • w) = a • ((m : E) • w) := by
          rw [← algebraMap_smul E a ((m : E) • w), ← ha, Nat.cast_mul, smul_smul, smul_smul]
          congr 1; ring
        rw [e]; exact Λ.smul_mem a hw }
  have hle : Submodule.span E (Λ : Set V) ≤ S :=
    Submodule.span_le.mpr (fun w hw => ⟨1, one_ne_zero, by simpa using hw⟩)
  rw [hΛ.span_eq_top] at hle
  obtain ⟨m, hm, h⟩ := hle (Submodule.mem_top : v ∈ (⊤ : Submodule E V))
  exact ⟨m, hm, h⟩
end Bl.general_b_fact_third_version
