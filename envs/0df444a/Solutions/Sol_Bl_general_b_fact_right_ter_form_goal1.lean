-- Prove2me | solution 1 for Bl.general_b_fact_right_ter_form.goal1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:08:54.607717+00:00
-- url     : https://prove2.me/submissions/c887ded1-0c45-4888-9038-88cfe3469d5d

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightTerForm_Imports

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_right_ter_form
namespace Bl.general_b_fact_right_ter_form
theorem _root_.solution :
  ∀ {L : Type} [inst : Field.{0} L] [inst_1 : @NumberField.{0} L inst] (x : L) (c : Int),
  @Eq.{1} L
      (@HPow.hPow.{0, 0, 0} L Nat L
        (@instHPow.{0, 0} L Nat
          (@NPow.toPow.{0} L
            (@Monoid.toNPow.{0} L
              (@Semiring.toMonoid.{0} L
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))))))
        x (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@Int.cast.{0} L
        (@AddGroupWithOne.toIntCast.{0} L
          (@Ring.toAddGroupWithOne.{0} L (@DivisionRing.toRing.{0} L (@Field.toDivisionRing.{0} L inst))))
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
            (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4)))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2))) c))
          (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))) →
    ∀
      (P :
        @Ideal.{0} (@NumberField.RingOfIntegers.{0} L inst)
          (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
            (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
              (@NumberField.instCommRingRingOfIntegers.{0} L inst))))
      [hP :
        @Ideal.IsPrime.{0} (@NumberField.RingOfIntegers.{0} L inst)
          (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
            (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
              (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
          P]
      [@Ideal.LiesOver.{0, 0} Int Int.instCommSemiring (@NumberField.RingOfIntegers.{0} L inst)
          (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
            (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
              (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
          (@Ring.toIntAlgebra.{0} (@NumberField.RingOfIntegers.{0} L inst)
            (@CommRing.toRing.{0} (@NumberField.RingOfIntegers.{0} L inst)
              (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
          P
          (@Ideal.span.{0} Int (@CommSemiring.toSemiring.{0} Int Int.instCommSemiring)
            (@Singleton.singleton.{0, 0} Int (Set.{0} Int) (@Set.instSingletonSet.{0} Int)
              (@OfNat.ofNat.{0} Int (nat_lit 2) (@instOfNat (nat_lit 2)))))]
      (σ :
        @AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
          (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
          (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
          (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
          (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)),
      @Membership.mem.{0, 0}
          (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
            (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
            (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
            (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
            (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
          (@Subgroup.{0}
            (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)))
          (@SetLike.instMembership.{0, 0}
            (@Subgroup.{0}
              (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
              (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)))
            (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            (@Subgroup.instSetLike.{0}
              (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
              (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))))
          (@MulAction.stabilizer.{0, 0}
            (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            (@Ideal.{0} (@NumberField.RingOfIntegers.{0} L inst)
              (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                  (@NumberField.instCommRingRingOfIntegers.{0} L inst))))
            (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            (@DistribMulAction.toMulAction.{0, 0}
              (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionSemiring.toSemiring.{0} L
                  (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
              (@Ideal.{0} (@NumberField.RingOfIntegers.{0} L inst)
                (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                  (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                    (@NumberField.instCommRingRingOfIntegers.{0} L inst))))
              (@DivInvMonoid.toMonoid.{0}
                (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                  (@DivisionSemiring.toSemiring.{0} L
                    (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                  (@DivisionSemiring.toSemiring.{0} L
                    (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                  (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                  (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                (@Group.toDivInvMonoid.{0}
                  (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                  (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))))
              (@AddMonoidWithOne.toAddMonoid.{0}
                (@Ideal.{0} (@NumberField.RingOfIntegers.{0} L inst)
                  (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                    (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                      (@NumberField.instCommRingRingOfIntegers.{0} L inst))))
                (@AddCommMonoidWithOne.toAddMonoidWithOne.{0}
                  (@Ideal.{0} (@NumberField.RingOfIntegers.{0} L inst)
                    (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                      (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                        (@NumberField.instCommRingRingOfIntegers.{0} L inst))))
                  (@Submodule.instAddCommMonoidWithOne.{0, 0} (@NumberField.RingOfIntegers.{0} L inst)
                    (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                      (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                        (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
                    (@NumberField.RingOfIntegers.{0} L inst)
                    (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                      (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                        (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
                    (@Semiring.toModule.{0} (@NumberField.RingOfIntegers.{0} L inst)
                      (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                        (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                          (@NumberField.instCommRingRingOfIntegers.{0} L inst)))))))
              (@Ideal.pointwiseDistribMulAction.{0, 0}
                (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                  (@DivisionSemiring.toSemiring.{0} L
                    (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                  (@DivisionSemiring.toSemiring.{0} L
                    (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                  (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                  (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                (@NumberField.RingOfIntegers.{0} L inst)
                (@DivInvMonoid.toMonoid.{0}
                  (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                  (@Group.toDivInvMonoid.{0}
                    (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                      (@DivisionSemiring.toSemiring.{0} L
                        (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                      (@DivisionSemiring.toSemiring.{0} L
                        (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                      (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                      (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                    (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
                      (@DivisionSemiring.toSemiring.{0} L
                        (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                      (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))))
                (@CommSemiring.toSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                  (@CommRing.toCommSemiring.{0} (@NumberField.RingOfIntegers.{0} L inst)
                    (@NumberField.instCommRingRingOfIntegers.{0} L inst)))
                (@NumberField.RingOfIntegers.instMulSemiringAction.{0, 0} L inst
                  (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                  (@AlgEquiv.aut.{0, 0} Rat L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
                  (@AlgEquiv.applyMulSemiringAction.{0, 0} Rat L Rat.commSemiring
                    (@DivisionSemiring.toSemiring.{0} L
                      (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
                    (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)))))
            P)
          σ →
        @Eq.{1} L
          (@DFunLike.coe.{1, 1, 1}
            (@AlgEquiv.{0, 0, 0} Rat L L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            L (fun (x : L) ↦ L)
            (@AlgEquiv.instFunLike.{0, 0, 0} Rat L L Rat.commSemiring
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionSemiring.toSemiring.{0} L (@Semifield.toDivisionSemiring.{0} L (@Field.toSemifield.{0} L inst)))
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _)
              (@DivisionRing.toRatAlgebra.{0} L (@Field.toDivisionRing.{0} L inst) _))
            σ x)
          x := by
  intro L _ _ x c hx P hP _ σ hσ
  have hsq : (σ x) ^ 2 = x ^ 2 := by
    rw [← map_pow, hx, map_intCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
  · exact h
  exfalso
  have hx' : x ^ 2 = 8 * (c : L) + 1 := by rw [hx]; push_cast; ring
  have hint : IsIntegral ℤ ((1 + x) / 2) := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X - Polynomial.C (2 * c), ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C]
      simp only [eq_intCast, Int.cast_mul, Int.cast_ofNat]
      linear_combination hx' / 4
  let y : NumberField.RingOfIntegers L := ⟨(1 + x) / 2, hint⟩
  have hy : algebraMap (NumberField.RingOfIntegers L) L y = (1 + x) / 2 := rfl
  have h2 : (2 : NumberField.RingOfIntegers L) ∈ P := by
    have h0 := (Ideal.mem_of_liesOver P (Ideal.span {(2 : ℤ)}) (2 : ℤ)).mp
      (Ideal.subset_span rfl)
    simpa using h0
  have hprod : y * (y - 1) = 2 * (c : NumberField.RingOfIntegers L) := by
    apply NumberField.RingOfIntegers.ext
    change algebraMap (NumberField.RingOfIntegers L) L (y * (y - 1)) =
      algebraMap (NumberField.RingOfIntegers L) L (2 * (c : NumberField.RingOfIntegers L))
    rw [map_mul, map_sub, map_one, map_mul, map_ofNat, map_intCast, hy]
    linear_combination hx' / 4
  have hmem : y * (y - 1) ∈ P := by
    rw [hprod]
    exact P.mul_mem_right _ h2
  have hσP : Ideal.map (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (NumberField.RingOfIntegers L) σ) P
      = P := hσ
  have key : ∀ a ∈ P, σ • a ∈ P := fun a ha => by
    have h3 := Ideal.mem_map_of_mem
      (MulSemiringAction.toRingHom (L ≃ₐ[ℚ] L) (NumberField.RingOfIntegers L) σ) ha
    rw [hσP] at h3
    exact h3
  have hσy : σ • y = 1 - y := by
    apply NumberField.RingOfIntegers.ext
    change σ (algebraMap (NumberField.RingOfIntegers L) L y) =
      algebraMap (NumberField.RingOfIntegers L) L (1 - y)
    rw [map_sub, map_one, hy, map_div₀, map_add, map_one, h, map_ofNat]
    ring
  have h1 : (1 : NumberField.RingOfIntegers L) ∈ P := by
    rcases hP.mem_or_mem hmem with h' | h'
    · have h4 := key y h'
      rw [hσy] at h4
      have e : (1 : NumberField.RingOfIntegers L) = (1 - y) + y := by ring
      rw [e]
      exact P.add_mem h4 h'
    · have h4 := key _ h'
      rw [smul_sub, hσy, smul_one] at h4
      have e : (1 : NumberField.RingOfIntegers L) = -((1 - y - 1) + (y - 1)) := by ring
      rw [e]
      exact P.neg_mem (P.add_mem h4 h')
  exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
end Bl.general_b_fact_right_ter_form
