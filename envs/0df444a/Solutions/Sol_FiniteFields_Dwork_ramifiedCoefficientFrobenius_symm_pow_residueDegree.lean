-- Prove2me | solution 1 for FiniteFields.Dwork.ramifiedCoefficientFrobenius_symm_pow_residueDegree
-- status  : ACCEPTED   (prove)
-- author  : @Idealson
-- created : 2026-10-20T06:45:35.097979+00:00
-- url     : https://prove2.me/submissions/a9722a8a-b761-4814-999f-ac3c284dedab

import Mathlib
import Definitions.Def_FiniteFields_Dwork_NuclearOperator
section
noncomputable section
open Polynomial
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
@[simp]
theorem ramifiedCoefficientFrobenius_dworkPrimitiveRoot :
    ramifiedCoefficientFrobenius k p (dworkPrimitiveRoot k p) =
      dworkPrimitiveRoot k p := by
  exact ramifiedCoefficientFrobeniusHom_dworkPrimitiveRoot k p
end FiniteFields.Dwork
end
end
section
noncomputable section
open Filter Topology
namespace FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw5bResiduePrimeAlgebra
theorem frobeniusLift_pow_finrank (x : CoefficientRing k p) :
    (frobeniusLift k p)^[Module.finrank (ZMod p) k] x = x := by
  letI := Fintype.ofFinite k
  ext n
  rw [show (frobeniusLift k p)^[Module.finrank (ZMod p) k] x
      = (WittVector.frobenius (p := p) (R := k))^[Module.finrank (ZMod p) k] x from rfl,
    WittVector.iterate_frobenius_coeff, FiniteField.pow_finrank_eq_natCard,
    Nat.card_eq_fintype_card, FiniteField.pow_card]
private theorem fracFrob_algebraMap (z : CoefficientRing k p) :
    WittVector.FractionRing.frobenius p k
        (algebraMap (CoefficientRing k p) (FractionRing (CoefficientRing k p)) z)
      = algebraMap (CoefficientRing k p) (FractionRing (CoefficientRing k p))
          (frobeniusLift k p z) :=
  IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _
private theorem fracFrob_iterate_algebraMap (m : ℕ) (z : CoefficientRing k p) :
    (WittVector.FractionRing.frobenius p k)^[m]
        (algebraMap (CoefficientRing k p) (FractionRing (CoefficientRing k p)) z)
      = algebraMap (CoefficientRing k p) (FractionRing (CoefficientRing k p))
          ((frobeniusLift k p)^[m] z) := by
  induction m generalizing z with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, fracFrob_algebraMap, ih, Function.iterate_succ_apply]
private theorem fracFrob_iterate_div (m : ℕ) (x y : FractionRing (CoefficientRing k p)) :
    (WittVector.FractionRing.frobenius p k)^[m] (x / y)
      = (WittVector.FractionRing.frobenius p k)^[m] x
        / (WittVector.FractionRing.frobenius p k)^[m] y := by
  induction m generalizing x y with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, map_div₀, ih]
theorem fractionRingFrobenius_pow_finrank (x : FractionRing (CoefficientRing k p)) :
    (WittVector.FractionRing.frobenius p k)^[Module.finrank (ZMod p) k] x = x := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := CoefficientRing k p) x
  rw [fracFrob_iterate_div, fracFrob_iterate_algebraMap, fracFrob_iterate_algebraMap,
    frobeniusLift_pow_finrank, frobeniusLift_pow_finrank]
private theorem valuedFrobenius_iterate_ofVal (m : ℕ)
    (x : WithVal (coefficientValuation k p)) :
    WithVal.ofVal ((coefficientValuedFrobenius k p)^[m] x)
      = (WittVector.FractionRing.frobenius p k)^[m] (WithVal.ofVal x) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
      rfl
theorem coefficientValuedFrobenius_pow_finrank (x : WithVal (coefficientValuation k p)) :
    (coefficientValuedFrobenius k p)^[Module.finrank (ZMod p) k] x = x := by
  apply WithVal.ofVal_injective
  rw [valuedFrobenius_iterate_ofVal, fractionRingFrobenius_pow_finrank]
private theorem coefficientFieldFrobenius_iterate_continuous (m : ℕ) :
    Continuous ((coefficientFieldFrobenius k p)^[m] :
      CoefficientField k p → CoefficientField k p) := by
  induction m with
  | zero => simpa using continuous_id
  | succ m ih =>
      rw [Function.iterate_succ]
      exact ih.comp (coefficientFieldFrobenius_continuous k p)
private theorem coefficientFieldFrobenius_iterate_coe (m : ℕ)
    (y : WithVal (coefficientValuation k p)) :
    (coefficientFieldFrobenius k p)^[m] (y : CoefficientField k p)
      = ((((coefficientValuedFrobenius k p)^[m] y : WithVal (coefficientValuation k p))) :
          CoefficientField k p) := by
  induction m generalizing y with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply, coefficientFieldFrobenius_coe, ih,
        Function.iterate_succ_apply]
theorem coefficientFieldFrobenius_pow_finrank (x : CoefficientField k p) :
    (coefficientFieldFrobenius k p)^[Module.finrank (ZMod p) k] x = x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (coefficientFieldFrobenius_iterate_continuous k p _) continuous_id) ?_
  intro y
  rw [coefficientFieldFrobenius_iterate_coe, coefficientValuedFrobenius_pow_finrank]
private theorem ramifiedFrobPow_apply (m : ℕ) (x : DworkCyclotomicField k p) :
    ramifiedFrobPow k p m x = (ramifiedCoefficientFrobenius k p)^[m] x := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply]
      exact ih _
private theorem ramifiedFrobPow_algebraMap (m : ℕ) (a : CoefficientField k p) :
    ramifiedFrobPow k p m (algebraMap (CoefficientField k p) (DworkCyclotomicField k p) a)
      = algebraMap (CoefficientField k p) (DworkCyclotomicField k p)
          ((coefficientFieldFrobenius k p)^[m] a) := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
      show ramifiedFrobPow k p m
        (ramifiedCoefficientFrobenius k p
          (algebraMap (CoefficientField k p) (DworkCyclotomicField k p) a)) = _
      rw [ramifiedCoefficientFrobenius_algebraMap, ih, Function.iterate_succ_apply]
private theorem ramifiedFrobPow_root (m : ℕ) :
    ramifiedFrobPow k p m (dworkPrimitiveRoot k p) = dworkPrimitiveRoot k p := by
  induction m with
  | zero => rfl
  | succ m ih =>
      show ramifiedFrobPow k p m
        (ramifiedCoefficientFrobenius k p (dworkPrimitiveRoot k p)) = _
      rw [ramifiedCoefficientFrobenius_dworkPrimitiveRoot, ih]
private theorem cyclotomicPolynomial_eval₂ :
    (DworkCyclotomicPolynomial k p).eval₂
        (algebraMap (CoefficientField k p) (DworkCyclotomicField k p))
        (dworkPrimitiveRoot k p) = 0 := by
  rw [← Polynomial.aeval_def, ← dworkCyclotomicIsAdjoinRoot_root k p]
  exact (dworkCyclotomicIsAdjoinRoot k p).aeval_root_self
theorem ramifiedCoefficientFrobenius_pow_residueDegree (x : DworkCyclotomicField k p) :
    (ramifiedCoefficientFrobenius k p)^[Module.finrank (ZMod p) k] x = x := by
  have hz := cyclotomicPolynomial_eval₂ k p
  let h := dworkCyclotomicIsAdjoinRoot k p
  have hpow : ramifiedFrobPow k p (Module.finrank (ZMod p) k)
      = h.lift (algebraMap (CoefficientField k p) (DworkCyclotomicField k p))
          (dworkPrimitiveRoot k p) hz :=
    h.eq_lift hz _
      (fun a => by
        rw [ramifiedFrobPow_algebraMap, coefficientFieldFrobenius_pow_finrank])
      (by rw [dworkCyclotomicIsAdjoinRoot_root, ramifiedFrobPow_root])
  have hid : (RingHom.id (DworkCyclotomicField k p))
      = h.lift (algebraMap (CoefficientField k p) (DworkCyclotomicField k p))
          (dworkPrimitiveRoot k p) hz :=
    h.eq_lift hz _ (fun a => rfl) (by rw [dworkCyclotomicIsAdjoinRoot_root]; rfl)
  have := congrArg (fun g : DworkCyclotomicField k p →+* DworkCyclotomicField k p => g x)
    (hpow.trans hid.symm)
  simpa [ramifiedFrobPow_apply] using this
end FiniteFields.Dwork
end
end
open Filter Topology
open FiniteFields.Dwork
variable (k : Type*) (p : ℕ) [Fact p.Prime] [Field k] [CharP k p] [Finite k]
attribute [local instance] FiniteFields.Dwork.dw5bResiduePrimeAlgebra
theorem solution (x : DworkCyclotomicField k p) :
    (ramifiedCoefficientFrobenius k p).symm^[Module.finrank (ZMod p) k] x = x := by
  have hinv : ∀ y : DworkCyclotomicField k p,
      (ramifiedCoefficientFrobenius k p)^[Module.finrank (ZMod p) k]
        ((ramifiedCoefficientFrobenius k p).symm^[Module.finrank (ZMod p) k] y) = y :=
    Function.LeftInverse.iterate
      (ramifiedCoefficientFrobenius k p).apply_symm_apply (Module.finrank (ZMod p) k)
  calc (ramifiedCoefficientFrobenius k p).symm^[Module.finrank (ZMod p) k] x
      = (ramifiedCoefficientFrobenius k p)^[Module.finrank (ZMod p) k]
          ((ramifiedCoefficientFrobenius k p).symm^[Module.finrank (ZMod p) k] x) :=
        (ramifiedCoefficientFrobenius_pow_residueDegree k p _).symm
    _ = x := hinv x
