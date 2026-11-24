-- Prove2me | solution 1 for Formalism.WachCohomologyFacts.PLenBound.length_quot_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:41:01.483752+00:00
-- url     : https://prove2.me/submissions/48a4079e-0bda-4e66-af28-f880fe14bf1e

import Definitions.Def_Formalism_FrobeniusContraction_Statement
import Definitions.Def_Formalism_FrobeniusContraction_FrobeniusContractionProofs_LenBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WachCohomologyFacts Formalism.WachCohomologyFacts.PLenBound
variable {O : Type} [CommRing O]
namespace Formalism.WachCohomologyFacts.PLenBound
theorem _root_.solution (a : O) (e : ℕ) :
    Module.length O (O ⧸ Ideal.span {a ^ e}) ≤ (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  induction e with
  | zero =>
    rw [pow_zero, Ideal.span_singleton_one, Nat.cast_zero, zero_mul]
    haveI : Subsingleton (O ⧸ (⊤ : Ideal O)) := ⟨fun x y => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact (Submodule.Quotient.eq _).2 Submodule.mem_top⟩
    exact le_of_eq (Module.length_eq_zero)
  | succ e ih =>
    have hle : Ideal.span {a ^ (e + 1)} ≤ Ideal.span {a ^ e} :=
      Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow a (Nat.le_succ e))
    have hex := Module.length_eq_add_of_exact (LinearMap.ker (Submodule.factor hle)).subtype
      (Submodule.factor hle) (Submodule.injective_subtype _) (Submodule.factor_surjective hle)
      (LinearMap.exact_subtype_ker_map _)
    let f0 : O →ₗ[O] O ⧸ Ideal.span {a ^ (e + 1)} :=
      (Ideal.span {a ^ (e + 1)}).mkQ ∘ₗ LinearMap.mulLeft O (a ^ e)
    have hf0 : Ideal.span {a} ≤ LinearMap.ker f0 := by
      refine Ideal.span_le.2 (Set.singleton_subset_iff.2 ?_)
      show (Ideal.span {a ^ (e + 1)}).mkQ (a ^ e * a) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, ← pow_succ]
      exact Ideal.subset_span rfl
    let f := (Ideal.span {a}).liftQ f0 hf0
    have hfk : ∀ x, f x ∈ LinearMap.ker (Submodule.factor hle) := by
      intro x
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [LinearMap.mem_ker]
      show (Submodule.Quotient.mk (a ^ e * y) : O ⧸ Ideal.span {a ^ e}) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Ideal.mem_span_singleton'.2 ⟨y, mul_comm _ _⟩
    let f' : O ⧸ Ideal.span {a} →ₗ[O] LinearMap.ker (Submodule.factor hle) := LinearMap.codRestrict _ f hfk
    have hf'surj : Function.Surjective f' := by
      rintro ⟨z, hz⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      have hy : y ∈ Ideal.span {a ^ e} := by
        rw [LinearMap.mem_ker] at hz
        exact (Submodule.Quotient.mk_eq_zero _).1 hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      refine ⟨Submodule.Quotient.mk c, Subtype.ext ?_⟩
      show (Submodule.Quotient.mk (a ^ e * c) : O ⧸ Ideal.span {a ^ (e + 1)}) = Submodule.Quotient.mk (c * a ^ e)
      rw [mul_comm]
    have hk := Module.length_le_of_surjective f' hf'surj
    rw [hex, Nat.cast_succ, add_mul, one_mul]
    exact (add_le_add hk ih).trans (le_of_eq (add_comm _ _))
end Formalism.WachCohomologyFacts.PLenBound
