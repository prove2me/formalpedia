-- Prove2me | solution 1 for GaloisRepAdic.isUnramifiedAt_of_forall_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/3a364de8-8be2-5766-ad56-b078a8f26c1b

import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Filtration
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isUnramifiedAt_of_forall_quotient

open scoped TensorProduct
open IsLocalRing Module

namespace LCMazur

private theorem eq_zero_of_forall_toMatrix_eq_zero {R : Type} [CommRing R] {V : Type}
    [AddCommGroup V] [Module R V] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι R V)
    (T : Module.End R V) (h : ∀ i j, LinearMap.toMatrix b b T i j = 0) : T = 0 :=
  (LinearMap.toMatrix b b).map_eq_zero_iff.mp (Matrix.ext fun i j => by rw [h, Matrix.zero_apply])

private theorem baseChange_eq_zero_iff {R : Type} [CommRing R] {V : Type} [AddCommGroup V]
    [Module R V] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Basis ι R V) (B : Type) [CommRing B]
    [Algebra R B] (T : Module.End R V) :
    T.baseChange B = 0 ↔ ∀ i j, algebraMap R B (LinearMap.toMatrix b b T i j) = 0 := by
  rw [← (LinearMap.toMatrix (Algebra.TensorProduct.basis B b)
      (Algebra.TensorProduct.basis B b)).map_eq_zero_iff, LinearMap.toMatrix_baseChange,
    ← Matrix.ext_iff]
  simp only [Matrix.map_apply, Matrix.zero_apply]

private theorem eq_zero_of_forall_mem_maximalIdeal_pow_succ {A : Type} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {x : A}
    (hx : ∀ m : ℕ, x ∈ maximalIdeal A ^ (m + 1)) : x = 0 := by
  have hx' : x ∈ ⨅ m : ℕ, maximalIdeal A ^ m :=
    Ideal.mem_iInf.mpr fun m => (Ideal.pow_le_pow_right m.le_succ) (hx m)
  rwa [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal A).ne_top,
    Ideal.mem_bot] at hx'

private theorem eq_zero_of_forall_baseChange_quotient_eq_zero {A : Type} [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] {V : Type} [AddCommGroup V] [Module A V]
    [Module.Free A V] [Module.Finite A V] (T : Module.End A V)
    (hT : ∀ m : ℕ, letI := (Ideal.Quotient.mk (maximalIdeal A ^ (m + 1))).toAlgebra;
      T.baseChange (A ⧸ maximalIdeal A ^ (m + 1)) = 0) : T = 0 := by
  classical
  let b := Module.Free.chooseBasis A V
  refine eq_zero_of_forall_toMatrix_eq_zero b T fun i j =>
    eq_zero_of_forall_mem_maximalIdeal_pow_succ fun m => ?_
  letI := (Ideal.Quotient.mk (maximalIdeal A ^ (m + 1))).toAlgebra
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact (baseChange_eq_zero_iff b _ T).mp (hT m) i j

end LCMazur

theorem solution {A : Type} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (ρ : GaloisRepAdic A) {q : ℕ}
    (h : ∀ m : ℕ,
      haveI : Nontrivial (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
          (Ideal.IsMaximal.ne_top inferInstance) (Ideal.pow_le_self (Nat.succ_ne_zero m)))
      haveI : IsLocalRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
      (ρ.baseChangeAlong (Ideal.Quotient.mk (IsLocalRing.maximalIdeal A ^ (m + 1)))
          (IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective)).IsUnramifiedAt q) :
    ρ.IsUnramifiedAt q := by
  intro P hP σ hσ
  rw [← sub_eq_zero]
  refine LCMazur.eq_zero_of_forall_baseChange_quotient_eq_zero (ρ.ρ σ - 1) fun m => ?_
  letI := (Ideal.Quotient.mk (maximalIdeal A ^ (m + 1))).toAlgebra
  have h1 : (ρ.ρ σ).baseChange (A ⧸ maximalIdeal A ^ (m + 1)) = 1 := h m P hP σ hσ
  rw [LinearMap.baseChange_sub, LinearMap.baseChange_one]; exact sub_eq_zero.mpr h1

end S_GaloisRepAdic_isUnramifiedAt_of_forall_quotient
end P2MW
export P2MW.S_GaloisRepAdic_isUnramifiedAt_of_forall_quotient (solution)
