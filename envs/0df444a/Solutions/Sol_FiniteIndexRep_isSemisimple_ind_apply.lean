-- Prove2me | solution 1 for FiniteIndexRep.isSemisimple_ind_apply
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T20:01:18.785164+00:00
-- url     : https://prove2.me/submissions/f3484840-c07b-4056-af6b-77d945950e19

import Mathlib
import Theorems.Thm_FiniteIndexRep_forall_isSemisimple_iff_forall_mem_subgroup

set_option autoImplicit false

namespace Sol_FiniteIndexRep_isSemisimple_ind_apply

open Polynomial

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (H : Subgroup G) (σ : Representation k H V)

/-- `⟦s g ⊗ σ(s) a⟧ = ⟦g ⊗ a⟧` for `s ∈ H`. -/
lemma mk_mul (s : H) (g : G) (a : V) :
    Representation.IndV.mk H.subtype σ ((s : G) * g) (σ s a) =
      Representation.IndV.mk H.subtype σ g a := by
  have := Representation.Coinvariants.mk_self_apply
    (Representation.tprod ((Representation.leftRegular k G).comp H.subtype) σ) s
    (MonoidAlgebra.single g (1 : k) ⊗ₜ[k] a)
  simpa using this

/-- `⟦s g ⊗ a⟧ = ⟦g ⊗ σ(s)⁻¹ a⟧`. -/
lemma mk_mul' (s : H) (g : G) (a : V) :
    Representation.IndV.mk H.subtype σ ((s : G) * g) a =
      Representation.IndV.mk H.subtype σ g (σ s⁻¹ a) := by
  rw [← mk_mul H σ s g (σ s⁻¹ a), ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
    Module.End.one_apply]

lemma conj_mem {n : G} (hn : n ∈ H.normalCore) (g : G) : g * n * g⁻¹ ∈ H :=
  Subgroup.normalCore_le H ((Subgroup.normalCore_normal H).conj_mem n hn g)

/-- An element of the normal core acts on `⟦g ⊗ a⟧` through `σ(g n g⁻¹)`. -/
lemma ind_comp_mk {n : G} (hn : n ∈ H.normalCore) (g : G) :
    Representation.ind H.subtype σ n ∘ₗ Representation.IndV.mk H.subtype σ g =
      Representation.IndV.mk H.subtype σ g ∘ₗ σ ⟨g * n * g⁻¹, conj_mem H hn g⟩ := by
  refine LinearMap.ext fun a => ?_
  show Representation.ind H.subtype σ n (Representation.IndV.mk H.subtype σ g a) =
    Representation.IndV.mk H.subtype σ g (σ ⟨g * n * g⁻¹, conj_mem H hn g⟩ a)
  rw [Representation.ind_mk]
  have h := mk_mul' H σ ⟨g * n⁻¹ * g⁻¹, by
    simpa using conj_mem H (H.normalCore.inv_mem hn) g⟩ g a
  have e1 : ((⟨g * n⁻¹ * g⁻¹, by simpa using conj_mem H (H.normalCore.inv_mem hn) g⟩ : H) : G) * g
      = g * n⁻¹ := by simp [mul_assoc]
  rw [e1] at h
  rw [h]
  congr 3
  ext
  simp [mul_assoc]

lemma aeval_comp {M W : Type*} [AddCommGroup M] [Module k M] [AddCommGroup W] [Module k W]
    (f : M →ₗ[k] W) (A : Module.End k M) (B : Module.End k W) (h : B ∘ₗ f = f ∘ₗ A)
    (p : k[X]) : aeval B p ∘ₗ f = f ∘ₗ aeval A p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [LinearMap.add_comp, LinearMap.comp_add, hp, hq]
  | monomial n a =>
    simp only [aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      LinearMap.smul_comp, LinearMap.comp_smul]
    rw [Module.End.commute_pow_left_of_commute h n]

lemma out_mem (g : G) :
    g * (Quotient.out (⟦g⟧ : Quotient (QuotientGroup.rightRel H)))⁻¹ ∈ H :=
  QuotientGroup.rightRel_apply.1 (Quotient.mk_out (s := QuotientGroup.rightRel H) g)

/-- `⟦g ⊗ a⟧ = ⟦c ⊗ σ(g c⁻¹)⁻¹ a⟧` for the chosen representative `c` of the coset `H g`. -/
lemma mk_eq_mk_out (g : G) :
    Representation.IndV.mk H.subtype σ g =
      Representation.IndV.mk H.subtype σ (Quotient.out (⟦g⟧ : Quotient (QuotientGroup.rightRel H)))
        ∘ₗ σ (⟨_, out_mem H g⟩ : H)⁻¹ := by
  refine LinearMap.ext fun a => ?_
  have h := mk_mul' H σ ⟨_, out_mem H g⟩
    (Quotient.out (⟦g⟧ : Quotient (QuotientGroup.rightRel H))) a
  have e : ((⟨_, out_mem H g⟩ : H) : G) *
      (Quotient.out (⟦g⟧ : Quotient (QuotientGroup.rightRel H))) = g := by simp
  rw [e] at h
  exact h

lemma finiteDimensional_indV [FiniteDimensional k V] [H.FiniteIndex] :
    FiniteDimensional k (Representation.IndV H.subtype σ) := by
  classical
  have : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  have : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  haveI : Fintype (Quotient (QuotientGroup.rightRel H)) := Fintype.ofFinite _
  let L : (Quotient (QuotientGroup.rightRel H) → V) →ₗ[k] Representation.IndV H.subtype σ :=
    ∑ q, Representation.IndV.mk H.subtype σ q.out ∘ₗ LinearMap.proj q
  have hL : ∀ (q : Quotient (QuotientGroup.rightRel H)) (b : V),
      L (Pi.single q b) = Representation.IndV.mk H.subtype σ q.out b := by
    intro q b
    simp only [L, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single q]
    · simp
    · intro q' _ hq'
      simp [hq']
    · simp
  have hmem : ∀ (g : G) (a : V), Representation.IndV.mk H.subtype σ g a ∈ LinearMap.range L := by
    intro g a
    rw [mk_eq_mk_out H σ g, LinearMap.comp_apply, ← hL]
    exact LinearMap.mem_range_self _ _
  have h0 : (LinearMap.range L).mkQ = 0 :=
    Representation.IndV.hom_ext H.subtype σ fun g => LinearMap.ext fun a => by
      simp only [LinearMap.comp_apply, LinearMap.zero_comp, LinearMap.zero_apply,
        Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).2 (hmem g a)
  have htop : LinearMap.range L = ⊤ := by
    simpa using congrArg LinearMap.ker h0
  exact Module.Finite.of_surjective L (LinearMap.range_eq_top.1 htop)

end Sol_FiniteIndexRep_isSemisimple_ind_apply

open Sol_FiniteIndexRep_isSemisimple_ind_apply in
open Polynomial UniqueFactorizationMonoid in
theorem solution {k G V : Type*} [Field k] [CharZero k] [Group G] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (H : Subgroup G) [H.FiniteIndex] (σ : Representation k H V)
    (hσ : ∀ h : H, Module.End.IsSemisimple (σ h)) (g : G) :
    Module.End.IsSemisimple (Representation.ind H.subtype σ g) := by
  classical
  haveI := finiteDimensional_indV H σ
  refine (FiniteIndexRep.forall_isSemisimple_iff_forall_mem_subgroup
    (Representation.ind H.subtype σ) H.normalCore).2 ?_ g
  intro n hn
  have : Finite (G ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
  have : Finite (Quotient (QuotientGroup.rightRel H)) :=
    Finite.of_equiv _ (QuotientGroup.quotientRightRelEquivQuotientLeftRel H).symm
  haveI : Fintype (Quotient (QuotientGroup.rightRel H)) := Fintype.ofFinite _
  let T : Quotient (QuotientGroup.rightRel H) → Module.End k V := fun q =>
    σ ⟨q.out * n * q.out⁻¹, conj_mem H hn q.out⟩
  let P : k[X] := ∏ q, minpoly k (T q)
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun q _ =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral (T q))
  have hT : ∀ q, aeval (T q) (radical P) = 0 := fun q => by
    rw [← minpoly.dvd_iff, dvd_radical_iff (hσ _).minpoly_squarefree.isRadical hP]
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ q)
  refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := radical P) squarefree_radical ?_
  refine Representation.IndV.hom_ext H.subtype σ fun g' => ?_
  rw [mk_eq_mk_out H σ g', LinearMap.zero_comp, ← LinearMap.comp_assoc,
    aeval_comp _ _ _ (ind_comp_mk H σ hn _), hT]
  simp
