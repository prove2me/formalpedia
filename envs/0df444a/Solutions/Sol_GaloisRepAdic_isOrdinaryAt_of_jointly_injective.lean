-- Prove2me | solution 1 for GaloisRepAdic.isOrdinaryAt_of_jointly_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/bf4935af-fc96-5cd3-b905-bb962848308c

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isOrdinaryAt_of_jointly_injective

open scoped TensorProduct
open IsLocalRing Module Polynomial

namespace LCMazur
namespace OrdJ

section Charpoly

variable {A : Type} [CommRing A]

theorem X_sq_sub_X_add_eq_mul (α β : A) :
    (X ^ 2 - C (α + β) * X + C (α * β) : A[X]) = (X - C α) * (X - C β) := by
  simp only [map_add, map_mul]
  ring

theorem eq_of_quadratic_eq {t d t' d' : A}
    (h : (X ^ 2 - C t * X + C d : A[X]) = X ^ 2 - C t' * X + C d') : t = t' ∧ d = d' := by
  have h1 := congrArg (fun p : A[X] => p.coeff 1) h
  have h0 := congrArg (fun p : A[X] => p.coeff 0) h
  simp at h1 h0
  exact ⟨h1, h0⟩

variable {V : Type} [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]

theorem charpoly_eq_of_finrank_eq_two [Nontrivial A] (h2 : finrank A V = 2) (φ : End A V) :
    φ.charpoly = X ^ 2 - C (LinearMap.trace A V φ) * X + C (LinearMap.det φ) := by
  let b := finBasisOfFinrankEq A V h2
  rw [← φ.charpoly_toMatrix b, Matrix.charpoly_fin_two, LinearMap.trace_eq_matrix_trace A b,
    LinearMap.det_toMatrix]

theorem charpoly_eq_of_trace_eq_det_add_one [Nontrivial A] (h2 : finrank A V = 2) (φ : End A V)
    (htr : LinearMap.trace A V φ = LinearMap.det φ + 1) :
    φ.charpoly = (X - C (LinearMap.det φ)) * (X - C 1) := by
  rw [charpoly_eq_of_finrank_eq_two h2, htr, ← X_sq_sub_X_add_eq_mul, mul_one]

theorem charpoly_eq_of_sub_smul_mem_span [Nontrivial A] (c : Basis (Fin 2) A V) {φ : End A V}
    {μ : A} (h : ∀ v, φ v - μ • v ∈ A ∙ c 0) :
    φ.charpoly = (X - C (c.repr (φ (c 0)) 0)) * (X - C μ) := by
  classical
  have h10 : c.repr (φ (c 0)) 1 = 0 := by
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (h (c 0))
    have := congrArg (fun v => c.repr v 1) hr
    simp only [map_smul, map_sub, Finsupp.smul_apply, Basis.repr_self, smul_eq_mul,
      Finsupp.sub_apply] at this
    simpa [Finsupp.single_apply] using this.symm
  have h11 : c.repr (φ (c 1)) 1 = μ := by
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp (h (c 1))
    have := congrArg (fun v => c.repr v 1) hr
    simp only [map_smul, map_sub, Finsupp.smul_apply, Basis.repr_self, smul_eq_mul,
      Finsupp.sub_apply] at this
    simpa [Finsupp.single_apply, sub_eq_zero] using this.symm
  rw [← φ.charpoly_toMatrix c, Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, h10, h11, mul_zero, sub_zero]
  exact X_sq_sub_X_add_eq_mul _ _

theorem trace_eq_det_add_one [Nontrivial A] (h2 : finrank A V = 2) (c : Basis (Fin 2) A V)
    {φ : End A V} (h : ∀ v, φ v - v ∈ A ∙ c 0) :
    LinearMap.trace A V φ = LinearMap.det φ + 1 := by
  have hchar := charpoly_eq_of_sub_smul_mem_span c (μ := 1) (fun v => by rw [one_smul]; exact h v)
  rw [charpoly_eq_of_finrank_eq_two h2, ← X_sq_sub_X_add_eq_mul] at hchar
  obtain ⟨htr, hdet⟩ := eq_of_quadratic_eq hchar
  rw [htr, hdet, mul_one]

end Charpoly

section Proj

variable {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]

noncomputable def ordProj (φ : End A V) (α β : A) : End A V :=
  Ring.inverse (α - β) • (φ - algebraMap A (End A V) β)

theorem ordProj_apply (φ : End A V) (α β : A) (v : V) :
    ordProj φ α β v = Ring.inverse (α - β) • (φ v - β • v) := by
  simp [ordProj]

theorem one_sub_ordProj (φ : End A V) {α β : A} (hu : IsUnit (α - β)) :
    1 - ordProj φ α β = ordProj φ β α := by
  have hinv : Ring.inverse (β - α) = -Ring.inverse (α - β) := by
    obtain ⟨u, hu'⟩ := hu
    rw [← neg_sub, ← hu', ← Units.val_neg, Ring.inverse_unit, Ring.inverse_unit, inv_neg,
      Units.val_neg]
  rw [ordProj, ordProj, hinv, neg_smul, sub_eq_iff_eq_add, neg_add_eq_sub, ← smul_sub,
    sub_sub_sub_cancel_left, ← map_sub, Algebra.smul_def, ← map_mul,
    Ring.inverse_mul_cancel _ hu, map_one]

theorem range_smul_of_isUnit {r : A} (hr : IsUnit r) (ψ : End A V) :
    LinearMap.range (r • ψ) = LinearMap.range ψ := by
  refine le_antisymm (LinearMap.range_smul_le_range ψ r) ?_
  obtain ⟨s, hs⟩ := hr.exists_left_inv
  calc LinearMap.range ψ = LinearMap.range ((s * r) • ψ) := by rw [hs, one_smul]
    _ = LinearMap.range (s • r • ψ) := by rw [mul_smul]
    _ ≤ LinearMap.range (r • ψ) := LinearMap.range_smul_le_range _ s

theorem range_ordProj_eq (φ : End A V) {α β : A} (hu : IsUnit (α - β)) :
    LinearMap.range (ordProj φ α β) = LinearMap.range (φ - algebraMap A (End A V) β) :=
  range_smul_of_isUnit hu.ringInverse _

variable [Module.Free A V] [Module.Finite A V] {φ : End A V} {α β : A}

theorem sub_mul_sub_eq_zero (hφ : φ.charpoly = (X - C α) * (X - C β)) :
    (φ - algebraMap A (End A V) β) * (φ - algebraMap A (End A V) α) = 0 := by
  have h := LinearMap.aeval_self_charpoly φ
  rwa [hφ, mul_comm, map_mul, map_sub, map_sub, aeval_X, aeval_C, aeval_C] at h

theorem isIdempotentElem_ordProj (hφ : φ.charpoly = (X - C α) * (X - C β))
    (hu : IsUnit (α - β)) : IsIdempotentElem (ordProj φ α β) := by
  set ψ := φ - algebraMap A (End A V) β with hψ
  have h2 : ψ * ψ = (α - β) • ψ := by
    rw [← sub_eq_zero, Algebra.smul_def, Algebra.commutes (α - β) ψ, ← mul_sub, map_sub,
      hψ, sub_sub_sub_cancel_right]
    exact sub_mul_sub_eq_zero hφ
  change ordProj φ α β * ordProj φ α β = ordProj φ α β
  rw [ordProj, ← hψ, smul_mul_assoc, mul_smul_comm, h2, smul_smul, smul_smul, mul_assoc,
    Ring.inverse_mul_cancel _ hu, mul_one]

theorem range_ordProj_eq_ker (hφ : φ.charpoly = (X - C α) * (X - C β)) (hu : IsUnit (α - β)) :
    LinearMap.range (ordProj φ α β) = LinearMap.ker (ordProj φ β α) := by
  rw [LinearMap.IsIdempotentElem.range_eq_ker_one_sub (isIdempotentElem_ordProj hφ hu),
    one_sub_ordProj φ hu]

theorem range_ordProj_invariant_iff (hφ : φ.charpoly = (X - C α) * (X - C β))
    (hu : IsUnit (α - β)) (g : End A V) :
    (∀ v ∈ LinearMap.range (ordProj φ α β), g v ∈ LinearMap.range (ordProj φ α β)) ↔
      ordProj φ β α * g * ordProj φ α β = 0 := by
  have hidem := isIdempotentElem_ordProj hφ hu
  rw [range_ordProj_eq_ker hφ hu]
  constructor
  · intro h
    ext v
    exact h _ (by rw [← range_ordProj_eq_ker hφ hu]; exact LinearMap.mem_range_self _ v)
  · intro h v hv
    rw [← range_ordProj_eq_ker hφ hu, LinearMap.IsIdempotentElem.mem_range_iff hidem] at hv
    rw [LinearMap.mem_ker, ← hv]
    exact congrArg (fun f : End A V => f v) h

theorem sub_mem_range_ordProj_iff (hφ : φ.charpoly = (X - C α) * (X - C β))
    (hu : IsUnit (α - β)) (g : End A V) :
    (∀ v, g v - v ∈ LinearMap.range (ordProj φ α β)) ↔ ordProj φ β α * (g - 1) = 0 := by
  rw [range_ordProj_eq_ker hφ hu]
  constructor
  · intro h
    ext v
    exact h v
  · intro h v
    exact congrArg (fun f : End A V => f v) h

end Proj

section Basis

variable {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]

theorem exists_basis_of_corner_isUnit (b₀ : Basis (Fin 2) A V) (ψ : End A V)
    (h00 : IsUnit (b₀.repr (ψ (b₀ 0)) 0))
    (hdet : b₀.repr (ψ (b₀ 0)) 0 * b₀.repr (ψ (b₀ 1)) 1 =
      b₀.repr (ψ (b₀ 1)) 0 * b₀.repr (ψ (b₀ 0)) 1) :
    ∃ b : Basis (Fin 2) A V, b 0 = ψ (b₀ 0) ∧ b 1 = b₀ 1 ∧
      LinearMap.range ψ = A ∙ b 0 := by
  classical
  let v : Fin 2 → V := ![ψ (b₀ 0), b₀ 1]
  have hdetv : b₀.det v = b₀.repr (ψ (b₀ 0)) 0 := by
    rw [Basis.det_apply, Matrix.det_fin_two]
    simp [v, Basis.toMatrix_apply]
  obtain ⟨hli, hsp⟩ := b₀.is_basis_iff_det.mpr (hdetv ▸ h00)
  refine ⟨Basis.mk hli hsp.ge, by simp [v], by simp [v], ?_⟩
  rw [Basis.coe_mk]
  change LinearMap.range ψ = A ∙ ψ (b₀ 0)
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr
    (LinearMap.mem_range_self ψ _))

  obtain ⟨u, hu⟩ := h00
  have hmul : ψ (b₀ 1) = (b₀.repr (ψ (b₀ 1)) 0 * ↑u⁻¹) • ψ (b₀ 0) := by
    rw [b₀.ext_elem_iff]
    have hinv : (↑u⁻¹ : A) * b₀.repr (ψ (b₀ 0)) 0 = 1 := by rw [← hu, Units.inv_mul]
    intro i
    fin_cases i
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Fin.zero_eta]
      linear_combination -(b₀.repr (ψ (b₀ 1)) 0) * hinv
    · simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, Fin.mk_one]
      linear_combination (↑u⁻¹ : A) * hdet - (b₀.repr (ψ (b₀ 1)) 1) * hinv
  rw [LinearMap.range_eq_map, ← b₀.span_eq, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  fin_cases i
  · exact Submodule.mem_span_singleton_self _
  · simp only [Fin.mk_one, SetLike.mem_coe]
    rw [hmul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

variable [IsLocalRing A] [Module.Free A V] [Module.Finite A V]

theorem exists_basis_range_eq_of_charpoly (h2 : finrank A V = 2) {ψ : End A V} {u : A}
    (hψ : ψ.charpoly = (X - C u) * X) (hu : IsUnit u) :
    ∃ b : Basis (Fin 2) A V, LinearMap.range ψ = A ∙ b 0 := by
  classical

  have key : ∀ b₀ : Basis (Fin 2) A V,
      b₀.repr (ψ (b₀ 0)) 0 + b₀.repr (ψ (b₀ 1)) 1 = u ∧
      b₀.repr (ψ (b₀ 0)) 0 * b₀.repr (ψ (b₀ 1)) 1 =
        b₀.repr (ψ (b₀ 1)) 0 * b₀.repr (ψ (b₀ 0)) 1 := by
    intro b₀
    have hM := ψ.charpoly_toMatrix b₀
    rw [hψ, Matrix.charpoly_fin_two, show ((X - C u) * X : A[X]) = X ^ 2 - C u * X + C 0 by
      simp only [map_zero, add_zero]; ring] at hM
    obtain ⟨htr, hdet⟩ := eq_of_quadratic_eq hM
    rw [Matrix.trace_fin_two] at htr
    rw [Matrix.det_fin_two, sub_eq_zero] at hdet
    simp only [LinearMap.toMatrix_apply] at htr hdet
    exact ⟨htr, hdet⟩
  let b₀ := finBasisOfFinrankEq A V h2
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add ((key b₀).1.symm ▸ hu) with h00 | h11
  · obtain ⟨b, -, -, hb⟩ := exists_basis_of_corner_isUnit b₀ ψ h00 (key b₀).2
    exact ⟨b, hb⟩
  ·
    let b₁ := b₀.reindex (Equiv.swap 0 1)
    have h0 : b₁ 0 = b₀ 1 := by simp [b₁]
    have hr : ∀ x, b₁.repr x 0 = b₀.repr x 1 := fun x => by simp [b₁]
    obtain ⟨b, -, -, hb⟩ := exists_basis_of_corner_isUnit b₁ ψ (by rwa [h0, hr]) (key b₁).2
    exact ⟨b, hb⟩

theorem exists_basis_range_ordProj (h2 : finrank A V = 2) {φ : End A V} {α β : A}
    (hφ : φ.charpoly = (X - C α) * (X - C β)) (hu : IsUnit (α - β)) :
    ∃ b : Basis (Fin 2) A V, LinearMap.range (ordProj φ α β) = A ∙ b 0 := by
  have hψ : (φ - algebraMap A (End A V) β).charpoly = (X - C (α - β)) * X := by
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.charpoly_sub_smul, hφ]
    simp only [mul_comp, sub_comp, X_comp, C_comp, map_sub]
    ring
  rw [range_ordProj_eq φ hu]
  exact exists_basis_range_eq_of_charpoly h2 hψ hu

end Basis

section Unique

variable {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]

theorem span_basis_eq_of_le {ι : Type} (b : Basis ι A V) (i : ι) {w : V}
    (h : (A ∙ b i) ≤ A ∙ w) : (A ∙ b i) = A ∙ w := by
  refine le_antisymm h ((Submodule.span_singleton_le_iff_mem _ _).mpr ?_)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    ((Submodule.span_singleton_le_iff_mem _ _).mp h)
  have hcu : IsUnit c := by
    refine IsUnit.of_mul_eq_one (b.coord i w) ?_
    have := congrArg (b.coord i) hc
    simpa [Basis.coord_apply] using this
  obtain ⟨u, rfl⟩ := hcu
  refine Submodule.mem_span_singleton.mpr ⟨↑u⁻¹, ?_⟩
  rw [← hc, smul_smul, Units.inv_mul, one_smul]

variable [IsLocalRing A] [Module.Free A V] [Module.Finite A V] {φ : End A V} {α β : A}

theorem span_singleton_eq_range_ordProj (h2 : finrank A V = 2)
    (hφ : φ.charpoly = (X - C α) * (X - C β)) (hu : IsUnit (α - β)) {w : V}
    (hw : ∀ v, φ v - β • v ∈ A ∙ w) : (A ∙ w) = LinearMap.range (ordProj φ α β) := by
  obtain ⟨b, hb⟩ := exists_basis_range_ordProj h2 hφ hu
  have hle : LinearMap.range (ordProj φ α β) ≤ A ∙ w := by
    rintro _ ⟨v, rfl⟩
    rw [ordProj_apply]
    exact Submodule.smul_mem _ _ (hw v)
  rw [hb] at hle ⊢
  exact (span_basis_eq_of_le b 0 hle).symm

end Unique

section BaseChange

variable {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]
  (B : Type) [CommRing B] [Algebra A B]

theorem algebraMap_ringInverse {x : A} (hx : IsUnit x) :
    algebraMap A B (Ring.inverse x) = Ring.inverse (algebraMap A B x) := by
  rw [← one_mul (Ring.inverse (algebraMap A B x)),
    Ring.eq_mul_inverse_iff_mul_eq _ _ _ (hx.map _), ← map_mul, Ring.inverse_mul_cancel _ hx,
    map_one]

theorem ordProj_baseChange (φ : End A V) {α β : A} (hu : IsUnit (α - β)) :
    (ordProj φ α β).baseChange B =
      ordProj (φ.baseChange B) (algebraMap A B α) (algebraMap A B β) := by
  rw [ordProj, ordProj, LinearMap.baseChange_smul, LinearMap.baseChange_sub, ← map_sub,
    ← algebraMap_ringInverse B hu, algebraMap_smul, Algebra.algebraMap_eq_smul_one,
    LinearMap.baseChange_smul, LinearMap.baseChange_one, Algebra.algebraMap_eq_smul_one,
    algebraMap_smul]

variable [Module.Free A V] [Module.Finite A V] {φ : End A V} {α β : A}

theorem charpoly_baseChange_eq (hφ : φ.charpoly = (X - C α) * (X - C β)) :
    (φ.baseChange B).charpoly = (X - C (algebraMap A B α)) * (X - C (algebraMap A B β)) := by
  rw [LinearMap.charpoly_baseChange, hφ]
  simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C]

end BaseChange

section Descent

variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem eq_zero_of_forall_toMatrix_eq_zero (b : Basis ι R V) (T : Module.End R V)
    (h : ∀ i j, LinearMap.toMatrix b b T i j = 0) : T = 0 :=
  (LinearMap.toMatrix b b).map_eq_zero_iff.mp (Matrix.ext fun i j => by rw [h, Matrix.zero_apply])

theorem baseChange_eq_zero_iff (b : Basis ι R V) (B : Type) [CommRing B] [Algebra R B]
    (T : Module.End R V) :
    T.baseChange B = 0 ↔ ∀ i j, algebraMap R B (LinearMap.toMatrix b b T i j) = 0 := by
  rw [← (LinearMap.toMatrix (Algebra.TensorProduct.basis B b)
      (Algebra.TensorProduct.basis B b)).map_eq_zero_iff, LinearMap.toMatrix_baseChange,
    ← Matrix.ext_iff]
  simp only [Matrix.map_apply, Matrix.zero_apply]

variable [Module.Free R V] [Module.Finite R V]

theorem eq_zero_of_baseChange_eq_zero_of_jointly_injective (A B : Type) [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B]
    (hinj : ∀ x : R, algebraMap R A x = 0 → algebraMap R B x = 0 → x = 0)
    (T : Module.End R V) (hA : T.baseChange A = 0) (hB : T.baseChange B = 0) : T = 0 := by
  classical
  let b := Module.Free.chooseBasis R V
  exact eq_zero_of_forall_toMatrix_eq_zero b T fun i j =>
    hinj _ ((baseChange_eq_zero_iff b A T).mp hA i j) ((baseChange_eq_zero_iff b B T).mp hB i j)

end Descent

section Galois

theorem exists_mem_inertiaSubgroupIn_apply_eq_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    ∃ σ ∈ P.inertiaSubgroupIn ℚ, ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ 2 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
  have h2 : ((ZMod.unitOfCoprime 2 hcop : (ZMod p)ˣ) : ZMod p).val = 2 := by
    rw [ZMod.coe_unitOfCoprime, Nat.cast_ofNat]
    haveI : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm hp2)⟩
    exact ZMod.val_ofNat_of_lt (Fact.out)
  obtain ⟨σ, hσ, h⟩ := P.exists_mem_inertiaSubgroupIn_apply_eq_pow hp hP
    (ZMod.unitOfCoprime 2 hcop)
  refine ⟨σ, hσ, fun μ hμ => ?_⟩
  have h' := h μ hμ
  rw [h2] at h'
  exact h'

theorem isUnit_sub_one_of_sub_two_mem {B : Type} [CommRing B] [IsLocalRing B] {p : ℕ}
    (hp : (p : B) ∈ maximalIdeal B) {d : B} (hd : d - 2 ∈ Ideal.span {(p : B)}) :
    IsUnit (d - 1) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hd
  have hm : d - 2 ∈ maximalIdeal B := hc ▸ Ideal.mul_mem_left _ c hp
  by_contra hnu
  have h1 : d - 1 ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).mpr hnu
  have h : (1 : B) ∈ maximalIdeal B := by
    have e : (1 : B) = (d - 1) - (d - 2) := by ring
    rw [e]
    exact (maximalIdeal B).sub_mem h1 hm
  exact (maximalIdeal B).ne_top_iff_one.mp (Ideal.IsMaximal.ne_top inferInstance) h

variable {A : Type} [CommRing A] [IsLocalRing A] {B : Type} [CommRing B] [IsLocalRing B]

theorem det_baseChangeAlong_apply (f : A →+* B) (hf : IsLocalHom f) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((ρ.baseChangeAlong f hf).ρ σ) = f (LinearMap.det (ρ.ρ σ)) := by
  letI := f.toAlgebra
  exact LinearMap.det_baseChange (ρ.ρ σ)

theorem trace_baseChangeAlong_apply (f : A →+* B) (hf : IsLocalHom f) (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.trace B _ ((ρ.baseChangeAlong f hf).ρ σ) = f (LinearMap.trace A _ (ρ.ρ σ)) := by
  letI := f.toAlgebra
  exact LinearMap.trace_baseChange (ρ.ρ σ) B

theorem isUnit_det_sub_one (f : A →+* B) (hf : IsLocalHom f) (ρ : GaloisRepAdic A) {p : ℕ}
    (hdet : (ρ.baseChangeAlong f hf).DetIsCyclotomic p)
    {σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ₀ : ∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ₀ μ = μ ^ 2) :
    IsUnit (LinearMap.det (ρ.ρ σ₀) - 1) := by
  have h2 := hdet.2 1 σ₀ 2 (fun μ hμ => hσ₀ μ (by rwa [pow_one] at hμ))
  rw [det_baseChangeAlong_apply, pow_one, Nat.cast_ofNat] at h2
  have hu : IsUnit (f (LinearMap.det (ρ.ρ σ₀) - 1)) := by
    rw [map_sub, map_one]
    exact isUnit_sub_one_of_sub_two_mem hdet.1 h2
  haveI := hf
  exact IsUnit.of_map f _ hu

theorem map_trace_eq_map_det_add_one (f : A →+* B) (hf : IsLocalHom f) (ρ : GaloisRepAdic A)
    {p : ℕ} (hord : (ρ.baseChangeAlong f hf).IsOrdinaryAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ₀ : σ₀ ∈ P.inertiaSubgroupIn ℚ) :
    f (LinearMap.trace A _ (ρ.ρ σ₀)) = f (LinearMap.det (ρ.ρ σ₀)) + 1 := by
  obtain ⟨L, ⟨c, rfl⟩, -, hI⟩ := hord P hP
  rw [← trace_baseChangeAlong_apply f hf, ← det_baseChangeAlong_apply f hf]
  exact trace_eq_det_add_one (ρ.baseChangeAlong f hf).finrank_eq c (hI σ₀ hσ₀)

theorem baseChange_identities_eq_zero (f : A →+* B) (hf : IsLocalHom f) (ρ : GaloisRepAdic A)
    {p : ℕ} (hord : (ρ.baseChangeAlong f hf).IsOrdinaryAt p)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ₀ : σ₀ ∈ P.inertiaSubgroupIn ℚ)
    {d : A} (hchar : (ρ.ρ σ₀).charpoly = (X - C d) * (X - C 1)) (hu : IsUnit (d - 1)) :
    (∀ σ ∈ P.decompositionSubgroup ℚ, letI := f.toAlgebra
      (ordProj (ρ.ρ σ₀) 1 d * ρ.ρ σ * ordProj (ρ.ρ σ₀) d 1).baseChange B = 0) ∧
    (∀ σ ∈ P.inertiaSubgroupIn ℚ, letI := f.toAlgebra
      (ordProj (ρ.ρ σ₀) 1 d * (ρ.ρ σ - 1)).baseChange B = 0) := by
  letI := f.toAlgebra
  obtain ⟨L, ⟨c, rfl⟩, hD, hI⟩ := hord P hP
  have hu' : IsUnit (1 - d) := by rwa [← neg_sub, IsUnit.neg_iff]

  have hcharB : LinearMap.charpoly ((ρ.baseChangeAlong f hf).ρ σ₀) =
      (X - C (algebraMap A B d)) * (X - C (algebraMap A B 1)) :=
    charpoly_baseChange_eq B hchar
  have huB : IsUnit (algebraMap A B d - algebraMap A B 1) := by
    rw [← map_sub]
    exact hu.map _

  have hL : (B ∙ c 0) = LinearMap.range
      (ordProj ((ρ.baseChangeAlong f hf).ρ σ₀) (algebraMap A B d) (algebraMap A B 1)) :=
    span_singleton_eq_range_ordProj (ρ.baseChangeAlong f hf).finrank_eq hcharB huB
      (fun v => by rw [map_one, one_smul]; exact hI σ₀ hσ₀ v)
  refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
  · have h := (range_ordProj_invariant_iff hcharB huB ((ρ.baseChangeAlong f hf).ρ σ)).mp
      (by rw [← hL]; exact hD σ hσ)
    rw [LinearMap.baseChange_mul, LinearMap.baseChange_mul, ordProj_baseChange B _ hu',
      ordProj_baseChange B _ hu]
    exact h
  · have h := (sub_mem_range_ordProj_iff hcharB huB ((ρ.baseChangeAlong f hf).ρ σ)).mp
      (by rw [← hL]; exact hI σ hσ)
    rw [LinearMap.baseChange_mul, LinearMap.baseChange_sub, LinearMap.baseChange_one,
      ordProj_baseChange B _ hu']
    exact h

theorem exists_line_of_identities (ρ : GaloisRepAdic A) (P : ValuationSubring (AlgebraicClosure ℚ))
    {σ₀ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {d : A}
    (hchar : (ρ.ρ σ₀).charpoly = (X - C d) * (X - C 1)) (hu : IsUnit (d - 1))
    (hS : ∀ σ ∈ P.decompositionSubgroup ℚ, ordProj (ρ.ρ σ₀) 1 d * ρ.ρ σ * ordProj (ρ.ρ σ₀) d 1 = 0)
    (hI : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ordProj (ρ.ρ σ₀) 1 d * (ρ.ρ σ - 1) = 0) :
    ∃ L : Submodule A ρ.V,
      (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) := by
  obtain ⟨b, hb⟩ := exists_basis_range_ordProj ρ.finrank_eq hchar hu
  exact ⟨_, ⟨b, hb⟩, fun σ hσ => (range_ordProj_invariant_iff hchar hu _).mpr (hS σ hσ),
    fun σ hσ => (sub_mem_range_ordProj_iff hchar hu _).mpr (hI σ hσ)⟩

end Galois

end LCMazur.OrdJ

open LCMazur.OrdJ

theorem solution {P A B : Type} [CommRing P]
    [IsLocalRing P] [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (πA : P →+* A) (hπA : IsLocalHom πA) (πB : P →+* B) (hπB : IsLocalHom πB)
    (hinj : ∀ x, πA x = 0 → πB x = 0 → x = 0) (ρ : GaloisRepAdic P) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdetA : (ρ.baseChangeAlong πA hπA).DetIsCyclotomic p)
    (hA : (ρ.baseChangeAlong πA hπA).IsOrdinaryAt p)
    (hB : (ρ.baseChangeAlong πB hπB).IsOrdinaryAt p) : ρ.IsOrdinaryAt p := by
  intro Pl hPl
  obtain ⟨σ₀, hσ₀, hσ₀pow⟩ := exists_mem_inertiaSubgroupIn_apply_eq_sq hp hp2 Pl hPl

  have hu := isUnit_det_sub_one πA hπA ρ hdetA hσ₀pow

  have htr : LinearMap.trace P _ (ρ.ρ σ₀) = LinearMap.det (ρ.ρ σ₀) + 1 := by
    rw [← sub_eq_zero]
    refine hinj _ ?_ ?_
    · rw [map_sub, map_add, map_one, map_trace_eq_map_det_add_one πA hπA ρ hA Pl hPl hσ₀, sub_self]
    · rw [map_sub, map_add, map_one, map_trace_eq_map_det_add_one πB hπB ρ hB Pl hPl hσ₀, sub_self]
  have hchar := charpoly_eq_of_trace_eq_det_add_one ρ.finrank_eq (ρ.ρ σ₀) htr

  obtain ⟨hSA, hIA⟩ := baseChange_identities_eq_zero πA hπA ρ hA Pl hPl hσ₀ hchar hu
  obtain ⟨hSB, hIB⟩ := baseChange_identities_eq_zero πB hπB ρ hB Pl hPl hσ₀ hchar hu
  letI := πA.toAlgebra
  letI := πB.toAlgebra
  exact exists_line_of_identities ρ Pl hchar hu
    (fun σ hσ => eq_zero_of_baseChange_eq_zero_of_jointly_injective A B hinj _ (hSA σ hσ)
      (hSB σ hσ))
    (fun σ hσ => eq_zero_of_baseChange_eq_zero_of_jointly_injective A B hinj _ (hIA σ hσ)
      (hIB σ hσ))

end S_GaloisRepAdic_isOrdinaryAt_of_jointly_injective
end P2MW
export P2MW.S_GaloisRepAdic_isOrdinaryAt_of_jointly_injective (solution)
