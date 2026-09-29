-- Prove2me | solution 1 for GaloisRepAdic.exists_baseChangeAlong_isEquiv_of_jointly_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/5be60cd0-8ee8-5eae-845a-08dccfd812b6

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Theorems.Thm_GaloisRepAdic_trace_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_residual_baseChangeAlong_isEquiv
import Theorems.Thm_ResidualGaloisRep_charpoly_baseChangeAlong
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
import Theorems.Thm_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_jointly_injective
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec CuspForm.HeckeGaloisRepDatum.mk.sizeOf_spec CuspForm.HeckeGaloisRepDatum.mk.injEq CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

namespace GlueAsm

open IsLocalRing Polynomial

section General

variable {A : Type} [CommRing A]

theorem repr_mem_of_mem_smul_top {V : Type*} [AddCommGroup V] [Module A V] {ι : Type*}
    (b : Module.Basis ι A V) (I : Ideal A) {v : V} (hv : v ∈ I • (⊤ : Submodule A V)) (i : ι) :
    b.repr v i ∈ I := by
  refine Submodule.smul_induction_on hv (fun a ha w _ => ?_) (fun x y hx hy => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ha
  · rw [map_add, Finsupp.add_apply]
    exact Ideal.add_mem _ hx hy

theorem trace_mem_of_forall_mem {V : Type*} [AddCommGroup V] [Module A V] [Module.Free A V]
    [Module.Finite A V] (I : Ideal A) (f : Module.End A V)
    (hf : ∀ v, f v ∈ I • (⊤ : Submodule A V)) : LinearMap.trace A V f ∈ I := by
  classical
  let b := Module.Free.chooseBasis A V
  rw [LinearMap.trace_eq_matrix_trace A b, Matrix.trace]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  exact repr_mem_of_mem_smul_top b I (hf _) i

end General

section Reps

variable {A : Type} [CommRing A] [IsLocalRing A]

theorem trace_eq_of_equiv {ρ₁ ρ₂ : GaloisRepAdic A} (e : GaloisRepAdic.Equiv ρ₁ ρ₂)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ρ₁.trace σ = ρ₂.trace σ := by
  have h : ρ₂.ρ σ = e.toLinearEquiv.conj (ρ₁.ρ σ) := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, e.map_apply, LinearEquiv.apply_symm_apply]
  unfold GaloisRepAdic.trace
  rw [h, LinearMap.trace_conj']

theorem charpoly_eq_of_residualEquiv {k : Type} [Field k] {ρ₁ ρ₂ : ResidualGaloisRep k}
    (e : ResidualGaloisRep.Equiv ρ₁ ρ₂) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly := by
  have h : ρ₂.ρ σ = e.toLinearEquiv.conj (ρ₁.ρ σ) := by
    refine LinearMap.ext fun y => ?_
    rw [LinearEquiv.conj_apply_apply, e.map_apply, LinearEquiv.apply_symm_apply]
  rw [h, LinearEquiv.charpoly_conj]

def levelStab (ρ : GaloisRepAdic A) (I : Ideal A) :
    Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) where
  carrier := {τ | ∀ v, ρ.ρ τ v - v ∈ I • (⊤ : Submodule A ρ.V)}
  one_mem' := fun v => by
    rw [map_one, Module.End.one_apply, sub_self]; exact Submodule.zero_mem _
  mul_mem' := fun {a b} ha hb v => by
    have h1 : ρ.ρ (a * b) v - v = ρ.ρ a (ρ.ρ b v - v) + (ρ.ρ a v - v) := by
      rw [map_mul, Module.End.mul_apply, map_sub]; abel
    rw [h1]
    refine Submodule.add_mem _ ?_ (ha v)
    have hmap : (I • (⊤ : Submodule A ρ.V)).map (ρ.ρ a) ≤ I • ⊤ := by
      rw [Submodule.map_smul'']; exact Submodule.smul_mono le_rfl le_top
    exact hmap (Submodule.mem_map_of_mem (hb v))
  inv_mem' := fun {a} ha v => by
    have h := ha (ρ.ρ a⁻¹ v)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    rw [← Submodule.neg_mem_iff, neg_sub]
    exact h

theorem trace_sub_trace_mem (ρ : GaloisRepAdic A) (I : Ideal A)
    {τ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (h : τ * σ⁻¹ ∈ levelStab ρ I) :
    ρ.trace τ - ρ.trace σ ∈ I := by
  have hτ : τ = (τ * σ⁻¹) * σ := by group
  have hlin : ρ.ρ τ - ρ.ρ σ = (ρ.ρ (τ * σ⁻¹) - 1) * ρ.ρ σ := by
    conv_lhs => rw [hτ]
    rw [map_mul, sub_mul, one_mul]
  unfold GaloisRepAdic.trace
  rw [← map_sub, hlin]
  refine trace_mem_of_forall_mem I _ fun v => ?_
  rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
  exact h _

theorem trace_conj (ρ : GaloisRepAdic A) (g τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ.trace (g * τ * g⁻¹) = ρ.trace τ := by
  unfold GaloisRepAdic.trace
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, ← mul_assoc, inv_mul_cancel, one_mul]

end Reps

theorem exists_frobenius_forall_trace_sub_mem {n : ℕ} (A : Fin n → Type) [∀ i, CommRing (A i)]
    [∀ i, IsLocalRing (A i)] (ρ : ∀ i, GaloisRepAdic (A i)) (S : Finset ℕ) (m : ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧ ∃ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ ∧
      ∃ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt τ ℓ ∧
        ∀ i, (ρ i).trace σ - (ρ i).trace τ ∈ (maximalIdeal (A i)) ^ m := by
  choose L hLfin hL using fun i => (ρ i).isAdicContinuous m
  haveI := hLfin
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by convert AlgebraicClosure.instIsAlgClosure ℚ; rfl; rfl
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := ⨆ i, L i
  haveI : FiniteDimensional ℚ L' := IntermediateField.finiteDimensional_iSup_of_finite
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ L' (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ F := normalClosure.is_finiteDimensional ℚ L' (AlgebraicClosure ℚ)
  haveI : NumberField F := ⟨⟩
  haveI : Normal ℚ F := normalClosure.normal ℚ L' (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ F := ⟨⟩
  let H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    ⨅ i, levelStab (ρ i) ((maximalIdeal (A i)) ^ m)
  have hLF : ∀ i, L i ≤ F := fun i =>
    (le_iSup L i).trans (IntermediateField.le_normalClosure L')
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    refine Subgroup.mem_iInf.mpr fun i => hL i x fun y hy => ?_
    have h1 := AlgEquiv.restrictNormalHom_apply F x ⟨y, hLF i hy⟩
    have h2 := DFunLike.congr_fun hx ⟨y, hLF i hy⟩
    rw [AlgEquiv.one_apply] at h2
    have h3 := congrArg (fun z : ↥F => (z : AlgebraicClosure ℚ)) h2
    exact h1.symm.trans h3
  obtain ⟨ℓ, P, τ, g, hℓ, hℓS, hP, hτ, hmem⟩ :=
    FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker F hker S σ
  refine ⟨ℓ, hℓ, hℓS, P, hP, τ, hτ, fun i => ?_⟩
  have h := trace_sub_trace_mem (ρ i) _ (Subgroup.mem_iInf.mp hmem i)
  rw [trace_conj] at h
  rw [← Submodule.neg_mem_iff, neg_sub]
  exact h

section FiniteLocal

variable (T : Type) [CommRing T] [IsLocalRing T] [IsNoetherianRing T]

theorem exists_maximalIdeal_pow_le_map (A : Type) [CommRing A] [IsLocalRing A] [Algebra T A]
    [Module.Finite T A] [IsLocalHom (algebraMap T A)] :
    ∃ c : ℕ, (maximalIdeal A) ^ c ≤ (maximalIdeal T).map (algebraMap T A) := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing T A
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf ?_
    rintro P ⟨hJP, hP⟩
    haveI := hP
    have hcomap : (maximalIdeal T) ≤ P.comap (algebraMap T A) :=
      Ideal.le_comap_of_map_le hJP
    have hne : P.comap (algebraMap T A) ≠ ⊤ := Ideal.comap_ne_top _ hP.ne_top
    have heq : P.comap (algebraMap T A) = maximalIdeal T :=
      ((maximalIdeal.isMaximal T).eq_of_le hne hcomap).symm
    have hPmax : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap P (heq ▸ maximalIdeal.isMaximal T)
    rw [IsLocalRing.eq_maximalIdeal hPmax]
  · exact IsNoetherian.noetherian _

variable {n : ℕ} (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, Algebra T (A i)]

def diag : T →ₗ[T] (∀ i, A i) := LinearMap.pi fun i => Algebra.linearMap T (A i)

omit [IsLocalRing T] [IsNoetherianRing T] in
@[scoped simp] private theorem _root_.GlueAsm.diag_apply (x : T) (i : Fin n) : diag T A x i = algebraMap T (A i) x := rfl

p2m_export "GlueAsm" "diag_apply"
omit [IsLocalRing T] [IsNoetherianRing T] in

theorem mem_smul_top_pi (I : Ideal T) (z : ∀ i, A i)
    (hz : ∀ i, z i ∈ I.map (algebraMap T (A i))) :
    z ∈ I • (⊤ : Submodule T (∀ i, A i)) := by
  classical
  have hsingle : ∀ i, (Pi.single i (z i) : ∀ i, A i) ∈ I • (⊤ : Submodule T (∀ i, A i)) := by
    intro i
    have hzi : z i ∈ I • (⊤ : Submodule T (A i)) := by
      rw [Ideal.smul_top_eq_map]; exact hz i
    refine Submodule.smul_induction_on hzi (fun a ha w _ => ?_) (fun x y hx hy => ?_)
    · rw [Pi.single_smul]
      exact Submodule.smul_mem_smul ha Submodule.mem_top
    · rw [Pi.single_add]
      exact Submodule.add_mem _ hx hy
  have : z = ∑ i, Pi.single i (z i) := by
    ext j
    simp [Finset.sum_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => hsingle i

theorem mem_range_diag_of_forall [∀ i, Module.Finite T (A i)] (y : ∀ i, A i)
    (hy : ∀ m : ℕ, ∃ x : T, y - diag T A x ∈ (maximalIdeal T) ^ m • (⊤ : Submodule T (∀ i, A i))) :
    y ∈ LinearMap.range (diag T A) := by
  set N := LinearMap.range (diag T A)
  have hmk : N.mkQ y ∈ (⨅ m : ℕ, (maximalIdeal T) ^ m • (⊤ : Submodule T ((∀ i, A i) ⧸ N))) := by
    refine Submodule.mem_iInf _ |>.mpr fun m => ?_
    obtain ⟨x, hx⟩ := hy m
    have h0 : N.mkQ (diag T A x) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨x, rfl⟩
    have h1 : N.mkQ y = N.mkQ (y - diag T A x) := by rw [map_sub, h0, sub_zero]
    rw [h1]
    have h2 : ((maximalIdeal T) ^ m • (⊤ : Submodule T (∀ i, A i))).map N.mkQ ≤
        (maximalIdeal T) ^ m • ⊤ := by
      rw [Submodule.map_smul'']
      exact Submodule.smul_mono le_rfl le_top
    exact h2 (Submodule.mem_map_of_mem hx)
  rw [Ideal.iInf_pow_smul_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal T).ne_top,
    Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmk
  exact hmk

end FiniteLocal

set_option maxHeartbeats 3200000 in
theorem main
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (maximalIdeal T) T] [Finite (ResidueField T)]
    {n : ℕ} (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Algebra T (A i)] [∀ i, Module.Finite T (A i)]
    [hloc : ∀ i, IsLocalHom (algebraMap T (A i))]
    (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0)
    (ρbar : ResidualGaloisRep (ResidueField T)) (habs : ρbar.IsAbsolutelyIrreducible)
    (ρ : ∀ i, GaloisRepAdic (A i))
    (hres : ∀ i, (ρ i).residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap T (A i)))))
    (S₀ : Finset ℕ) (τ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → T)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          ∀ i, (ρ i).trace σ = algebraMap T (A i) (τ ℓ hℓ hℓS)) :
    ∃ ρ' : GaloisRepAdic T,
      (∀ i, ((ρ'.baseChangeAlong (algebraMap T (A i)) (hloc i)).IsEquiv (ρ i))) ∧
      ρ'.residual.IsEquiv ρbar ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
            ρ'.trace σ = τ ℓ hℓ hℓS) := by

  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      exact absurd (hinj 1 fun i => i.elim0) one_ne_zero
    · exact h
  let i₀ : Fin n := ⟨0, hn⟩

  choose c hc using fun i => exists_maximalIdeal_pow_le_map T (A i)
  let C : ℕ := ∑ i, c i
  have hC : ∀ i, (maximalIdeal (A i)) ^ C ≤ (maximalIdeal T).map (algebraMap T (A i)) := fun i =>
    (Ideal.pow_le_pow_right (Finset.single_le_sum (fun j _ => Nat.zero_le (c j))
      (Finset.mem_univ i))).trans (hc i)

  have htrT : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ x : T,
      ∀ i, (ρ i).trace σ = algebraMap T (A i) x := by
    intro σ
    have hy : ∀ m : ℕ, ∃ x : T, (fun i => (ρ i).trace σ) - diag T A x ∈
        (maximalIdeal T) ^ m • (⊤ : Submodule T (∀ i, A i)) := by
      intro m
      obtain ⟨ℓ, hℓ, hℓS, P, hP, τ', hτ', hcong⟩ :=
        exists_frobenius_forall_trace_sub_mem A ρ S₀ (C * m) σ
      refine ⟨τ ℓ hℓ hℓS, mem_smul_top_pi T A _ _ fun i => ?_⟩
      have h1 := hcong i
      rw [htr ℓ hℓ hℓS P hP τ' hτ' i, pow_mul] at h1
      have h2 : ((maximalIdeal (A i)) ^ C) ^ m ≤ ((maximalIdeal T) ^ m).map (algebraMap T (A i)) := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (hC i) m
      exact h2 h1
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (mem_range_diag_of_forall T A _ hy)
    exact ⟨x, fun i => (congrFun hx i).symm⟩
  choose tr htr' using htrT

  obtain ⟨ρ', hEq⟩ := GaloisRepAdic.exists_baseChangeAlong_isEquiv_of_forall_trace_eq (T := T) A
    hinj ρbar habs ρ hres tr htr'
  refine ⟨ρ', hEq, ?_, ?_⟩
  ·

    obtain ⟨e⟩ := hEq i₀
    obtain ⟨e'⟩ := hres i₀
    obtain ⟨e''⟩ := GaloisRepAdic.residual_baseChangeAlong_isEquiv (algebraMap T (A i₀)) (hloc i₀) ρ'
    have hcp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (ρbar.ρ σ).charpoly = (ρ'.residual.ρ σ).charpoly := by
      intro σ
      apply Polynomial.map_injective (ResidueField.map (algebraMap T (A i₀)))
        (RingHom.injective _)
      rw [← ResidualGaloisRep.charpoly_baseChangeAlong, ← ResidualGaloisRep.charpoly_baseChangeAlong,
        ← charpoly_eq_of_residualEquiv e' σ, ← charpoly_eq_of_residualEquiv e.residual σ,
        charpoly_eq_of_residualEquiv e'' σ]
    have habs' : ρ'.residual.IsAbsolutelyIrreducible :=
      ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq _ _ habs hcp
    exact ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq _ _ habs' habs
      fun σ => (hcp σ).symm
  ·
    intro ℓ hℓ hℓS P hP σ hσ
    apply sub_eq_zero.mp
    apply hinj
    intro i
    obtain ⟨e⟩ := hEq i
    rw [map_sub, ← htr ℓ hℓ hℓS P hP σ hσ i, ← trace_eq_of_equiv e σ,
      GaloisRepAdic.trace_baseChangeAlong, sub_self]

end GlueAsm
p2m_reactivate "P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_jointly_injective.GlueAsm"

open IsLocalRing

theorem solution
    {T : Type} [CommRing T] [IsLocalRing T] [IsNoetherianRing T]
    [IsAdicComplete (maximalIdeal T) T] [Finite (ResidueField T)]
    {n : ℕ} (A : Fin n → Type) [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    [∀ i, Algebra T (A i)] [∀ i, Module.Finite T (A i)]
    [hloc : ∀ i, IsLocalHom (algebraMap T (A i))]
    (hinj : ∀ x : T, (∀ i, algebraMap T (A i) x = 0) → x = 0)
    (ρbar : ResidualGaloisRep (ResidueField T)) (habs : ρbar.IsAbsolutelyIrreducible)
    (ρ : ∀ i, GaloisRepAdic (A i))
    (hres : ∀ i, (ρ i).residual.IsEquiv
      (ρbar.baseChangeAlong (ResidueField.map (algebraMap T (A i)))))
    (S₀ : Finset ℕ) (τ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → T)
    (htr : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
          ∀ i, (ρ i).trace σ = algebraMap T (A i) (τ ℓ hℓ hℓS)) :
    ∃ ρ' : GaloisRepAdic T,

      (∀ i, ((ρ'.baseChangeAlong (algebraMap T (A i)) (hloc i)).IsEquiv (ρ i))) ∧

      ρ'.residual.IsEquiv ρbar ∧

      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
        ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
          ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ ℓ →
            ρ'.trace σ = τ ℓ hℓ hℓS) :=
  GlueAsm.main A hinj ρbar habs ρ hres S₀ τ htr

end S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_jointly_injective
end P2MW
export P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_jointly_injective (solution)
