-- Prove2me | solution 1 for GaloisRepAdic.residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d9ef1427-b722-508d-b4bd-05ace1165f1f

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Theorems.Thm_ResidualGaloisRep_trace_eq_of_trace_frobenius_eq
import Theorems.Thm_ResidualGaloisRep_charpoly_eq_of_charpoly_frobenius_eq
import Theorems.Thm_FrobeniusDensity_statement
import Theorems.Thm_ResidualGaloisRep_isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq
import Theorems.Thm_ResidualGaloisRep_isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq
import Theorems.Thm_ResidualGaloisRep_IsAbsolutelyIrreducible_baseChangeAlong
import Theorems.Thm_ResidualGaloisRep_charpoly_baseChangeAlong
import Theorems.Thm_FrobeniusDensity_exists_isFrobeniusAt_conj_mem_of_le_ker
import Theorems.Thm_MonoidHom_isOpen_ker_of_cycloCharSpec
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"

set_option autoImplicit false

noncomputable section

namespace ResCmpAsm

open Polynomial IsLocalRing
open scoped TensorProduct

local notation "Galℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section RankTwo

variable {A : Type*} [CommRing A] [Nontrivial A] {V : Type*} [AddCommGroup V] [Module A V]
  [Module.Free A V] [Module.Finite A V]

theorem charpoly_eq_of_finrank_eq_two (hV : Module.finrank A V = 2) (f : Module.End A V) :
    f.charpoly = X ^ 2 - C (LinearMap.trace A V f) * X + C (LinearMap.det f) := by
  classical
  let b := Module.finBasisOfFinrankEq A V hV
  rw [← LinearMap.charpoly_toMatrix f b, LinearMap.trace_eq_matrix_trace A b, ← LinearMap.det_toMatrix b,
    Matrix.charpoly_fin_two, Matrix.trace_fin_two, Matrix.det_fin_two]

theorem trace_eq_of_charpoly_eq (hV : Module.finrank A V = 2) (f : Module.End A V) {t d : A}
    (h : f.charpoly = X ^ 2 - C t * X + C d) : LinearMap.trace A V f = t := by
  have h' := (charpoly_eq_of_finrank_eq_two hV f).symm.trans h
  have := congrArg (fun q : A[X] => q.coeff 1) h'
  simpa [coeff_X, coeff_C, coeff_X_pow] using this

theorem det_eq_of_charpoly_eq (hV : Module.finrank A V = 2) (f : Module.End A V) {t d : A}
    (h : f.charpoly = X ^ 2 - C t * X + C d) : LinearMap.det f = d := by
  have h' := (charpoly_eq_of_finrank_eq_two hV f).symm.trans h
  have := congrArg (fun q : A[X] => q.coeff 0) h'
  simpa [coeff_X, coeff_C, coeff_X_pow] using this

theorem two_mul_det_eq (hV : Module.finrank A V = 2) (f : Module.End A V) :
    2 * LinearMap.det f = LinearMap.trace A V f ^ 2 - LinearMap.trace A V (f * f) := by
  have hCH := LinearMap.aeval_self_charpoly f
  rw [charpoly_eq_of_finrank_eq_two hV f] at hCH
  simp only [map_add, map_sub, map_mul, aeval_X, aeval_C, map_pow, Module.algebraMap_end_eq_smul_id] at hCH
  have h1 : (LinearMap.trace A V f • LinearMap.id * f) = LinearMap.trace A V f • f := by
    rw [smul_mul_assoc, ← Module.End.one_eq_id, one_mul]
  rw [h1] at hCH
  have htr := congrArg (LinearMap.trace A V) hCH
  rw [map_zero, map_add, map_sub, map_smul, map_smul, LinearMap.trace_id, hV] at htr
  simp only [smul_eq_mul, Nat.cast_ofNat] at htr
  rw [pow_two] at htr
  rw [sq]
  linear_combination htr

end RankTwo

theorem charpoly_eq_of_forall_trace_eq {k : Type} [Field k] (h2 : (2 : k) ≠ 0)
    (ρ₁ ρ₂ : ResidualGaloisRep k)
    (h : ∀ σ : Galℚ, LinearMap.trace k ρ₁.V (ρ₁.ρ σ) = LinearMap.trace k ρ₂.V (ρ₂.ρ σ)) (σ : Galℚ) :
    (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly := by
  have hd : LinearMap.det (ρ₁.ρ σ) = LinearMap.det (ρ₂.ρ σ) := by
    have e1 := two_mul_det_eq ρ₁.finrank_eq (ρ₁.ρ σ)
    have e2 := two_mul_det_eq ρ₂.finrank_eq (ρ₂.ρ σ)
    rw [← map_mul, h σ, h (σ * σ)] at e1
    rw [← map_mul] at e2
    exact mul_left_cancel₀ h2 (e1.trans e2.symm)
  rw [charpoly_eq_of_finrank_eq_two ρ₁.finrank_eq, charpoly_eq_of_finrank_eq_two ρ₂.finrank_eq, h σ, hd]

section Det

variable {A : Type} [CommRing A]

theorem det_conj {V : Type*} [AddCommGroup V] [Module A V]
    (ρ : Galℚ →* Module.End A V) (g τ : Galℚ) :
    LinearMap.det (ρ (g * τ * g⁻¹)) = LinearMap.det (ρ τ) := by
  let f : Galℚ →* A := LinearMap.det.comp ρ
  show f (g * τ * g⁻¹) = f τ
  rw [map_mul, map_mul, mul_comm (f g) (f τ), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

theorem det_mul_sub_det_mem {V : Type*} [AddCommGroup V] [Module A V] [Module.Free A V] [Module.Finite A V]
    (I : Ideal A) (f g : Module.End A V) (hf : ∀ v, f v - v ∈ I • (⊤ : Submodule A V)) :
    LinearMap.det (f * g) - LinearMap.det g ∈ I := by
  rw [← Ideal.Quotient.eq, LinearMap.det.map_mul]
  suffices h : Ideal.Quotient.mk I (LinearMap.det f) = 1 by rw [map_mul, h, one_mul]
  have hbc : Ideal.Quotient.mk I (LinearMap.det f) = LinearMap.det (f.baseChange (A ⧸ I)) := by
    rw [LinearMap.det_baseChange]; rfl
  rw [hbc]
  have hkill : ∀ x ∈ I • (⊤ : Submodule A V), ∀ c : A ⧸ I, c ⊗ₜ[A] x = (0 : (A ⧸ I) ⊗[A] V) := by
    intro x hx c
    refine Submodule.smul_induction_on (p := fun x => c ⊗ₜ[A] x = (0 : (A ⧸ I) ⊗[A] V)) hx ?_ ?_
    · intro a ha w _
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul, TensorProduct.zero_tmul]
    · intro x y hx hy
      rw [TensorProduct.tmul_add, hx, hy, add_zero]
  have h1 : f.baseChange (A ⧸ I) = 1 := by
    refine LinearMap.ext fun w => ?_
    induction w using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]
    | tmul c v =>
      rw [LinearMap.baseChange_tmul, Module.End.one_apply, ← sub_eq_zero, ← TensorProduct.tmul_sub]
      exact hkill _ (hf v) c
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  rw [h1, LinearMap.det.map_one]

end Det

theorem exists_frob_conj {n : ℕ} (E : Fin n → IntermediateField ℚ (AlgebraicClosure ℚ))
    (hE : ∀ j, FiniteDimensional ℚ (E j)) (S : Finset ℕ) (σ : Galℚ) :
    ∃ (ℓ : ℕ) (A : ValuationSubring (AlgebraicClosure ℚ)) (τ g : Galℚ),
      ℓ.Prime ∧ ℓ ∉ S ∧ A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ ∧
        ∀ j, ∀ y ∈ E j, (g * τ * g⁻¹ * σ⁻¹) y = y := by
  haveI := hE
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := by
    convert AlgebraicClosure.instIsAlgClosure ℚ <;> first | rfl | exact Subsingleton.elim _ _
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := ⨆ j, E j
  haveI : FiniteDimensional ℚ L' := IntermediateField.finiteDimensional_iSup_of_finite
  let F : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.normalClosure ℚ L' (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ F := normalClosure.is_finiteDimensional ℚ L' (AlgebraicClosure ℚ)
  haveI : NumberField F := ⟨⟩
  haveI : Normal ℚ F := normalClosure.normal ℚ L' (AlgebraicClosure ℚ)
  haveI : IsGalois ℚ F := ⟨⟩
  let H : Subgroup Galℚ := ⨅ j, (E j).fixingSubgroup
  have hEF : ∀ j, E j ≤ F := fun j => (le_iSup E j).trans (IntermediateField.le_normalClosure L')
  have hker : (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ H := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    refine Subgroup.mem_iInf.mpr fun j => ?_
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro y hy
    have h1 := AlgEquiv.restrictNormalHom_apply F x ⟨y, hEF j hy⟩
    have h2 := DFunLike.congr_fun hx ⟨y, hEF j hy⟩
    rw [AlgEquiv.one_apply] at h2
    have h3 := congrArg (fun z : ↥F => (z : AlgebraicClosure ℚ)) h2
    exact h1.symm.trans h3
  obtain ⟨ℓ, A, τ, g, hℓ, hℓS, hA, hτ, hmem⟩ :=
    FrobeniusDensity.exists_isFrobeniusAt_conj_mem_of_le_ker F hker S σ
  refine ⟨ℓ, A, τ, g, hℓ, hℓS, hA, hτ, fun j y hy => ?_⟩
  have := Subgroup.mem_iInf.mp hmem j
  rw [IntermediateField.mem_fixingSubgroup_iff] at this
  exact this y hy

theorem exists_level_residual {k : Type} [Field k] (ρ : ResidualGaloisRep k) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∀ x : Galℚ, (∀ y ∈ E, x y = y) → ρ.ρ x = 1 :=
  ρ.factorsThroughFiniteLevel

theorem exists_level_of_isOpen_ker {M : Type*} [Group M] (f : Galℚ →* M)
    (hf : IsOpen ((f.ker : Subgroup Galℚ) : Set Galℚ)) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧
      ∀ x : Galℚ, (∀ y ∈ E, x y = y) → f x = 1 := by
  have hmem : ((f.ker : Subgroup Galℚ) : Set Galℚ) ∈ nhds (1 : Galℚ) := hf.mem_nhds (Subgroup.one_mem _)
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ (AlgebraicClosure ℚ) _).mp hmem
  refine ⟨E, hE, fun x hx => ?_⟩
  have : x ∈ (E.fixingSubgroup : Set Galℚ) := by
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]; exact hx
  exact MonoidHom.mem_ker.mp (hsub this)

theorem exists_isPrimitiveRoot (m : ℕ) [NeZero m] :
    ∃ ζ : AlgebraicClosure ℚ, IsPrimitiveRoot ζ m := by
  haveI : NeZero (m : ℚ) := ⟨by exact_mod_cast NeZero.ne m⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) m

def toRingAut : Galℚ →* (AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) where
  toFun σ := σ.toRingEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem exists_cyc (m : ℕ) [NeZero m] :
    ∃ κ : Galℚ →* (ZMod m)ˣ, ∀ (σ : Galℚ) (μ : AlgebraicClosure ℚ), μ ^ m = 1 →
      σ μ = μ ^ ((κ σ : ZMod m)).val := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot m
  have hn : Nat.card (rootsOfUnity m (AlgebraicClosure ℚ)) = m := hζ.card_rootsOfUnity
  refine ⟨(modularCyclotomicCharacter (AlgebraicClosure ℚ) hn).comp toRingAut, fun σ μ hμ => ?_⟩
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne m)] at hμ
    exact zero_ne_one hμ
  let u : (AlgebraicClosure ℚ)ˣ := Units.mk0 μ hμ0
  have hu : u ∈ rootsOfUnity m (AlgebraicClosure ℚ) := by
    rw [mem_rootsOfUnity]; ext; simp [u, hμ]
  have := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) hn σ.toRingEquiv hu
  first | simpa [u] using this | (simp [u] at this; exact this)

theorem cyc_eq_one_of_apply_eq {m : ℕ} [NeZero m] (κ : Galℚ →* (ZMod m)ˣ)
    (hκ : ∀ (σ : Galℚ) (μ : AlgebraicClosure ℚ), μ ^ m = 1 → σ μ = μ ^ ((κ σ : ZMod m)).val)
    {ζ : AlgebraicClosure ℚ} (hζ : IsPrimitiveRoot ζ m) {x : Galℚ} (hx : x ζ = ζ) : κ x = 1 := by
  by_cases hm1 : m = 1
  · subst hm1; exact Subsingleton.elim _ _
  have h := hκ x ζ hζ.pow_eq_one
  rw [hx] at h
  have h1 : ζ ^ (1 : ℕ) = ζ ^ ((κ x : ZMod m)).val := by rw [pow_one]; exact h
  have hlt : 1 < m := lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr (NeZero.ne m)) (Ne.symm hm1)
  have := hζ.pow_inj hlt (ZMod.val_lt _) h1
  refine Units.ext (ZMod.val_injective m ?_)
  rw [← this, Units.val_one, ZMod.val_one'' hm1]

theorem val_cyc_eq_mod {m : ℕ} [NeZero m] (κ : Galℚ →* (ZMod m)ˣ)
    (hκ : ∀ (σ : Galℚ) (μ : AlgebraicClosure ℚ), μ ^ m = 1 → σ μ = μ ^ ((κ σ : ZMod m)).val)
    {σ : Galℚ} {b : ℕ} (hb : ∀ μ : AlgebraicClosure ℚ, μ ^ m = 1 → σ μ = μ ^ b) :
    ((κ σ : ZMod m)).val = b % m := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot m
  have h1 := hκ σ ζ hζ.pow_eq_one
  rw [hb ζ hζ.pow_eq_one] at h1
  have h2 : ζ ^ (b % m) = ζ ^ ((κ σ : ZMod m)).val := by
    rw [← h1]
    conv_rhs => rw [← Nat.mod_add_div b m, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  exact (hζ.pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne m))) (ZMod.val_lt _) h2).symm

theorem exists_maximalIdeal_pow_le {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CharZero O] (p : ℕ) [Fact p.Prime] (n : ℕ) :
    ∃ m : ℕ, maximalIdeal O ^ m ≤ Ideal.span {((p ^ n : ℕ) : O)} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : Ideal.span {((p ^ n : ℕ) : O)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast pow_ne_zero n (Fact.out : p.Prime).ne_zero
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hne hϖ
  refine ⟨m, le_of_eq ?_⟩
  rw [hm, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]

theorem main
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (p : ℕ) [Fact p.Prime] (hpO : (p : O) ∈ maximalIdeal O)
    (ρ : GaloisRepAdic O)
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (habs : ρbar.IsAbsolutelyIrreducible)
    (ψ : k →+* ResidueField O)
    (L : ℕ) [NeZero L] (κ : Galℚ →* (ZMod L)ˣ)
    (hκ : ∀ (σ : Galℚ) (μ : AlgebraicClosure ℚ), μ ^ L = 1 → σ μ = μ ^ ((κ σ : ZMod L)).val)
    (χ : (ZMod L)ˣ →* Oˣ)
    (h2 : p ≠ 2 ∨ ∀ u : (ZMod L)ˣ, residue O (χ u) = 1)
    (S₀ : Finset ℕ) (a : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → O) (abar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → k)
    (hred : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀), residue O (a ℓ hℓ hℓS) = ψ (abar ℓ hℓ hℓS))
    (hρ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Galℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) =
            X ^ 2 - C (a ℓ hℓ hℓS) * X + C ((χ (κ σ) : O) * (ℓ : O)))
    (hρbar : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : Galℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (abar ℓ hℓ hℓS) * X + C (ℓ : k)) :
    ρ.residual.IsEquiv (ρbar.baseChangeAlong ψ) ∧
    (∀ σ : Galℚ, residue O (χ (κ σ)) = 1) ∧
    (∀ (n : ℕ) (σ : Galℚ) (b : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ b) →
        LinearMap.det (ρ.ρ σ) - (b : O) * (χ (κ σ) : O) ∈ Ideal.span {((p ^ n : ℕ) : O)}) := by
  classical
  have hprime : p.Prime := Fact.out

  have hp0 : (p : ResidueField O) = 0 := by
    rw [← map_natCast (residue O), residue_eq_zero_iff]; exact hpO
  haveI : CharP (ResidueField O) p := (CharP.charP_iff_prime_eq_zero hprime).mpr hp0
  set ρ₁ : ResidualGaloisRep (ResidueField O) := ρ.residual with hρ₁
  set ρ₂ : ResidualGaloisRep (ResidueField O) := ρbar.baseChangeAlong ψ with hρ₂

  let S₁ : Finset ℕ := insert p S₀
  have hS₁ : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₁ → ℓ ∉ S₀ ∧ ℓ ≠ p := by
    intro ℓ _ hℓS
    simp only [S₁, Finset.mem_insert, not_or] at hℓS
    exact ⟨hℓS.2, hℓS.1⟩
  have hℓk : ∀ ℓ : ℕ, ℓ.Prime → ℓ ≠ p → (ℓ : ResidueField O) ≠ 0 := by
    intro ℓ hℓ hℓp h
    rw [CharP.cast_eq_zero_iff (ResidueField O) p] at h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq hprime hℓ).mp h).symm

  have hcp₁ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ : Galℚ), A.LiesOverPrime ℓ → A.IsFrobeniusAt τ ℓ →
        (ρ₁.ρ τ).charpoly = X ^ 2 - C (residue O (a ℓ hℓ hℓS)) * X +
          C (residue O (χ (κ τ)) * (ℓ : ResidueField O)) := by
    intro ℓ hℓ hℓS A τ hA hτ
    show ((ρ.ρ τ).baseChange (ResidueField O)).charpoly = _
    rw [LinearMap.charpoly_baseChange, hρ ℓ hℓ hℓS A hA τ hτ]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]
  have hcp₂ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀) (A : ValuationSubring (AlgebraicClosure ℚ))
      (τ : Galℚ), A.LiesOverPrime ℓ → A.IsFrobeniusAt τ ℓ →
        (ρ₂.ρ τ).charpoly = X ^ 2 - C (ψ (abar ℓ hℓ hℓS)) * X + C (ℓ : ResidueField O) := by
    intro ℓ hℓ hℓS A τ hA hτ
    rw [hρ₂, ResidualGaloisRep.charpoly_baseChangeAlong, hρbar ℓ hℓ hℓS A hA τ hτ]
    simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow]

  have hcp : ∀ σ : Galℚ, (ρ₁.ρ σ).charpoly = (ρ₂.ρ σ).charpoly := by
    rcases h2 with hp2 | hχ1
    · have h2k : (2 : ResidueField O) ≠ 0 := by
        have := hℓk 2 Nat.prime_two (Ne.symm hp2)
        exact_mod_cast this
      have htr : ∀ σ : Galℚ, LinearMap.trace _ ρ₁.V (ρ₁.ρ σ) = LinearMap.trace _ ρ₂.V (ρ₂.ρ σ) := by
        refine ResidualGaloisRep.trace_eq_of_trace_frobenius_eq ρ₁ ρ₂ S₀ ?_
        intro ℓ hℓ hℓS A τ hA hτ
        rw [trace_eq_of_charpoly_eq ρ₁.finrank_eq _ (hcp₁ ℓ hℓ hℓS A τ hA hτ),
          trace_eq_of_charpoly_eq ρ₂.finrank_eq _ (hcp₂ ℓ hℓ hℓS A τ hA hτ), hred]
      exact charpoly_eq_of_forall_trace_eq h2k ρ₁ ρ₂ htr
    · refine ResidualGaloisRep.charpoly_eq_of_charpoly_frobenius_eq
        (fun M _ _ _ => FrobeniusDensity.statement M) ρ₁ ρ₂ S₀ ?_
      intro ℓ hℓ hℓS A τ hA hτ
      rw [hcp₁ ℓ hℓ hℓS A τ hA hτ, hcp₂ ℓ hℓ hℓS A τ hA hτ, hred, hχ1, one_mul]
  have habs₂ : ρ₂.IsAbsolutelyIrreducible := habs.baseChangeAlong ψ
  have habs₁ : ρ₁.IsAbsolutelyIrreducible :=
    ResidualGaloisRep.isAbsolutelyIrreducible_of_isAbsolutelyIrreducible_of_charpoly_eq ρ₂ ρ₁ habs₂
      (fun σ => (hcp σ).symm)
  have hequiv : ρ₁.IsEquiv ρ₂ :=
    ResidualGaloisRep.isEquiv_of_isAbsolutelyIrreducible_of_charpoly_eq ρ₁ ρ₂ habs₁ habs₂ hcp

  obtain ⟨E₁, hE₁, hE₁fix⟩ := exists_level_residual ρ₁
  obtain ⟨E₂, hE₂, hE₂fix⟩ := exists_level_residual ρ₂
  obtain ⟨E₃, hE₃, hE₃fix⟩ := exists_level_of_isOpen_ker κ (MonoidHom.isOpen_ker_of_cycloCharSpec L κ hκ)
  have hκfrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓL : ¬ ℓ ∣ L) (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ τ : Galℚ, A.IsFrobeniusAt τ ℓ →
        κ τ = ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓL) := fun ℓ hℓ hℓL =>
    ValuationSubring.cycloChar_eq_unitOfCoprime_of_isFrobeniusAt L κ hκ ℓ hℓ hℓL

  have hconj : ∀ {M : Type} [Monoid M] (f : Galℚ →* M) (g τ σ : Galℚ), f (g * τ * g⁻¹ * σ⁻¹) = 1 →
      f (g * τ * g⁻¹) = f σ := by
    intro M _ f g τ σ h
    have : g * τ * g⁻¹ = (g * τ * g⁻¹ * σ⁻¹) * σ := by group
    rw [this, map_mul, h, one_mul]
  have hκconj : ∀ (g τ σ : Galℚ), κ (g * τ * g⁻¹ * σ⁻¹) = 1 → κ τ = κ σ := by
    intro g τ σ h
    have := hconj κ g τ σ h
    rwa [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at this
  have hn : ∀ σ : Galℚ, residue O (χ (κ σ)) = 1 := by
    intro σ
    obtain ⟨ℓ, A, τ, g, hℓ, hℓS, hA, hτ, hfix⟩ := exists_frob_conj ![E₁, E₂, E₃]
      (by intro j; fin_cases j <;> assumption) S₁ σ
    obtain ⟨hℓS₀, hℓp⟩ := hS₁ ℓ hℓ hℓS
    have h1 : ρ₁.ρ (g * τ * g⁻¹) = ρ₁.ρ σ := hconj ρ₁.ρ g τ σ (hE₁fix _ (hfix 0))
    have h2' : ρ₂.ρ (g * τ * g⁻¹) = ρ₂.ρ σ := hconj ρ₂.ρ g τ σ (hE₂fix _ (hfix 1))
    have h3 : κ τ = κ σ := hκconj g τ σ (hE₃fix _ (hfix 2))
    have hd : LinearMap.det (ρ₁.ρ σ) = LinearMap.det (ρ₂.ρ σ) := by
      have h := hcp σ
      rw [charpoly_eq_of_finrank_eq_two ρ₁.finrank_eq, charpoly_eq_of_finrank_eq_two ρ₂.finrank_eq] at h
      have := congrArg (fun q : (ResidueField O)[X] => q.coeff 0) h
      simpa [coeff_X, coeff_C, coeff_X_pow] using this
    rw [← h1, ← h2', det_conj, det_conj, det_eq_of_charpoly_eq ρ₁.finrank_eq _ (hcp₁ ℓ hℓ hℓS₀ A τ hA hτ),
      det_eq_of_charpoly_eq ρ₂.finrank_eq _ (hcp₂ ℓ hℓ hℓS₀ A τ hA hτ), h3] at hd
    have hℓ0 := hℓk ℓ hℓ hℓp
    calc residue O (χ (κ σ)) = residue O (χ (κ σ)) * (ℓ : ResidueField O) * (ℓ : ResidueField O)⁻¹ := by
          rw [mul_inv_cancel_right₀ hℓ0]
      _ = 1 := by rw [hd, mul_inv_cancel₀ hℓ0]

  refine ⟨hequiv, hn, fun n σ b hb => ?_⟩
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0
    rw [pow_zero, Nat.cast_one, Ideal.span_singleton_one]
    exact Submodule.mem_top
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hprime.ne_zero⟩

  obtain ⟨m, hm⟩ := exists_maximalIdeal_pow_le (O := O) p n
  obtain ⟨E₄, hE₄, hE₄fix⟩ := ρ.isAdicContinuous m

  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (p ^ n)
  obtain ⟨κ', hκ'⟩ := exists_cyc (p ^ n)
  let E₅ : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.adjoin ℚ {ζ}
  have hE₅ : FiniteDimensional ℚ E₅ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (R := ℚ) ζ)
  obtain ⟨ℓ, A, τ, g, hℓ, hℓS, hA, hτ, hfix⟩ := exists_frob_conj ![E₃, E₄, E₅]
    (by intro j; fin_cases j <;> assumption) S₁ σ
  obtain ⟨hℓS₀, hℓp⟩ := hS₁ ℓ hℓ hℓS
  set x : Galℚ := g * τ * g⁻¹ * σ⁻¹ with hx

  have h3 : κ τ = κ σ := hκconj g τ σ (hE₃fix _ (hfix 0))

  have hdet : LinearMap.det (ρ.ρ σ) - LinearMap.det (ρ.ρ τ) ∈ maximalIdeal O ^ m := by
    have hgt : g * τ * g⁻¹ = x * σ := by rw [hx]; group
    have h := det_mul_sub_det_mem (maximalIdeal O ^ m) (ρ.ρ x) (ρ.ρ σ) (hE₄fix x (hfix 1))
    rw [← map_mul, ← hgt, det_conj] at h
    rw [← Submodule.neg_mem_iff, neg_sub]
    exact h

  have hdetτ : LinearMap.det (ρ.ρ τ) = (χ (κ τ) : O) * (ℓ : O) :=
    det_eq_of_charpoly_eq ρ.finrank_eq _ (hρ ℓ hℓ hℓS₀ A hA τ hτ)

  have hℓpn : ¬ ℓ ∣ p ^ n := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq hℓ hprime).mp (hℓ.dvd_of_dvd_pow h))
  have hκ'τ : κ' τ = ZMod.unitOfCoprime ℓ (hℓ.coprime_iff_not_dvd.mpr hℓpn) :=
    ValuationSubring.cycloChar_eq_unitOfCoprime_of_isFrobeniusAt (p ^ n) κ' hκ' ℓ hℓ hℓpn A hA τ hτ
  have hκ'x : κ' x = 1 :=
    cyc_eq_one_of_apply_eq κ' hκ' hζ (hfix 2 ζ (IntermediateField.mem_adjoin_simple_self ℚ ζ))
  have hκ'σ : κ' σ = κ' τ := by
    have := hconj κ' g τ σ hκ'x
    rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm] at this
    exact this.symm
  have hbmod : b % p ^ n = ℓ % p ^ n := by
    rw [← val_cyc_eq_mod κ' hκ' hb, hκ'σ, hκ'τ, ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  have hℓb : (ℓ : O) - (b : O) ∈ Ideal.span {((p ^ n : ℕ) : O)} := by
    have hmod : (b : ℤ) ≡ (ℓ : ℤ) [ZMOD ((p ^ n : ℕ) : ℤ)] := by
      rw [Int.ModEq, ← Int.natCast_mod, ← Int.natCast_mod, hbmod]
    obtain ⟨c, hc⟩ := Int.modEq_iff_dvd.mp hmod
    refine Ideal.mem_span_singleton'.mpr ⟨(c : O), ?_⟩
    have := congrArg (fun z : ℤ => (z : O)) hc
    push_cast at this ⊢
    rw [this, mul_comm]

  have hspan : LinearMap.det (ρ.ρ σ) - (b : O) * (χ (κ σ) : O) =
      (LinearMap.det (ρ.ρ σ) - LinearMap.det (ρ.ρ τ)) + (χ (κ σ) : O) * ((ℓ : O) - (b : O)) := by
    rw [hdetτ, h3]; ring
  rw [hspan]
  exact Ideal.add_mem _ (hm hdet) (Ideal.mul_mem_left _ _ hℓb)

end ResCmpAsm

end

open Polynomial IsLocalRing in
theorem solution
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (p : ℕ) [Fact p.Prime] (hpO : (p : O) ∈ maximalIdeal O)
    (ρ : GaloisRepAdic O)
    {k : Type} [Field k] (ρbar : ResidualGaloisRep k) (habs : ρbar.IsAbsolutelyIrreducible)
    (ψ : k →+* ResidueField O)
    (L : ℕ) [NeZero L] (κ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod L)ˣ)
    (hκ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ),
      μ ^ L = 1 → σ μ = μ ^ ((κ σ : ZMod L)).val)
    (χ : (ZMod L)ˣ →* Oˣ)
    (h2 : p ≠ 2 ∨ ∀ u : (ZMod L)ˣ, residue O (χ u) = 1)
    (S₀ : Finset ℕ) (a : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → O) (abar : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S₀ → k)
    (hred : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀), residue O (a ℓ hℓ hℓS) = ψ (abar ℓ hℓ hℓS))
    (hρ : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρ.ρ σ) =
            X ^ 2 - C (a ℓ hℓ hℓS) * X + C ((χ (κ σ) : O) * (ℓ : O)))
    (hρbar : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S₀),
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          LinearMap.charpoly (ρbar.ρ σ) = X ^ 2 - C (abar ℓ hℓ hℓS) * X + C (ℓ : k)) :
    ρ.residual.IsEquiv (ρbar.baseChangeAlong ψ) ∧
    (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, residue O (χ (κ σ)) = 1) ∧
    (∀ (n : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ b) →
        LinearMap.det (ρ.ρ σ) - (b : O) * (χ (κ σ) : O) ∈ Ideal.span {((p ^ n : ℕ) : O)}) :=
  ResCmpAsm.main p hpO ρ ρbar habs ψ L κ hκ χ h2 S₀ a abar hred hρ hρbar

end S_GaloisRepAdic_residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq
end P2MW
export P2MW.S_GaloisRepAdic_residual_isEquiv_and_det_sub_mem_of_charpoly_frobenius_eq (solution)
