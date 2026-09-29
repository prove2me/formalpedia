-- Prove2me | solution 1 for GaloisRep.DeformationRingData.algHom_inertiaCharacter_eq_one_of_forall_isUnramifiedAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4432d50f-14ee-51b9-a613-41edc4225c66

import Definitions.Def_GaloisRep_DeformationRingData
import Definitions.Def_CuspForm_HeckeGaloisRepDatum
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_IntegralStructure
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_GaloisRep_LocalConditions
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_ResidualEquiv
import Definitions.Def_Algebra_PatchingDatum
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Length
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_apply_eq_pow
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_mem_inertiaSubgroupIn
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.Ideal.GoingUp
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_DeformationRingData_algHom_inertiaCharacter_eq_one_of_forall_isUnramifiedAt

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open IsLocalRing Polynomial
open scoped TensorProduct

local notation "ℚbar" => AlgebraicClosure ℚ
local notation "𝔾" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace TWLoc

theorem exists_mem_inertiaSubgroupIn_cyc_eq' {q : ℕ} (hq : q.Prime) (P : ValuationSubring ℚbar) (hP : P.LiesOverPrime q)
    (cyc : 𝔾 →* (ZMod q)ˣ) (hcyc : ∀ (σ : 𝔾) (μ : ℚbar), μ ^ q = 1 → σ μ = μ ^ ((cyc σ : ZMod q).val))
    (u : (ZMod q)ˣ) : ∃ σ ∈ P.inertiaSubgroupIn ℚ, cyc σ = u := by
  obtain ⟨σ, hσ, hσμ⟩ := ValuationSubring.exists_mem_inertiaSubgroupIn_apply_eq_pow P hq hP u
  haveI : NeZero (q : ℚbar) := ⟨Nat.cast_ne_zero.mpr hq.ne_zero⟩
  haveI : NeZero q := ⟨hq.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚbar q
  refine ⟨σ, hσ, Units.ext (ZMod.val_injective q ?_)⟩
  have h1 := hcyc σ ζ hζ.pow_eq_one
  have h2 := hσμ ζ hζ.pow_eq_one
  exact hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) (h1.symm.trans h2)

theorem exists_liesOverPrime {q : ℕ} (hq : q.Prime) : ∃ P : ValuationSubring ℚbar, P.LiesOverPrime q := by
  have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hprime : (Ideal.span {(q : ℤ)}).IsPrime := (Ideal.span_singleton_prime hqZ.ne_zero).mpr hqZ
  haveI hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    hprime.isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hqZ.ne_zero)
  obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := integralClosure ℤ ℚbar)
    (Ideal.span {(q : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ (integralClosure ℤ ℚbar)).injective_int]
      exact bot_le)
  haveI := hQmax
  have hqQ : (q : integralClosure ℤ ℚbar) ∈ Q := by
    have h : (q : ℤ) ∈ Q.comap (algebraMap ℤ (integralClosure ℤ ℚbar)) := by
      rw [hQ]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.mem_comap, map_natCast] at h
    exact h
  obtain ⟨P, hP, -⟩ := ValuationSubring.exists_liesOverPrime_mem_inertiaSubgroupIn Q hq hqQ 1
    (fun b => ⟨0, Q.zero_mem, by simp⟩)
  exact ⟨P, hP⟩

end TWLoc

open TWLoc in

theorem solution
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] [IsAdicComplete (maximalIdeal 𝒪) 𝒪]
    (p : ℕ) {ρbar : ResidualGaloisRep (ResidueField 𝒪)}
    {𝒟₀ 𝒟Q : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop}
    (D₀ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟₀) (DQ : GaloisRep.DeformationRingData 𝒪 ρbar 𝒟Q)
    {q : ℕ} (hq : q.Prime)
    (h₀ : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A] (ρ : GaloisRepAdic A), 𝒟₀ ρ → ρ.IsUnramifiedAt q)
    (ε : DQ.R →ₐ[𝒪] D₀.R) (hε : IsLocalHom (ε : DQ.R →+* D₀.R))
    (hερ : (DQ.ρ.baseChangeAlong (ε : DQ.R →+* D₀.R) hε).IsEquiv D₀.ρ)
    {k : ℕ}
    (cyc : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (ZMod q)ˣ)
    (hcyc : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (μ : AlgebraicClosure ℚ), μ ^ q = 1 →
      σ μ = μ ^ ((cyc σ : ZMod q).val))
    (πΔ : (ZMod q)ˣ →* Multiplicative (ZMod (p ^ k))) (hπΔ : Function.Surjective πΔ)
    (χ : Multiplicative (ZMod (p ^ k)) →* DQ.Rˣ)
    (hχ : ∀ (P : ValuationSubring (AlgebraicClosure ℚ)), P.LiesOverPrime q →
      ∃ b : Module.Basis (Fin 2) DQ.R DQ.ρ.V, ∀ σ ∈ P.inertiaSubgroupIn ℚ,
        DQ.ρ.ρ σ (b 0) = ((χ (πΔ (cyc σ)) : DQ.Rˣ) : DQ.R) • b 0 ∧
        DQ.ρ.ρ σ (b 1) = (((χ (πΔ (cyc σ)))⁻¹ : DQ.Rˣ) : DQ.R) • b 1)
    (d : Multiplicative (ZMod (p ^ k))) :
    ε ((χ d : DQ.Rˣ) : DQ.R) = 1 := by
  classical
  have hunr : D₀.ρ.IsUnramifiedAt q := h₀ D₀.ρ D₀.isOfType
  obtain ⟨P, hP⟩ := exists_liesOverPrime hq
  obtain ⟨b, hb⟩ := hχ P hP
  obtain ⟨u, hu⟩ := hπΔ d
  obtain ⟨σ, hσ, hσu⟩ := exists_mem_inertiaSubgroupIn_cyc_eq' hq P hP cyc hcyc u
  have h0 : DQ.ρ.ρ σ (b 0) = ((χ d : DQ.Rˣ) : DQ.R) • b 0 := by rw [(hb σ hσ).1, hσu, hu]
  obtain ⟨e⟩ := hερ
  have h1 : D₀.ρ.ρ σ = 1 := hunr P hP σ hσ
  have h2 : ∀ x, (DQ.ρ.baseChangeAlong (ε : DQ.R →+* D₀.R) hε).ρ σ x = x := by
    intro x
    apply e.toLinearEquiv.injective
    rw [e.map_apply, h1]
    rfl
  letI : Algebra DQ.R D₀.R := (ε : DQ.R →+* D₀.R).toAlgebra
  set c : DQ.R := ((χ d : DQ.Rˣ) : DQ.R) with hc
  have h3 : (DQ.ρ.baseChangeAlong (ε : DQ.R →+* D₀.R) hε).ρ σ ((1 : D₀.R) ⊗ₜ[DQ.R] b 0) =
      (ε c) • ((1 : D₀.R) ⊗ₜ[DQ.R] b 0) := by
    change (DQ.ρ.ρ σ).baseChange D₀.R ((1 : D₀.R) ⊗ₜ[DQ.R] b 0) = _
    rw [LinearMap.baseChange_tmul, h0, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  have h4 : (ε c) • ((1 : D₀.R) ⊗ₜ[DQ.R] b 0) = (1 : D₀.R) ⊗ₜ[DQ.R] b 0 := by
    rw [← h3]
    exact h2 _
  have h5 := congrArg (fun v => (Algebra.TensorProduct.basis D₀.R b).repr v 0) h4
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h5
  rw [← Algebra.TensorProduct.basis_apply, Module.Basis.repr_self, Finsupp.single_eq_same, mul_one] at h5
  exact h5

#print axioms solution

end S_GaloisRep_DeformationRingData_algHom_inertiaCharacter_eq_one_of_forall_isUnramifiedAt
end P2MW
export P2MW.S_GaloisRep_DeformationRingData_algHom_inertiaCharacter_eq_one_of_forall_isUnramifiedAt (solution)
