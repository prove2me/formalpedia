-- Prove2me | solution 1 for GaloisRepAdic.isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f4dd643b-e91c-56e6-9db7-c9dcc4bfe666

import Mathlib
import Definitions.Def_GaloisRep_StrictOrdinary
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ModularCurve_exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false

namespace P2mStrictOfLine

open Module

variable {A : Type} [CommRing A] {V : Type} [AddCommGroup V] [Module A V]
  (b : Basis (Fin 2) A V)

theorem repr_one_eq_zero_of_mem {v : V} (hv : v ∈ A ∙ b 0) : b.repr v 1 = 0 := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul, Finsupp.smul_apply, b.repr_self, Finsupp.single_apply, if_neg (by decide),
    smul_zero]

theorem mem_of_repr_one_eq_zero {v : V} (hv : b.repr v 1 = 0) : v ∈ A ∙ b 0 := by
  have h := b.sum_repr v
  rw [Fin.sum_univ_two, hv, zero_smul, add_zero] at h
  rw [← h]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

theorem mem_iff_repr_one_eq_zero (v : V) : v ∈ A ∙ b 0 ↔ b.repr v 1 = 0 :=
  ⟨repr_one_eq_zero_of_mem b, mem_of_repr_one_eq_zero b⟩

noncomputable def xc (f : V →ₗ[A] V) : A := b.repr (f (b 0)) 0

noncomputable def yc (f : V →ₗ[A] V) : A := b.repr (f (b 1)) 0

noncomputable def zc (f : V →ₗ[A] V) : A := b.repr (f (b 1)) 1

def Pres (f : V →ₗ[A] V) : Prop := ∀ v ∈ A ∙ b 0, f v ∈ A ∙ b 0

variable {b}

theorem apply_b0 {f : V →ₗ[A] V} (hf : Pres b f) : f (b 0) = xc b f • b 0 := by
  have h := b.sum_repr (f (b 0))
  rw [Fin.sum_univ_two, repr_one_eq_zero_of_mem b (hf _ (Submodule.mem_span_singleton_self _)),
    zero_smul, add_zero] at h
  exact h.symm

theorem apply_b1 (f : V →ₗ[A] V) : f (b 1) = yc b f • b 0 + zc b f • b 1 := by
  have h := b.sum_repr (f (b 1))
  rw [Fin.sum_univ_two] at h
  exact h.symm

theorem repr_b0_one : b.repr (b 0) 1 = 0 := by
  rw [b.repr_self, Finsupp.single_apply, if_neg (by decide)]

theorem repr_b1_one : b.repr (b 1) 1 = 1 := by
  rw [b.repr_self, Finsupp.single_apply, if_pos rfl]

theorem apply_eq_xc_smul {f : V →ₗ[A] V} (hf : Pres b f) {w : V} (hw : w ∈ A ∙ b 0) :
    f w = xc b f • w := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, apply_b0 hf, smul_comm]

theorem sub_zc_smul_mem {f : V →ₗ[A] V} (hf : Pres b f) (v : V) :
    f v - zc b f • v ∈ A ∙ b 0 := by
  rw [mem_iff_repr_one_eq_zero]
  have h := b.sum_repr v
  rw [Fin.sum_univ_two] at h
  rw [← h]
  simp only [map_add, map_sub, map_smul, smul_add, Finsupp.add_apply, Finsupp.sub_apply,
    Finsupp.smul_apply, smul_eq_mul, apply_b0 hf, apply_b1 f, repr_b0_one, repr_b1_one]
  ring

theorem det_eq {f : V →ₗ[A] V} (hf : Pres b f) : LinearMap.det f = xc b f * zc b f := by
  classical
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply]
  rw [repr_one_eq_zero_of_mem b (hf _ (Submodule.mem_span_singleton_self _)), mul_zero, sub_zero]
  rfl

theorem zc_mul {f : V →ₗ[A] V} (hf : Pres b f) (g : V →ₗ[A] V) :
    zc b (f * g) = zc b f * zc b g := by
  show b.repr (f (g (b 1))) 1 = _
  rw [apply_b1 g, map_add, map_smul, map_smul, apply_b0 hf, apply_b1 f]
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, repr_b0_one,
    repr_b1_one]
  unfold zc
  rw [apply_b1 f]
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, repr_b0_one,
    repr_b1_one]
  ring

theorem zc_one : zc b (1 : V →ₗ[A] V) = 1 := by
  show b.repr (b 1) 1 = 1
  exact repr_b1_one

theorem zc_eq_of_sub_smul_mem {f : V →ₗ[A] V} {a : A} (h : ∀ v : V, f v - a • v ∈ A ∙ b 0) :
    zc b f = a := by
  have h1 := repr_one_eq_zero_of_mem b (h (b 1))
  rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, repr_b1_one, smul_eq_mul,
    mul_one, sub_eq_zero] at h1
  exact h1

theorem repr_mem_of_mem_smul_top {I : Ideal A} {w : V} (hw : w ∈ I • (⊤ : Submodule A V))
    (i : Fin 2) : b.repr w i ∈ I := by
  refine Submodule.smul_induction_on (p := fun w => b.repr w i ∈ I) hw ?_ ?_
  · intro r hr v _
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ hr
  · intro v w hv hw
    rw [map_add, Finsupp.add_apply]
    exact I.add_mem hv hw

theorem zc_sub_one_mem {f : V →ₗ[A] V} {I : Ideal A} (h : f (b 1) - b 1 ∈ I • (⊤ : Submodule A V)) :
    zc b f - 1 ∈ I := by
  have h1 := repr_mem_of_mem_smul_top (b := b) h 1
  rwa [map_sub, Finsupp.sub_apply, repr_b1_one] at h1

end P2mStrictOfLine

section Main

open P2mStrictOfLine IsLocalRing

theorem inertiaSubgroupIn_le_decompositionSubgroup (P : ValuationSubring (AlgebraicClosure ℚ)) :
    P.inertiaSubgroupIn ℚ ≤ P.decompositionSubgroup ℚ :=
  Subgroup.map_subtype_le _

theorem exists_pow_mul_inertia_fixing {p : ℕ} (hp : p.Prime)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    (φ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : P.IsFrobeniusAt φ p)
    (hσ : σ ∈ P.decompositionSubgroup ℚ)
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ F] :
    ∃ (n : ℕ) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      τ ∈ P.inertiaSubgroupIn ℚ ∧ (φ ^ n * τ)⁻¹ * σ ∈ F.fixingSubgroup :=
  ModularCurve.exists_frobeniusAt_pow_mul_inertia_fixing_of_mem_decompositionSubgroup p hp P hP
    φ hφ σ hσ F

theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (ρ : GaloisRepAdic A) {p : ℕ} (hp : p.Prime) (hdet : ρ.DetIsCyclotomic p)
    (a : A) (ha : a ^ 2 = 1)
    (hline : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∃ L : Submodule A ρ.V,
        (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
        (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
        (∀ τ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ τ v - v ∈ L) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
          ∀ v : ρ.V, ρ.ρ σ v - a • v ∈ L)) :
    ρ.IsStrictOrdinaryAt p := by
  refine ⟨hdet.1, fun P hP => ?_⟩
  obtain ⟨L, ⟨b, rfl⟩, hD, hI, hF⟩ := hline P hP
  refine ⟨A ∙ b 0, ⟨b, rfl⟩, hD, hI, fun σ hσ => ?_⟩

  have pres : ∀ g ∈ P.decompositionSubgroup ℚ, Pres b (ρ.ρ g) := fun g hg v hv => hD g hg v hv

  have zmul : ∀ g ∈ P.decompositionSubgroup ℚ, ∀ h ∈ P.decompositionSubgroup ℚ,
      zc b (ρ.ρ (g * h)) = zc b (ρ.ρ g) * zc b (ρ.ρ h) := by
    intro g hg h hh
    rw [map_mul]
    exact zc_mul (pres g hg) _

  obtain ⟨φ, hφ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hp P hP
  have hφD : φ ∈ P.decompositionSubgroup ℚ := hφ.mem_decompositionSubgroup
  have zφ : zc b (ρ.ρ φ) = a := zc_eq_of_sub_smul_mem (hF φ hφ)
  have zφpow : ∀ n : ℕ, zc b (ρ.ρ (φ ^ n)) = a ^ n := by
    intro n
    induction n with
    | zero => rw [pow_zero, pow_zero, map_one]; exact zc_one
    | succ n ih =>
      rw [pow_succ, zmul _ (Subgroup.pow_mem _ hφD n) _ hφD, ih, zφ, pow_succ]
  have zτ : ∀ τ ∈ P.inertiaSubgroupIn ℚ, zc b (ρ.ρ τ) = 1 := by
    intro τ hτ
    refine zc_eq_of_sub_smul_mem fun v => ?_
    rw [one_smul]
    exact hI τ hτ v

  set z : A := zc b (ρ.ρ σ) with hz
  have hzN : ∀ N : ℕ, z ^ 2 - 1 ∈ maximalIdeal A ^ N := by
    intro N
    obtain ⟨F, hFfd, hcont⟩ := ρ.isAdicContinuous N
    haveI : FiniteDimensional ℚ F := hFfd
    obtain ⟨n, τ, hτ, hν⟩ := exists_pow_mul_inertia_fixing hp P hP φ σ hφ hσ F
    set ν := (φ ^ n * τ)⁻¹ * σ with hνdef
    have hτD : τ ∈ P.decompositionSubgroup ℚ := inertiaSubgroupIn_le_decompositionSubgroup P hτ
    have hφnτD : φ ^ n * τ ∈ P.decompositionSubgroup ℚ :=
      Subgroup.mul_mem _ (Subgroup.pow_mem _ hφD n) hτD
    have hνD : ν ∈ P.decompositionSubgroup ℚ :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hφnτD) hσ
    have hσeq : σ = (φ ^ n * τ) * ν := by rw [hνdef, mul_inv_cancel_left]

    have hνfix : ∀ x ∈ F, ν x = x := (IntermediateField.mem_fixingSubgroup_iff _ _).mp hν
    have zν : zc b (ρ.ρ ν) - 1 ∈ maximalIdeal A ^ N := zc_sub_one_mem (hcont ν hνfix (b 1))

    have hzσ : z = a ^ n * zc b (ρ.ρ ν) := by
      rw [hz, hσeq, zmul _ hφnτD _ hνD, zmul _ (Subgroup.pow_mem _ hφD n) _ hτD, zφpow, zτ τ hτ,
        mul_one]
    obtain ⟨m, hm, hmeq⟩ : ∃ m ∈ maximalIdeal A ^ N, zc b (ρ.ρ ν) = 1 + m :=
      ⟨zc b (ρ.ρ ν) - 1, zν, by ring⟩
    have han : (a ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, ha, one_pow]
    have e1 : z ^ 2 - 1 = m * (2 + m) := by
      rw [hzσ, hmeq]; linear_combination (1 + m) ^ 2 * han
    rw [e1]
    exact Ideal.mul_mem_right _ _ hm
  have hz2 : z ^ 2 = 1 := by
    have hmem : z ^ 2 - 1 ∈ (⨅ i : ℕ, maximalIdeal A ^ i) := Submodule.mem_iInf _ |>.mpr hzN
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal A).ne_top,
      Ideal.mem_bot, sub_eq_zero] at hmem
    exact hmem

  refine ⟨xc b (ρ.ρ σ), z, fun w hw => apply_eq_xc_smul (pres σ hσ) hw,
    fun v => sub_zc_smul_mem (pres σ hσ) v, fun n c hμ => ?_⟩
  have hd := hdet.2 n σ c hμ
  rw [det_eq (pres σ hσ)] at hd
  have e2 : xc b (ρ.ρ σ) - (c : A) * z = z * (xc b (ρ.ρ σ) * z - (c : A)) := by
    linear_combination (-(xc b (ρ.ρ σ))) * hz2
  rw [e2]
  exact Ideal.mul_mem_left _ _ hd

end Main

end S_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine
end P2MW
export P2MW.S_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_ordinaryLine (solution)
