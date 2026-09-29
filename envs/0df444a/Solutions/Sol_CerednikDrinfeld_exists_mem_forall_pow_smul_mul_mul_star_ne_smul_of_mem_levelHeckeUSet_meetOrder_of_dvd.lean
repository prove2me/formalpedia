-- Prove2me | solution 1 for CerednikDrinfeld.exists_mem_forall_pow_smul_mul_mul_star_ne_smul_of_mem_levelHeckeUSet_meetOrder_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/a7e826c8-3ea9-5c8e-ab87-ed6621b1e026

import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_mem_forall_pow_smul_mul_mul_star_ne_smul_of_mem_levelHeckeUSet_meetOrder_of_dvd

set_option autoImplicit false
set_option maxHeartbeats 1600000

open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld
open scoped Quaternion TensorProduct NumberField

theorem solution
    {r rbar N : ℕ} [Fact r.Prime] [Fact rbar.Prime] [NeZero N]
    {a₁ b₁ : ℚ}
    (Λ₁ R₁ : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hΛ₁ : IsMaximalOrder Λ₁) (hR₁ : IsEichlerOrder R₁ N) (hRΛ₁ : R₁ ≤ Λ₁)
    (n₁ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn₁ : n₁ ∈ primeHeckeSet R₁ r)
    (hS₁ : IsEichlerOrder (meetOrder R₁ n₁) (N * r))
    (ℓ : HeckeTower.AwayPrime r rbar) (s : (ℍ[ℚ, a₁, b₁])ˣ)
    (sf : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hs :
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∉ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          (s : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : u.adicCompletion ℚ)) ∧
      (∀ u : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ u.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] u (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1) ∧
      Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * sf⁻¹ ∈
        (if (ℓ.1 : ℕ) ∣ N then levelHeckeUSet Λ₁ (meetOrder R₁ n₁) (ℓ.1 : ℕ)
          else primeHeckeSet (meetOrder R₁ n₁) (ℓ.1 : ℕ)) ∧
      nrd (s : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ))
    (hℓN : (ℓ.1 : ℕ) ∣ N) :
    ∃ z : ℍ[ℚ, a₁, b₁], z ∈ R₁ ∧ ∀ (c : ℕ) (y : ℍ[ℚ, a₁, b₁]), y ∈ Λ₁ →
      ((r ^ c : ℕ) : ℚ) • ((s : ℍ[ℚ, a₁, b₁]) * z * star (s : ℍ[ℚ, a₁, b₁])) ≠ ((ℓ.1 : ℕ) : ℚ) • y := by
  classical
  have hrp : r.Prime := Fact.out
  obtain ⟨hs1, hs2, hs3, hs4⟩ := hs
  rw [if_pos hℓN] at hs3

  have hU : ¬ meetOrder R₁ n₁ ≤ Submodule.conjByFiniteIdele Λ₁
      (Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
          (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
            (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) * sf⁻¹) := by
    simp only [levelHeckeUSet, Set.mem_setOf_eq] at hs3
    exact hs3.2.2
  by_contra H
  push_neg at H
  apply hU

  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    have hnu : ¬ IsUnit ((r : ℕ) : 𝓞 ℚ) := by
      intro hu
      have hu' := hu.map (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toRingHom
      rw [map_natCast] at hu'
      rcases Int.isUnit_iff.1 hu' with h1 | h1
      · exact hrp.one_lt.ne' (by exact_mod_cast h1)
      · have : (0 : ℤ) ≤ (r : ℕ) := Int.natCast_nonneg r
        omega
    have hI : Ideal.span {((r : ℕ) : 𝓞 ℚ)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top]; exact hnu
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal _ hI
    have hrM : ((r : ℕ) : 𝓞 ℚ) ∈ M := hIM (Ideal.mem_span_singleton_self _)
    refine ⟨⟨M, hM.isPrime, ?_⟩, hrM⟩
    intro hbot
    have : ((r : ℕ) : 𝓞 ℚ) = 0 := by simpa [hbot] using hrM
    exact hrp.ne_zero (by exact_mod_cast this)

  set D : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
    Submodule.finiteIdeleDiagonal ℍ[ℚ, a₁, b₁]
      (Units.map (algebraMap ℚ ℍ[ℚ, a₁, b₁]).toMonoidHom
        (Units.mk0 ((ℓ.1 : ℕ) : ℚ) (Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero))) with hD
  have hDval : (D : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
      algebraMap ℚ (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ((ℓ.1 : ℕ) : ℚ) := by
    rw [hD, Submodule.val_finiteIdeleDiagonal_apply, Algebra.TensorProduct.algebraMap_apply]
    rfl
  have hDcomm : ∀ x : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ,
      (D : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * x = x * D := by
    intro x; rw [hDval]; exact Algebra.commutes _ _
  intro z hz
  have hzR : z ∈ R₁ :=
    (Submodule.mem_inf.1 (show z ∈ R₁ ⊓ Submodule.conjByFiniteIdele R₁ n₁ from hz)).1
  obtain ⟨c, y, hy, hcy⟩ := H z hzR

  have hℓ0 : ((ℓ.1 : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr ℓ.1.prop.ne_zero
  have hstar : star (s : ℍ[ℚ, a₁, b₁]) = ((ℓ.1 : ℕ) : ℚ) • ((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) := by
    have h1 := QuaternionAlgebra.mul_star_eq_coe_nrd (s : ℍ[ℚ, a₁, b₁])
    rw [hs4] at h1
    calc star (s : ℍ[ℚ, a₁, b₁])
        = ((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * ((s : ℍ[ℚ, a₁, b₁]) * star (s : ℍ[ℚ, a₁, b₁])) := by
          rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = ((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) * ((((ℓ.1 : ℕ) : ℚ) : ℚ) : ℍ[ℚ, a₁, b₁]) := by rw [h1]
      _ = ((ℓ.1 : ℕ) : ℚ) • ((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) := by
          rw [QuaternionAlgebra.mul_coe_eq_smul]
  have hszs : ((r ^ c : ℕ) : ℚ) • ((s : ℍ[ℚ, a₁, b₁]) * z * ((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) = y := by
    rw [hstar, mul_smul_comm, smul_comm] at hcy
    exact smul_right_injective _ hℓ0 hcy

  have haway : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      ((s : ℍ[ℚ, a₁, b₁]) * z * ((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁])) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈
        Submodule.localBox Λ₁ w :=
    (QuaternionAlgebra.IsOrder.forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem Λ₁ hΛ₁.isOrder r v hv _).2
      ⟨c, by rw [hszs]; exact hy⟩

  rw [Submodule.mem_conjByFiniteIdele_iff, AddSubgroup.mem_map]
  refine ⟨(sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) *
      ((sf⁻¹ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ), ?_, ?_⟩
  ·
    rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hΛ₁.isOrder.fg hΛ₁.isOrder.spanTop]
    intro w
    have hinvw : Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] w
          ((sf⁻¹ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) *
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] w (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hz1 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] w (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) =
        z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
      rw [Submodule.finiteAdeleEvalAt_tmul]; rfl
    rw [map_mul, map_mul, hz1]
    by_cases hw : ((r : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    ·
      have h1 := hs2 w hw
      rw [h1, mul_one] at hinvw
      rw [h1, hinvw, one_mul, mul_one]
      exact AddSubgroup.subset_closure ⟨z, hRΛ₁ hzR, 1, Subring.one_mem _, rfl⟩
    ·
      have h1 := hs1 w hw
      have hinv' : Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] w
          ((sf⁻¹ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
          ((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
        rw [h1] at hinvw
        have h2 : ((s : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) *
            (((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = 1 := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, Units.mul_inv, mul_one]; rfl
        calc _ = Submodule.finiteAdeleEvalAt ℍ[ℚ, a₁, b₁] w
              ((sf⁻¹ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) *
              (((s : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) *
                (((s⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ))) := by rw [h2, mul_one]
          _ = _ := by rw [← mul_assoc, hinvw, one_mul]
      rw [h1, hinv', Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_one]
      have hwv : w ≠ v := fun h => hw (h ▸ hv)
      exact haway w hwv
  ·
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight,
      Units.val_mul, mul_inv_rev, inv_inv]

    have e1 : ((sf⁻¹ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) *
        (sf : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := Units.inv_mul _
    have e2 : ((D⁻¹ : (ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) *
        (D : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1 := Units.inv_mul _
    calc (D : ℍ[ℚ, a₁, b₁] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) * ↑sf⁻¹ * (↑sf * z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * ↑sf⁻¹) * (↑sf * ↑D⁻¹)
        = ↑D * (↑sf⁻¹ * ↑sf) * z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * (↑sf⁻¹ * ↑sf) * ↑D⁻¹ := by
          simp only [mul_assoc]
      _ = ↑D * z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * ↑D⁻¹ := by rw [e1, mul_one, mul_one]
      _ = z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * ↑D * ↑D⁻¹ := by rw [hDcomm]
      _ = z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) := by rw [mul_assoc, Units.mul_inv, mul_one]

end S_CerednikDrinfeld_exists_mem_forall_pow_smul_mul_mul_star_ne_smul_of_mem_levelHeckeUSet_meetOrder_of_dvd
end P2MW
export P2MW.S_CerednikDrinfeld_exists_mem_forall_pow_smul_mul_mul_star_ne_smul_of_mem_levelHeckeUSet_meetOrder_of_dvd (solution)
