-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/6021012b-1f57-5525-a3c9-38fdf1e15e15

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace S5

local notation "Kv" v => IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v
local notation "Ov" v => IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v

variable {a b : ℚ}

theorem tmul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    {c : Kv w} (hc : c ∈ Ov w) : z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ w :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem mul_neg' (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) : x * (-y) = -(x * y) :=
  eq_neg_of_add_eq_zero_left (by rw [← mul_add, neg_add_cancel, mul_zero])

theorem neg_mul' (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) : (-x) * y = -(x * y) :=
  eq_neg_of_add_eq_zero_left (by rw [← add_mul, neg_add_cancel, zero_mul])

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)} (hx : x ∈ Submodule.localBox Λ w) (hy : y ∈ Submodule.localBox Λ w) :
    x * y ∈ Submodule.localBox Λ w := by

  refine AddSubgroup.closure_induction (p := fun y _ => x * y ∈ Submodule.localBox Λ w) ?_ ?_ ?_ ?_ hy
  · rintro y ⟨z', hz', c', hc', rfl⟩
    refine AddSubgroup.closure_induction (p := fun x _ => x * (z' ⊗ₜ[ℚ] c') ∈ Submodule.localBox Λ w) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨z, hz, c, hc, rfl⟩
      beta_reduce
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox (hΛ.mul_mem hz hz') w (mul_mem hc hc')
    · beta_reduce; rw [zero_mul]; exact zero_mem _
    · intro x₁ x₂ _ _ h₁ h₂; beta_reduce; rw [add_mul]; exact add_mem h₁ h₂
    · intro x₁ _ h₁; beta_reduce; rw [neg_mul' w]; exact neg_mem h₁
  · beta_reduce; rw [mul_zero]; exact zero_mem _
  · intro y₁ y₂ _ _ h₁ h₂; beta_reduce; rw [mul_add]; exact add_mem h₁ h₂
  · intro y₁ _ h₁; beta_reduce; rw [mul_neg' w]; exact neg_mem h₁

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) ∈ Submodule.localBox Λ w :=
  tmul_mem_localBox hΛ.one_mem w (one_mem _)

def localBoxUnitsSubgroup {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] (Kv w))ˣ where
  carrier := Submodule.localBoxUnits Λ w
  one_mem' := ⟨by rw [Units.val_one]; exact one_mem_localBox hΛ w,
    by rw [inv_one, Units.val_one]; exact one_mem_localBox hΛ w⟩
  mul_mem' := fun {u u'} hu hu' =>
    ⟨by rw [Units.val_mul]; exact localBox_mul_mem hΛ w hu.1 hu'.1,
     by rw [mul_inv_rev, Units.val_mul]; exact localBox_mul_mem hΛ w hu'.2 hu.2⟩
  inv_mem' := fun {u} hu => ⟨hu.2, by rw [inv_inv]; exact hu.1⟩

theorem closure_localBoxUnits_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (w : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup.closure (Submodule.localBoxUnits Λ w) = localBoxUnitsSubgroup hΛ w :=
  Subgroup.closure_eq (localBoxUnitsSubgroup hΛ w)

theorem mem_closure_localBoxUnits_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (w : HeightOneSpectrum (𝓞 ℚ)) (u : (ℍ[ℚ, a, b] ⊗[ℚ] (Kv w))ˣ) :
    u ∈ Subgroup.closure (Submodule.localBoxUnits Λ w) ↔
      (u : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) ∈ Submodule.localBox Λ w ∧
        ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] (Kv w))ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] (Kv w)) ∈ Submodule.localBox Λ w := by
  rw [closure_localBoxUnits_eq hΛ w]
  exact Iff.rfl

theorem coe_toLoc (w : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b])ˣ) :
    ((CerednikDrinfeld.CosetGraph.toLoc w x : (CerednikDrinfeld.CosetGraph.Loc a b w)ˣ) :
      CerednikDrinfeld.CosetGraph.Loc a b w) = (x : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv w) := rfl

theorem coe_toLoc_inv (w : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b])ˣ) :
    (((CerednikDrinfeld.CosetGraph.toLoc w x)⁻¹ : (CerednikDrinfeld.CosetGraph.Loc a b w)ˣ) :
      CerednikDrinfeld.CosetGraph.Loc a b w) = ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : Kv w) := by
  rw [← map_inv]; rfl

theorem main (R₀ R' : Submodule ℤ ℍ[ℚ, a, b]) (hR₀ : QuaternionAlgebra.IsOrder R₀) (hR' : QuaternionAlgebra.IsOrder R')
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hloc : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.localBox R' w = Submodule.localBox R₀ w) :
    (∀ x : (ℍ[ℚ, a, b])ˣ,
        x ∈ CerednikDrinfeld.CosetGraph.awayUnits R' v ↔
          ∃ K K' : ℕ, ((r ^ K : ℕ) : ℚ) • ((x : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R₀ ∧
            ((r ^ K' : ℕ) : ℚ) • ((x⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ R₀) ∧
    (∀ y : ↥R', ∃ K : ℕ, ((r ^ K : ℕ) : ℚ) • (y : ℍ[ℚ, a, b]) ∈ R₀) := by
  have LGM := fun y => QuaternionAlgebra.IsOrder.forall_tmul_one_mem_localBox_iff_exists_pow_smul_mem R₀ hR₀ r v hv y
  refine ⟨fun x => ?_, fun y => ?_⟩
  · simp only [CerednikDrinfeld.CosetGraph.awayUnits, Subgroup.mem_iInf, Subgroup.mem_comap,
      mem_closure_localBoxUnits_iff hR', coe_toLoc, coe_toLoc_inv]
    constructor
    · intro h
      obtain ⟨K, hK⟩ := (LGM _).1 fun w hw => by rw [← hloc w hw]; exact (h w hw).1
      obtain ⟨K', hK'⟩ := (LGM _).1 fun w hw => by rw [← hloc w hw]; exact (h w hw).2
      exact ⟨K, K', hK, hK'⟩
    · rintro ⟨K, K', hK, hK'⟩ w hw
      rw [hloc w hw]
      exact ⟨(LGM _).2 ⟨K, hK⟩ w hw, (LGM _).2 ⟨K', hK'⟩ w hw⟩
  · exact (LGM _).1 fun w hw => by rw [← hloc w hw]; exact tmul_mem_localBox y.2 w (one_mem _)

end S5

end

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    {a₁ b₁ : ℚ} (R₀ R' : Submodule ℤ ℍ[ℚ, a₁, b₁]) (hR₀ : IsOrder R₀) (hR' : IsOrder R')
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hloc : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.localBox R' w = Submodule.localBox R₀ w) :
    (∀ x : (ℍ[ℚ, a₁, b₁])ˣ,
        x ∈ CerednikDrinfeld.CosetGraph.awayUnits R' v ↔
          ∃ K K' : ℕ, ((r ^ K : ℕ) : ℚ) • ((x : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₀ ∧
            ((r ^ K' : ℕ) : ℚ) • ((x⁻¹ : (ℍ[ℚ, a₁, b₁])ˣ) : ℍ[ℚ, a₁, b₁]) ∈ R₀) ∧
    (∀ y : ↥R', ∃ K : ℕ, ((r ^ K : ℕ) : ℚ) • (y : ℍ[ℚ, a₁, b₁]) ∈ R₀) := by
  exact S5.main R₀ R' hR₀ hR' r v hv hloc

end S_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_mem_awayUnits_iff_exists_pow_smul_mem_of_forall_localBox_eq (solution)
