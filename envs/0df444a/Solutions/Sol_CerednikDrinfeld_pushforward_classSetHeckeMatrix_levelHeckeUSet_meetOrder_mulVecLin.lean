-- Prove2me | solution 1 for CerednikDrinfeld.pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/61a97c4c-914c-50cc-95dd-d8e94a5ef9dc

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_Order_FiniteIdele
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet
import Theorems.Thm_CerednikDrinfeld_mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer
import Theorems.Thm_CerednikDrinfeld_mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq
import Theorems.Thm_CerednikDrinfeld_conj_mem_levelHeckeUSet_iff_of_mem_primeHeckeSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace Nat
p2m_export "Nat" "prime_iff card_eq_fintype_card cast_ite count cast_smul_eq_nsmul cast_sum Coprime choose Prime prime_iff_prime_int any isCoprime_iff_coprime eq_zero_or_pos cast_zero castRingHom card_congr zero cast_one"
p2m_open "Nat"

noncomputable def placesOf (ℓ : ℕ) : Finset (HeightOneSpectrum (𝓞 ℚ)) :=
  if h : (Ideal.span {(ℓ : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) = ⊥ then ∅ else (Ideal.finite_factors h).toFinset

theorem span_natCast_ne_bot {ℓ : ℕ} (hℓ : ℓ ≠ 0) : (Ideal.span {(ℓ : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot]
  exact_mod_cast hℓ

theorem mem_placesOf_iff {ℓ : ℕ} (hℓ : ℓ ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    v ∈ placesOf ℓ ↔ (ℓ : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [placesOf, dif_neg (span_natCast_ne_bot hℓ), Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    Ideal.dvd_span_singleton]

theorem inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ placesOf ℓ) :
    algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ := by
  rw [mem_placesOf_iff hℓ] at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers,
    show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) = v.valuation ℚ ((ℓ : ℚ)⁻¹) from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _, map_inv₀]
  have h1 : v.valuation ℚ (ℓ : ℚ) = 1 := by
    have : (ℓ : ℚ) = algebraMap (𝓞 ℚ) ℚ (ℓ : 𝓞 ℚ) := by simp
    rw [this, HeightOneSpectrum.valuation_of_algebraMap]
    have hle := v.intValuation_le_one (ℓ : 𝓞 ℚ)
    have hnlt : ¬ v.intValuation (ℓ : 𝓞 ℚ) < 1 := by
      rw [HeightOneSpectrum.intValuation_lt_one_iff_mem]
      exact hv
    exact le_antisymm hle (not_lt.mp hnlt)
  rw [h1, inv_one]

theorem disjoint_placesOf_of_coprime {ℓ ℓ' : ℕ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) (h : ℓ.Coprime ℓ') :
    Disjoint (placesOf ℓ) (placesOf ℓ') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_placesOf_iff hℓ] at hv
  rw [mem_placesOf_iff hℓ'] at hv'
  have hcop : IsCoprime (ℓ : 𝓞 ℚ) (ℓ' : 𝓞 ℚ) := by
    have := (Nat.isCoprime_iff_coprime.mpr h : IsCoprime (ℓ : ℤ) (ℓ' : ℤ))
    simpa using this.map (Int.castRingHom (𝓞 ℚ))
  obtain ⟨x, y, hxy⟩ := hcop
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hxy]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hv) (Ideal.mul_mem_left _ _ hv')

theorem not_mem_placesOf_of_mem_placesOf_of_coprime {ℓ ℓ' : ℕ} (hℓ : ℓ ≠ 0) (hℓ' : ℓ' ≠ 0) (h : ℓ.Coprime ℓ')
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ placesOf ℓ) : v ∉ placesOf ℓ' :=
  Finset.disjoint_left.mp (disjoint_placesOf_of_coprime hℓ hℓ' h) hv

theorem isMaximal_span_natCast_of_prime {p : ℕ} (hp : p.Prime) :
    (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsMaximal := by
  have e : 𝓞 ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hpZ : _root_.Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpO : _root_.Prime (p : 𝓞 ℚ) := by
    have : (p : 𝓞 ℚ) = e.symm (p : ℤ) := by rw [map_natCast]
    rw [this]
    exact (MulEquiv.prime_iff (e.symm : ℤ ≃* 𝓞 ℚ)).mpr hpZ
  have hprime : (Ideal.span {(p : 𝓞 ℚ)} : Ideal (𝓞 ℚ)).IsPrime := (Ideal.span_singleton_prime hpO.ne_zero).mpr hpO
  exact hprime.isMaximal (span_natCast_ne_bot hp.ne_zero)

theorem HeightOneSpectrum.eq_of_natCast_prime_mem {p : ℕ} (hp : p.Prime) {v v' : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) (hv' : (p : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' := by
  have hmax := isMaximal_span_natCast_of_prime hp
  have h1 : v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv)).symm
  have h2 : v'.asIdeal = Ideal.span {(p : 𝓞 ℚ)} :=
    (hmax.eq_of_le v'.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).mpr hv')).symm
  exact HeightOneSpectrum.ext (h1.trans h2.symm)

end Nat

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace HeckeLocal

variable {a b : ℚ}

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ𝔸 :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem box_eq_span (Λ : Submodule ℤ ℍ[ℚ, a, b]) :
    Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
  rw [Submodule.span_int_eq_addSubgroupClosure]; rfl

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  rw [box_eq_span]; rfl

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x y : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, fun v => ?_, ?_⟩
      · have e : (c' * c) v = c' v * c v := rfl
        rw [e]
        exact mul_mem (hc' v) (hc v)
      · rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) :
    (1 : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun v => ?_, ?_⟩
  · have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
    rw [e]; exact one_mem _
  · rfl

theorem coe_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  have h := (Submodule.mem_finiteIdeleStabilizer_iff Λ u).mp hu

  have h1 : (u : ℍ𝔸) * 1 ∈ u • ((Submodule.finiteAdeleBox Λ : AddSubgroup ℍ𝔸) : Set ℍ𝔸) :=
    Set.smul_mem_smul_set (one_mem_box hΛ)
  rw [h, mul_one] at h1
  exact h1

theorem coe_inv_mem_box_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  coe_mem_box_of_mem_stabilizer hΛ (inv_mem hu)

theorem mul_mem_primeHeckeSet_of_mem_stabilizer {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    u * h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ hub h1
  · rw [mul_inv_rev, Units.val_mul, ← smul_mul_assoc]
    exact box_mul_mem hΛ h2 huib
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (((u * h)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (u : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem hub
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((ℓ : ℚ)⁻¹ • ((u * h : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
      rw [mul_smul_comm, Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]; exact box_mul_mem hΛ huib hmem

theorem mul_mem_primeHeckeSet_of_mem_stabilizer' {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (ℓ : ℕ) {u h : (ℍ𝔸)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    h * u ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  obtain ⟨h1, h2, h3, h4⟩ := hh
  have hub := coe_mem_box_of_mem_stabilizer hΛ hu
  have huib := coe_inv_mem_box_of_mem_stabilizer hΛ hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hΛ h1 hub
  · rw [mul_inv_rev, Units.val_mul, ← mul_smul_comm]
    exact box_mul_mem hΛ huib h2
  · intro hmem
    apply h3
    have : ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (u : ℍ𝔸) * (((h * u)⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [mul_inv_rev, Units.val_mul, ← mul_assoc, Units.mul_inv, one_mul]
    rw [this]; exact box_mul_mem hΛ hub hmem
  · intro hmem
    apply h4
    have : (ℓ : ℚ)⁻¹ • (h : ℍ𝔸) = ((ℓ : ℚ)⁻¹ • ((h * u : (ℍ𝔸)ˣ) : ℍ𝔸)) * ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := by
      rw [smul_mul_assoc, Units.val_mul, mul_assoc, Units.mul_inv, mul_one]
    rw [this]; exact box_mul_mem hΛ hmem huib

theorem box_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') :
    Submodule.finiteAdeleBox Λ ≤ Submodule.finiteAdeleBox Λ' := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mem_stabilizer_of_coe_mem_of_coe_inv_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {u : (ℍ𝔸)ˣ} (hu : (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) (hui : ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact box_mul_mem hΛ hu hx
  · intro x hx
    refine ⟨(u⁻¹ : (ℍ𝔸)ˣ) • x, box_mul_mem hΛ hui hx, ?_⟩
    show (u : ℍ𝔸) * (((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x) = x
    rw [← mul_assoc, Units.mul_inv, one_mul]

theorem stabilizer_mono {S R : Submodule ℤ ℍ[ℚ, a, b]} (hS : QuaternionAlgebra.IsOrder S) (hR : QuaternionAlgebra.IsOrder R)
    (h : S ≤ R) : Submodule.finiteIdeleStabilizer S ≤ Submodule.finiteIdeleStabilizer R := by
  intro u hu
  exact mem_stabilizer_of_coe_mem_of_coe_inv_mem hR (box_mono h (coe_mem_box_of_mem_stabilizer hS hu))
    (box_mono h (coe_inv_mem_box_of_mem_stabilizer hS hu))

theorem mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  ⟨fun hu => ⟨coe_mem_box_of_mem_stabilizer hΛ hu, coe_inv_mem_box_of_mem_stabilizer hΛ hu⟩,
   fun h => mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ h.1 h.2⟩

def localBoxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) (v : HeightOneSpectrum (𝓞 ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : v.adicCompletion ℚ, c ∈ v.adicCompletionIntegers ℚ ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_localBox_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {v : HeightOneSpectrum (𝓞 ℚ)} {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} :
    x ∈ Submodule.localBox Λ v ↔ x ∈ Submodule.span ℤ (localBoxGen Λ v) := by
  have : Submodule.localBox Λ v = (Submodule.span ℤ (localBoxGen Λ v)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

theorem finiteAdeleEvalAt_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {x : ℍ𝔸} (hx : x ∈ Submodule.finiteAdeleBox Λ) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v x ∈ Submodule.localBox Λ v := by
  rw [mem_box_iff] at hx
  rw [mem_localBox_iff_span]
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c v, hc v, ?_⟩
    simp [Submodule.finiteAdeleEvalAt, Submodule.finiteAdeleEvalAlgHom_apply]
  | zero => rw [map_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [map_zsmul]; exact Submodule.smul_mem _ _ h₁

theorem tmul_one_mul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c * c', mul_mem hc hc', ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet {Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (ℓ : ℕ) {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hℓv : algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ) :
    Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h ∈ Submodule.localBoxUnits Λ v := by
  obtain ⟨h1, h2, -, h4⟩ := hh
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓpos
  · exfalso; apply h4
    rw [Nat.cast_zero, inv_zero, zero_smul]; exact zero_mem _
  have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓpos.ne'
  rw [Submodule.mem_localBoxUnits_iff]
  refine ⟨finiteAdeleEvalAt_mem_localBox v h1, ?_⟩

  set f := Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v with hf
  have e1 : (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)
      = f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) := Units.coe_map_inv _ _
  have e2 : f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) * f ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
    rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hℓ0, one_smul]
  show (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ _
  rw [e1, e2]
  exact tmul_one_mul_mem_localBox v hℓv (finiteAdeleEvalAt_mem_localBox v h2)

theorem localBox_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  unfold Submodule.localBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem mul_tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) :
    x * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx ⊢
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hx'
    refine Submodule.subset_span ⟨z, hz, c' * c, mul_mem hc' hc, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  | zero => rw [zero_mul]; exact zero_mem _
  | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
  | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁

theorem localBox_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span] at hx hy ⊢
  induction hy using Submodule.span_induction with
  | mem y hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      refine Submodule.subset_span ⟨z' * z, hΛ.mul_mem hz' hz, c' * c, mul_mem hc' hc, ?_⟩
      rw [Algebra.TensorProduct.tmul_mul_tmul]
    | zero => rw [zero_mul]; exact zero_mem _
    | add x₁ x₂ _ _ h₁ h₂ => rw [add_mul]; exact add_mem h₁ h₂
    | smul m x₁ _ h₁ => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h₁
  | zero => rw [mul_zero]; exact zero_mem _
  | add y₁ y₂ _ _ h₁ h₂ => rw [mul_add]; exact add_mem h₁ h₂
  | smul m y₁ _ h₁ => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h₁

theorem one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨1, hΛ.one_mem, 1, one_mem _, rfl⟩

theorem tmul_one_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) ∈ Submodule.localBox Λ v := by
  rw [mem_localBox_iff_span]
  exact Submodule.subset_span ⟨z, hz, 1, one_mem _, rfl⟩

end HeckeLocal

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace GOODEQ

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" v => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v

theorem mem_conjByFiniteIdele_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (ℍ𝔸)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ := by
  show z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ (Submodule.finiteAdeleBox Λ).map _ ↔ _
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨u, hu, h⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight] at h
    have : ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : ℍ𝔸) = u := by
      rw [← h, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact hu
  · intro h
    refine ⟨_, h, ?_⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    show (g : ℍ𝔸) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : ℍ𝔸)) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = _
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem tmul_one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨z, hz, 1, fun v => ?_, rfl⟩
  have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
  rw [e]; exact one_mem _

theorem natCast_smul_mem_meetOrder {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) {q : ℕ}
    {n : (ℍ𝔸)ˣ} (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q) {z : ℍ[ℚ, a, b]} (hz : z ∈ R) :
    (q : ℤ) • z ∈ CerednikDrinfeld.meetOrder R n := by
  refine ⟨Submodule.smul_mem _ _ hz, ?_⟩
  show (q : ℤ) • z ∈ Submodule.conjByFiniteIdele R n
  rw [mem_conjByFiniteIdele_iff]
  have e : ((q : ℤ) • z) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = (q : ℚ) • (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    rw [natCast_zsmul, Nat.cast_smul_eq_nsmul]
    exact (TensorProduct.smul_tmul' (q : ℕ) z (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)).symm
  rw [e, mul_smul_comm, ← smul_mul_assoc]
  exact HeckeLocal.box_mul_mem hR (HeckeLocal.box_mul_mem hR hn.2.1 (tmul_one_mem_box hz)) hn.1

theorem localBox_meetOrder_eq {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) {q : ℕ}
    {n : (ℍ𝔸)ˣ} (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q) (v : HeightOneSpectrum (𝓞 ℚ))
    (hqv : algebraMap ℚ (v.adicCompletion ℚ) ((q : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ) :
    Submodule.localBox (CerednikDrinfeld.meetOrder R n) v = Submodule.localBox R v := by
  apply le_antisymm (HeckeLocal.localBox_mono inf_le_left v)
  unfold Submodule.localBox
  rw [AddSubgroup.closure_le]
  rintro _ ⟨z, hz, c, hc, rfl⟩
  have hq0 : (q : ℚ) ≠ 0 := by
    rintro h
    have : q = 0 := by exact_mod_cast h
    subst this
    exact hn.2.2.2 (by rw [Nat.cast_zero, inv_zero, zero_smul]; exact zero_mem _)

  have e : z ⊗ₜ[ℚ] c = ((q : ℤ) • z) ⊗ₜ[ℚ] (algebraMap ℚ (v.adicCompletion ℚ) ((q : ℚ)⁻¹) * c) := by
    rw [natCast_zsmul, ← Nat.cast_smul_eq_nsmul ℚ, TensorProduct.smul_tmul, Algebra.smul_def, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hq0, map_one, one_mul]
  rw [e]
  exact AddSubgroup.subset_closure ⟨_, natCast_smul_mem_meetOrder hR hn hz, _, mul_mem hqv hc, rfl⟩

def IsSupportedOn (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (β : (ℍ𝔸)ˣ) : Prop :=
  ∀ v ∉ S, (ev v) (β : ℍ𝔸) = 1

theorem IsSupportedOn.inv {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {β : (ℍ𝔸)ˣ} (h : IsSupportedOn S β) :
    IsSupportedOn S β⁻¹ := fun v hv => by
  have e : (ev v) ((β⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (ev v) (β : ℍ𝔸) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  rw [h v hv, mul_one] at e
  exact e

theorem IsSupportedOn.mul {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {β γ : (ℍ𝔸)ˣ} (hβ : IsSupportedOn S β)
    (hγ : IsSupportedOn S γ) : IsSupportedOn S (β * γ) := fun v hv => by
  rw [Units.val_mul, map_mul, hβ v hv, hγ v hv, mul_one]

theorem IsSupportedOn.conj {S : Finset (HeightOneSpectrum (𝓞 ℚ))} {β : (ℍ𝔸)ˣ} (hβ : IsSupportedOn S β) (n : (ℍ𝔸)ˣ) :
    IsSupportedOn S (n⁻¹ * β * n) := fun v hv => by
  rw [Units.val_mul, Units.val_mul, map_mul, map_mul, hβ v hv, mul_one, ← map_mul, Units.inv_mul, map_one]

theorem ev_smul (v : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : ℍ𝔸) : (ev v) (c • x) = c • (ev v) x := map_smul _ _ _

theorem smul_mem_localBox {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ)) {c : ℚ}
    (hc : algebraMap ℚ (v.adicCompletion ℚ) c ∈ v.adicCompletionIntegers ℚ)
    {x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v) : c • x ∈ Submodule.localBox Λ v := by
  have e : c • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) c) * x := by
    have e1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) c) = c • (1 : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    rw [e1, smul_mul_assoc, one_mul]
  rw [e]
  exact HeckeLocal.tmul_one_mul_mem_localBox v hc hx

theorem mem_box_iff_of_isSupportedOn {X Y : Submodule ℤ ℍ[ℚ, a, b]} (hX : QuaternionAlgebra.IsOrder X)
    (hY : QuaternionAlgebra.IsOrder Y) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hXY : ∀ v ∈ S, Submodule.localBox X v = Submodule.localBox Y v)
    {β : (ℍ𝔸)ˣ} (hβ : IsSupportedOn S β) (c : ℚ)
    (hc : ∀ v ∉ S, algebraMap ℚ (v.adicCompletion ℚ) c ∈ v.adicCompletionIntegers ℚ) :
    c • (β : ℍ𝔸) ∈ Submodule.finiteAdeleBox X ↔ c • (β : ℍ𝔸) ∈ Submodule.finiteAdeleBox Y := by
  rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox X hX.fg hX.spanTop,
    Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Y hY.fg hY.spanTop]
  refine forall_congr' fun v => ?_
  by_cases hv : v ∈ S
  · rw [hXY v hv]
  · rw [ev_smul, hβ v hv]
    exact ⟨fun _ => smul_mem_localBox v (hc v hv) (HeckeLocal.one_mem_localBox hY v),
      fun _ => smul_mem_localBox v (hc v hv) (HeckeLocal.one_mem_localBox hX v)⟩

theorem mem_primeHeckeSet_iff_of_isSupportedOn {X Y : Submodule ℤ ℍ[ℚ, a, b]} (hX : QuaternionAlgebra.IsOrder X)
    (hY : QuaternionAlgebra.IsOrder Y) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    (hXY : ∀ v ∈ Nat.placesOf ℓ, Submodule.localBox X v = Submodule.localBox Y v)
    {β : (ℍ𝔸)ˣ} (hβ : IsSupportedOn (Nat.placesOf ℓ) β) :
    β ∈ QuaternionAlgebra.primeHeckeSet X ℓ ↔ β ∈ QuaternionAlgebra.primeHeckeSet Y ℓ := by
  have h1 : ∀ v ∉ Nat.placesOf ℓ, algebraMap ℚ (v.adicCompletion ℚ) (1 : ℚ) ∈ v.adicCompletionIntegers ℚ :=
    fun v _ => by rw [map_one]; exact one_mem _
  have hℓi : ∀ v ∉ Nat.placesOf ℓ, algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ v.adicCompletionIntegers ℚ :=
    fun v hv => Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hℓ hv
  have hℓ' : ∀ v ∉ Nat.placesOf ℓ, algebraMap ℚ (v.adicCompletion ℚ) (ℓ : ℚ) ∈ v.adicCompletionIntegers ℚ :=
    fun v _ => by rw [map_natCast]; exact natCast_mem _ ℓ
  have A := mem_box_iff_of_isSupportedOn hX hY _ hXY hβ 1 h1
  have B := mem_box_iff_of_isSupportedOn hX hY _ hXY hβ.inv (ℓ : ℚ) hℓ'
  have C := mem_box_iff_of_isSupportedOn hX hY _ hXY hβ.inv 1 h1
  have D := mem_box_iff_of_isSupportedOn hX hY _ hXY hβ ((ℓ : ℚ)⁻¹) hℓi
  simp only [one_smul] at A C
  simp only [QuaternionAlgebra.primeHeckeSet, Set.mem_setOf_eq]
  rw [A, B, C, D]

theorem mem_finiteIdeleStabilizer_iff_of_isSupportedOn {X Y : Submodule ℤ ℍ[ℚ, a, b]} (hX : QuaternionAlgebra.IsOrder X)
    (hY : QuaternionAlgebra.IsOrder Y) (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hXY : ∀ v ∈ S, Submodule.localBox X v = Submodule.localBox Y v)
    {u : (ℍ𝔸)ˣ} (hu : IsSupportedOn S u) :
    u ∈ Submodule.finiteIdeleStabilizer X ↔ u ∈ Submodule.finiteIdeleStabilizer Y := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits X hX,
    QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Y hY]
  refine forall_congr' fun v => ?_
  by_cases hv : v ∈ S
  · simp only [Submodule.mem_localBoxUnits_iff, hXY v hv]
  · have e : Units.map (ev v).toRingHom.toMonoidHom u = 1 := Units.ext (hu v hv)
    rw [e]
    simp only [Submodule.mem_localBoxUnits_iff, Units.val_one, inv_one]
    exact ⟨fun _ => ⟨HeckeLocal.one_mem_localBox hY v, HeckeLocal.one_mem_localBox hY v⟩,
      fun _ => ⟨HeckeLocal.one_mem_localBox hX v, HeckeLocal.one_mem_localBox hX v⟩⟩

theorem mem_box_conjByFiniteIdele_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (n : (ℍ𝔸)ˣ) (x : ℍ𝔸) :
    x ∈ Submodule.finiteAdeleBox (Submodule.conjByFiniteIdele R n) ↔
      ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (n : ℍ𝔸) ∈ Submodule.finiteAdeleBox R := by
  rw [Submodule.finiteAdeleBox_conjByFiniteIdele R hR.fg hR.spanTop n, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    have : ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n : ℍ𝔸) * y * ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * (n : ℍ𝔸) = y := by
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    show (n : ℍ𝔸) * (((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * (n : ℍ𝔸)) * ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = x
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem mem_finiteIdeleStabilizer_conjByFiniteIdele_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (n : (ℍ𝔸)ˣ) (hRn : QuaternionAlgebra.IsOrder (Submodule.conjByFiniteIdele R n)) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer (Submodule.conjByFiniteIdele R n) ↔
      n⁻¹ * u * n ∈ Submodule.finiteIdeleStabilizer R := by
  rw [HeckeLocal.mem_stabilizer_iff hRn, HeckeLocal.mem_stabilizer_iff hR, mem_box_conjByFiniteIdele_iff hR,
    mem_box_conjByFiniteIdele_iff hR]
  simp only [Units.val_mul, mul_inv_rev, inv_inv, mul_assoc]

theorem conj_mem_localBox_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (v : HeightOneSpectrum (𝓞 ℚ))
    {m : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hm : m ∈ Submodule.localBoxUnits R v)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * x * m ∈ Submodule.localBox R v ↔
      x ∈ Submodule.localBox R v := by
  rw [Submodule.mem_localBoxUnits_iff] at hm
  constructor
  · intro h
    have := HeckeLocal.localBox_mul_mem hR v (HeckeLocal.localBox_mul_mem hR v hm.1 h) hm.2
    rwa [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one] at this
  · intro h
    exact HeckeLocal.localBox_mul_mem hR v (HeckeLocal.localBox_mul_mem hR v hm.2 h) hm.1

theorem unitsMap_mem_localBoxUnits_of_mem_primeHeckeSet {R : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} (hq : q ≠ 0) {n : (ℍ𝔸)ˣ}
    (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ Nat.placesOf q) :
    Units.map (ev v).toRingHom.toMonoidHom n ∈ Submodule.localBoxUnits R v :=
  HeckeLocal.map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet q hn v
    (Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hq hv)

theorem smul_conj_mem_box_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) {q : ℕ} (hq : q ≠ 0)
    {n : (ℍ𝔸)ˣ} (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : Disjoint S (Nat.placesOf q))
    {β : (ℍ𝔸)ˣ} (hβ : IsSupportedOn S β) (c : ℚ) :
    c • (((n⁻¹ * β * n : (ℍ𝔸)ˣ)) : ℍ𝔸) ∈ Submodule.finiteAdeleBox R ↔ c • (β : ℍ𝔸) ∈ Submodule.finiteAdeleBox R := by
  rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox R hR.fg hR.spanTop,
    Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox R hR.fg hR.spanTop]
  refine forall_congr' fun v => ?_
  by_cases hv : v ∈ Nat.placesOf q
  ·
    have hvS : v ∉ S := fun h => Finset.disjoint_left.mp hS h hv
    rw [ev_smul, ev_smul, Units.val_mul, Units.val_mul, map_mul, map_mul, hβ v hvS, mul_one, ← map_mul, Units.inv_mul,
      map_one]
  ·
    have hu := unitsMap_mem_localBoxUnits_of_mem_primeHeckeSet hq hn hv
    rw [ev_smul, ev_smul, Units.val_mul, Units.val_mul, map_mul, map_mul, ← smul_mul_assoc, ← mul_smul_comm]
    have e1 : (ev v) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
        (((Units.map (ev v).toRingHom.toMonoidHom n)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := (Units.coe_map_inv _ _).symm
    have e2 : (ev v) (n : ℍ𝔸) = ((Units.map (ev v).toRingHom.toMonoidHom n : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
          ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) := rfl
    rw [e1, e2]
    exact conj_mem_localBox_iff hR v hu _

theorem conj_mem_primeHeckeSet_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) {q ℓ : ℕ} (hq : q ≠ 0)
    (hℓ : ℓ ≠ 0) (hcop : ℓ.Coprime q) {n : (ℍ𝔸)ˣ} (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    {β : (ℍ𝔸)ˣ} (hβ : IsSupportedOn (Nat.placesOf ℓ) β) :
    n⁻¹ * β * n ∈ QuaternionAlgebra.primeHeckeSet R ℓ ↔ β ∈ QuaternionAlgebra.primeHeckeSet R ℓ := by
  have hS := Nat.disjoint_placesOf_of_coprime hℓ hq hcop
  have A := smul_conj_mem_box_iff hR hq hn _ hS hβ 1
  have B := smul_conj_mem_box_iff hR hq hn _ hS hβ.inv (ℓ : ℚ)
  have C := smul_conj_mem_box_iff hR hq hn _ hS hβ.inv 1
  have D := smul_conj_mem_box_iff hR hq hn _ hS hβ ((ℓ : ℚ)⁻¹)
  simp only [one_smul] at A C
  have einv : (n⁻¹ * β * n)⁻¹ = n⁻¹ * β⁻¹ * n := by rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
  simp only [QuaternionAlgebra.primeHeckeSet, Set.mem_setOf_eq, einv]
  rw [A, B, C, D]

theorem conj_mem_localBoxUnits_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) (v : HeightOneSpectrum (𝓞 ℚ))
    {m : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hm : m ∈ Submodule.localBoxUnits R v)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    m⁻¹ * x * m ∈ Submodule.localBoxUnits R v ↔ x ∈ Submodule.localBoxUnits R v := by
  have hm2 := hm
  rw [Submodule.mem_localBoxUnits_iff] at hm2
  simp only [Submodule.mem_localBoxUnits_iff, SetLike.mem_coe, mul_inv_rev, inv_inv, Units.val_mul, ← mul_assoc]
  rw [conj_mem_localBox_iff hR v hm]

  have e2 : ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) *
      ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) * m ∈ Submodule.localBox R v ↔
      ((x⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox R v :=
    conj_mem_localBox_iff hR v hm _
  rw [e2]

theorem conj_mem_finiteIdeleStabilizer_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) {q : ℕ} (hq : q ≠ 0)
    {n : (ℍ𝔸)ˣ} (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : Disjoint S (Nat.placesOf q)) {w : (ℍ𝔸)ˣ} (hw : IsSupportedOn S w) :
    n⁻¹ * w * n ∈ Submodule.finiteIdeleStabilizer R ↔ w ∈ Submodule.finiteIdeleStabilizer R := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits R hR,
    QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits R hR]
  refine forall_congr' fun v => ?_
  rw [map_mul, map_mul, map_inv]
  by_cases hv : v ∈ Nat.placesOf q
  · have hvS : v ∉ S := fun h => Finset.disjoint_left.mp hS h hv
    have e : Units.map (ev v).toRingHom.toMonoidHom w = 1 := Units.ext (hw v hvS)
    rw [e, mul_one, inv_mul_cancel]
  · exact conj_mem_localBoxUnits_iff hR v (unitsMap_mem_localBoxUnits_of_mem_primeHeckeSet hq hn hv) _

theorem one_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (1 : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBoxUnits Λ v := by
  rw [Submodule.mem_localBoxUnits_iff]
  exact ⟨HeckeLocal.one_mem_localBox hΛ v, by simpa using HeckeLocal.one_mem_localBox hΛ v⟩

theorem exists_isSupportedOn_mul_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {ℓ : ℕ} (hℓ : ℓ ≠ 0) {h : (ℍ𝔸)ˣ} (hh : h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ) :
    ∃ β u : (ℍ𝔸)ˣ, u ∈ Submodule.finiteIdeleStabilizer Λ ∧ h = β * u ∧ IsSupportedOn (Nat.placesOf ℓ) β := by
  obtain ⟨β, h1, h2⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) (Nat.placesOf ℓ)
    (fun v => Units.map (ev v).toRingHom.toMonoidHom h)
  refine ⟨β, β⁻¹ * h, ?_, by rw [mul_inv_cancel_left], h2⟩
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ]
  intro v
  rw [map_mul, map_inv]
  by_cases hv : v ∈ Nat.placesOf ℓ
  · have : Units.map (ev v).toRingHom.toMonoidHom β = Units.map (ev v).toRingHom.toMonoidHom h := Units.ext (h1 v hv)
    rw [this, inv_mul_cancel]
    exact one_mem_localBoxUnits hΛ v
  · have : Units.map (ev v).toRingHom.toMonoidHom β = 1 := Units.ext (h2 v hv)
    rw [this, inv_one, one_mul]
    exact HeckeLocal.map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet ℓ hh v
      (Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hℓ hv)

theorem exists_rep {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {ℓ : ℕ} (hℓ : ℓ ≠ 0) :
    ∃ r : ((ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) → (ℍ𝔸)ˣ,
      ∀ c, (∃ h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ, (h : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c) →
        r c ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ ∧ (r c : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c ∧
          IsSupportedOn (Nat.placesOf ℓ) (r c) := by
  classical
  have key : ∀ c : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ,
      (∃ h ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ, (h : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c) →
      ∃ β : (ℍ𝔸)ˣ, β ∈ QuaternionAlgebra.primeHeckeSet Λ ℓ ∧ (β : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c ∧
        IsSupportedOn (Nat.placesOf ℓ) β := by
    rintro c ⟨h, hhT, rfl⟩
    obtain ⟨β, u, hu, rfl, hβ⟩ := exists_isSupportedOn_mul_eq hΛ hℓ hhT
    refine ⟨β, ?_, (QuotientGroup.mk_mul_of_mem β hu).symm, hβ⟩
    have := HeckeLocal.mul_mem_primeHeckeSet_of_mem_stabilizer' hΛ ℓ (inv_mem hu) hhT
    rwa [mul_inv_cancel_right] at this
  refine ⟨fun c => if hc : _ then (key c hc).choose else 1, fun c hc => ?_⟩
  simp only [dif_pos hc]
  exact (key c hc).choose_spec

end GOODEQ

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace GOODEQ

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem sum_ite_mul_card_filter {ι E V : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (CS : Finset ι) (g : ι → E) (f : E → V) (v : V) :
    ∑ e, (if f e = v then (1 : ℤ) else 0) * ((CS.filter fun c => g c = e).card : ℤ) =
      ((CS.filter fun c => f (g c) = v).card : ℤ) := by
  classical
  simp_rw [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single (g c)]
  · simp
  · intro e _ hne
    rw [if_neg (Ne.symm hne), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

section Generic

variable (US UR : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)

theorem natCard_heckeIncidence_eq_card_filter [DecidableEq (QuaternionAlgebra.ClassSet US)]
    (S : Set (ℍ𝔸)ˣ) (CS : Finset ((ℍ𝔸)ˣ ⧸ US))
    (hCS : ∀ c, c ∈ CS ↔ ∃ h ∈ S, (h : (ℍ𝔸)ˣ ⧸ US) = c)
    (r : ((ℍ𝔸)ˣ ⧸ US) → (ℍ𝔸)ˣ) (hr : ∀ c ∈ CS, r c ∈ S ∧ (r c : (ℍ𝔸)ˣ ⧸ US) = c)
    (x : (ℍ𝔸)ˣ) (y : QuaternionAlgebra.ClassSet US) :
    Nat.card (QuaternionAlgebra.HeckeIncidence US S x y) =
      (CS.filter fun c => QuaternionAlgebra.ClassSet.mk US (x * r c) = y).card := by
  classical
  have hiff : ∀ c : (ℍ𝔸)ˣ ⧸ US, (∃ h ∈ S, (h : (ℍ𝔸)ˣ ⧸ US) = c ∧ QuaternionAlgebra.ClassSet.mk US (x * h) = y) ↔
      c ∈ CS.filter fun c => QuaternionAlgebra.ClassSet.mk US (x * r c) = y := by
    intro c
    rw [Finset.mem_filter, hCS]
    constructor
    · rintro ⟨h, hS, hc, hy⟩
      refine ⟨⟨h, hS, hc⟩, ?_⟩
      obtain ⟨-, hrc⟩ := hr c ((hCS c).mpr ⟨h, hS, hc⟩)
      have hu : h⁻¹ * r c ∈ US := QuotientGroup.eq.mp (hc.trans hrc.symm)
      have : r c = h * (h⁻¹ * r c) := by rw [mul_inv_cancel_left]
      rw [this, ← mul_assoc, QuaternionAlgebra.ClassSet.mk_mul_of_mem _ _ hu, hy]
    · rintro ⟨hc, hy⟩
      obtain ⟨hS, hrc⟩ := hr c ((hCS c).mpr hc)
      exact ⟨r c, hS, hrc, hy⟩
  unfold QuaternionAlgebra.HeckeIncidence
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff), Nat.card_eq_fintype_card, Fintype.card_coe]

variable [Fintype (QuaternionAlgebra.ClassSet US)] [Fintype (QuaternionAlgebra.ClassSet UR)]
  [DecidableEq (QuaternionAlgebra.ClassSet US)] [DecidableEq (QuaternionAlgebra.ClassSet UR)]

theorem pushforward_classSetHeckeMatrix_mulVec
    (TS TR : Set (ℍ𝔸)ˣ) (hTS : ∀ u ∈ US, ∀ s ∈ TS, u * s ∈ TS) (hTR : ∀ u ∈ UR, ∀ s ∈ TR, u * s ∈ TR)
    (CS : Finset ((ℍ𝔸)ˣ ⧸ US)) (CR : Finset ((ℍ𝔸)ˣ ⧸ UR))
    (hCS : ∀ c, c ∈ CS ↔ ∃ h ∈ TS, (h : (ℍ𝔸)ˣ ⧸ US) = c) (hCR : ∀ c, c ∈ CR ↔ ∃ h ∈ TR, (h : (ℍ𝔸)ˣ ⧸ UR) = c)
    (r : ((ℍ𝔸)ˣ ⧸ US) → (ℍ𝔸)ˣ) (hr : ∀ c ∈ CS, r c ∈ TS ∧ (r c : (ℍ𝔸)ˣ ⧸ US) = c)
    (m : (ℍ𝔸)ˣ) (hm : ∀ x y : (ℍ𝔸)ˣ, QuaternionAlgebra.ClassSet.mk US x = QuaternionAlgebra.ClassSet.mk US y →
      QuaternionAlgebra.ClassSet.mk UR (x * m) = QuaternionAlgebra.ClassSet.mk UR (y * m))
    (τ : (ℍ𝔸)ˣ → (ℍ𝔸)ˣ) (hτm : ∀ c ∈ CS, r c * m = m * τ (r c)) (hτT : ∀ c ∈ CS, τ (r c) ∈ TR)
    (hτbij : ∀ c' ∈ CR, ∃! c, c ∈ CS ∧ (τ (r c) : (ℍ𝔸)ˣ ⧸ UR) = c')
    (x : QuaternionAlgebra.ClassSet US → ℤ) (v : QuaternionAlgebra.ClassSet UR) :
    CerednikDrinfeld.pushforward (fun e : QuaternionAlgebra.ClassSet US => QuaternionAlgebra.ClassSet.mk UR (e.out * m))
        ((CerednikDrinfeld.classSetHeckeMatrix US TS).mulVecLin x) v =
      (CerednikDrinfeld.classSetHeckeMatrix UR TR).mulVecLin
        (CerednikDrinfeld.pushforward (fun e : QuaternionAlgebra.ClassSet US => QuaternionAlgebra.ClassSet.mk UR (e.out * m)) x) v := by
  classical

  have hfmk : ∀ z : (ℍ𝔸)ˣ, (fun e : QuaternionAlgebra.ClassSet US => QuaternionAlgebra.ClassSet.mk UR (e.out * m))
      (QuaternionAlgebra.ClassSet.mk US z) = QuaternionAlgebra.ClassSet.mk UR (z * m) := by
    intro z
    apply hm
    exact Quotient.out_eq _

  choose σ hσ hσu using hτbij
  let r' : ((ℍ𝔸)ˣ ⧸ UR) → (ℍ𝔸)ˣ := fun c' => if hc' : c' ∈ CR then τ (r (σ c' hc')) else 1
  have hr' : ∀ c' ∈ CR, r' c' ∈ TR ∧ ((r' c' : (ℍ𝔸)ˣ ⧸ UR)) = c' := fun c' hc' => by
    simp only [r', dif_pos hc']
    exact ⟨hτT _ (hσ c' hc').1, (hσ c' hc').2⟩

  have key : ∀ e' : QuaternionAlgebra.ClassSet US,
      ∑ e, (if (fun e : QuaternionAlgebra.ClassSet US => QuaternionAlgebra.ClassSet.mk UR (e.out * m)) e = v then (1 : ℤ) else 0) *
          CerednikDrinfeld.classSetHeckeMatrix US TS e e' =
        CerednikDrinfeld.classSetHeckeMatrix UR TR v
          ((fun e : QuaternionAlgebra.ClassSet US => QuaternionAlgebra.ClassSet.mk UR (e.out * m)) e') := by
    intro e'
    have hL : ∀ e, CerednikDrinfeld.classSetHeckeMatrix US TS e e' =
        ((CS.filter fun c => QuaternionAlgebra.ClassSet.mk US (e'.out * r c) = e).card : ℤ) := by
      intro e
      rw [CerednikDrinfeld.classSetHeckeMatrix, Matrix.of_apply, QuaternionAlgebra.heckeKernel,
        natCard_heckeIncidence_eq_card_filter US TS CS hCS r hr]
    simp_rw [hL]
    rw [sum_ite_mul_card_filter]
    simp_rw [hfmk]

    have hR : CerednikDrinfeld.classSetHeckeMatrix UR TR v (QuaternionAlgebra.ClassSet.mk UR (e'.out * m)) =
        ((CR.filter fun c' => QuaternionAlgebra.ClassSet.mk UR (e'.out * m * r' c') = v).card : ℤ) := by
      rw [CerednikDrinfeld.classSetHeckeMatrix, Matrix.of_apply, QuaternionAlgebra.heckeKernel_mk UR TR hTR,
        natCard_heckeIncidence_eq_card_filter UR TR CR hCR r' hr']
    rw [hR]
    congr 1

    refine (Finset.card_bij (fun c' hc' => σ c' (Finset.mem_filter.mp hc').1) ?_ ?_ ?_).symm
    · intro c' hc'
      obtain ⟨hc', hv⟩ := Finset.mem_filter.mp hc'
      refine Finset.mem_filter.mpr ⟨(hσ c' hc').1, ?_⟩
      rw [mul_assoc, hτm _ (hσ c' hc').1, ← mul_assoc]
      simp only [r', dif_pos hc'] at hv
      exact hv
    · intro c₁ hc₁ c₂ hc₂ h
      obtain ⟨hc₁', -⟩ := Finset.mem_filter.mp hc₁
      obtain ⟨hc₂', -⟩ := Finset.mem_filter.mp hc₂
      have e1 := (hσ c₁ hc₁').2
      have e2 := (hσ c₂ hc₂').2

      have h' : σ c₁ hc₁' = σ c₂ hc₂' := h
      rw [← e1, ← e2, h']
    · intro c hc
      obtain ⟨hc, hv⟩ := Finset.mem_filter.mp hc
      have hc' : ((τ (r c) : (ℍ𝔸)ˣ ⧸ UR)) ∈ CR := (hCR _).mpr ⟨τ (r c), hτT c hc, rfl⟩
      have hσc : σ _ hc' = c := (hσu _ hc' c ⟨hc, rfl⟩).symm
      refine ⟨_, Finset.mem_filter.mpr ⟨hc', ?_⟩, hσc⟩
      simp only [r', dif_pos hc']
      rw [hσc, mul_assoc, ← hτm c hc, ← mul_assoc]
      exact hv

  simp only [CerednikDrinfeld.pushforward, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, CerednikDrinfeld.degeneracyMatrix,
    Matrix.of_apply]

  calc ∑ e, (if QuaternionAlgebra.ClassSet.mk UR (e.out * m) = v then (1 : ℤ) else 0) *
          ∑ e', CerednikDrinfeld.classSetHeckeMatrix US TS e e' * x e'
      = ∑ e', (∑ e, (if QuaternionAlgebra.ClassSet.mk UR (e.out * m) = v then (1 : ℤ) else 0) *
          CerednikDrinfeld.classSetHeckeMatrix US TS e e') * x e' := by
        simp_rw [Finset.mul_sum, ← mul_assoc]
        rw [Finset.sum_comm]
        simp_rw [Finset.sum_mul]
    _ = ∑ e', CerednikDrinfeld.classSetHeckeMatrix UR TR v (QuaternionAlgebra.ClassSet.mk UR (e'.out * m)) * x e' := by
        refine Finset.sum_congr rfl fun e' _ => ?_
        rw [key e']
    _ = ∑ v', CerednikDrinfeld.classSetHeckeMatrix UR TR v v' *
          ∑ e', (if QuaternionAlgebra.ClassSet.mk UR (e'.out * m) = v' then (1 : ℤ) else 0) * x e' := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun e' _ => ?_
        rw [Finset.sum_eq_single (QuaternionAlgebra.ClassSet.mk UR (e'.out * m))]
        · simp
        · intro v' _ hne
          rw [if_neg (Ne.symm hne), zero_mul, mul_zero]
        · intro h; exact absurd (Finset.mem_univ _) h

end Generic

end GOODEQ

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace GOODEQ

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" v => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v

section Frame

variable {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) {q ℓ : ℕ} (hq : q ≠ 0) (hℓ : ℓ ≠ 0)
  (hcop : ℓ.Coprime q) {n : (ℍ𝔸)ˣ} (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)

include hR in
theorem isOrder_meetOrder (n : (ℍ𝔸)ˣ) : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n) :=
  QuaternionAlgebra.IsOrder.inf hR (QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n)

end Frame

theorem localBox_meetOrder_eq_of_mem_placesOf {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R) {q ℓ : ℕ}
    (hq : q ≠ 0) (hℓ : ℓ ≠ 0) (hcop : ℓ.Coprime q) {n : (ℍ𝔸)ˣ} (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∈ Nat.placesOf ℓ) :
    Submodule.localBox (CerednikDrinfeld.meetOrder R n) v = Submodule.localBox R v :=
  localBox_meetOrder_eq hR hn v (Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hq
    (Nat.not_mem_placesOf_of_mem_placesOf_of_coprime hℓ hq hcop hv))

section Frame

variable {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)

include hR in

theorem stab_meetOrder_le (n : (ℍ𝔸)ˣ) :
    Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R :=
  HeckeLocal.stabilizer_mono (isOrder_meetOrder hR n) hR inf_le_left

include hR in

theorem conj_mem_stab_of_mem_stab_meetOrder (n : (ℍ𝔸)ˣ) {u : (ℍ𝔸)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) :
    n⁻¹ * u * n ∈ Submodule.finiteIdeleStabilizer R := by
  have hRn := QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n
  have := HeckeLocal.stabilizer_mono (isOrder_meetOrder hR n) hRn inf_le_right hu
  exact (mem_finiteIdeleStabilizer_conjByFiniteIdele_iff hR n hRn u).mp this

include hR in

theorem mk_mul_eq_of_mk_eq (n m : (ℍ𝔸)ˣ) (hm : m = 1 ∨ m = n) (x y : (ℍ𝔸)ˣ)
    (h : QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) x =
      QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) y) :
    QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (x * m) =
      QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (y * m) := by
  obtain ⟨δ, hδ, u, hu, rfl⟩ := (DoubleCoset.eq _ _ _ _).mp h
  obtain ⟨δ', rfl⟩ := MonoidHom.mem_range.mp hδ
  rw [mul_assoc, mul_assoc, QuaternionAlgebra.ClassSet.mk_diagonal_mul]

  have : x * (u * m) = x * m * (m⁻¹ * u * m) := by group
  rw [this]
  refine (QuaternionAlgebra.ClassSet.mk_mul_of_mem _ _ ?_).symm
  rcases hm with hm1 | hmn
  · rw [hm1, inv_one, one_mul, mul_one]; exact stab_meetOrder_le hR n hu
  · rw [hmn]; exact conj_mem_stab_of_mem_stab_meetOrder hR n hu

end Frame

section Transport

theorem exists_rep' {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {ℓ : ℕ} (hℓ : ℓ ≠ 0)
    {T : Set (ℍ𝔸)ˣ} (hT : T ⊆ QuaternionAlgebra.primeHeckeSet Λ ℓ)
    (hTr : ∀ u ∈ Submodule.finiteIdeleStabilizer Λ, ∀ s ∈ T, s * u ∈ T) :
    ∃ r : ((ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) → (ℍ𝔸)ˣ,
      ∀ c, (∃ h ∈ T, (h : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c) →
        r c ∈ T ∧ (r c : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c ∧ IsSupportedOn (Nat.placesOf ℓ) (r c) := by
  classical
  have key : ∀ c : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ, (∃ h ∈ T, (h : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c) →
      ∃ β : (ℍ𝔸)ˣ, β ∈ T ∧ (β : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = c ∧ IsSupportedOn (Nat.placesOf ℓ) β := by
    rintro c ⟨h, hhT, rfl⟩
    obtain ⟨β, u, hu, rfl, hβ⟩ := exists_isSupportedOn_mul_eq hΛ hℓ (hT hhT)
    refine ⟨β, ?_, (QuotientGroup.mk_mul_of_mem β hu).symm, hβ⟩
    have := hTr u⁻¹ (inv_mem hu) _ hhT
    rwa [mul_inv_cancel_right] at this
  refine ⟨fun c => if hc : _ then (key c hc).choose else 1, fun c hc => ?_⟩
  simp only [dif_pos hc]
  exact (key c hc).choose_spec

theorem pushforward_of_transport (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : QuaternionAlgebra.IsOrder R) (q ℓ : ℕ)
    (hq : q ≠ 0) (hℓ : ℓ ≠ 0) (hcop : ℓ.Coprime q) (n : (ℍ𝔸)ˣ) (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)))]
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R))]
    (TS TR : Set (ℍ𝔸)ˣ) (hTSsub : TS ⊆ QuaternionAlgebra.primeHeckeSet (CerednikDrinfeld.meetOrder R n) ℓ)
    (hTRsub : TR ⊆ QuaternionAlgebra.primeHeckeSet R ℓ)
    (hTSl : ∀ u ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n), ∀ s ∈ TS, u * s ∈ TS) (hTSr : ∀ u ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n), ∀ s ∈ TS, s * u ∈ TS)
    (hTRl : ∀ u ∈ Submodule.finiteIdeleStabilizer R, ∀ s ∈ TR, u * s ∈ TR) (hTRr : ∀ u ∈ Submodule.finiteIdeleStabilizer R, ∀ s ∈ TR, s * u ∈ TR)
    (htrans : ∀ β, IsSupportedOn (Nat.placesOf ℓ) β → (β ∈ TS ↔ β ∈ TR))
    (hconj : ∀ β, IsSupportedOn (Nat.placesOf ℓ) β → (n⁻¹ * β * n ∈ TR ↔ β ∈ TR))
    (m : (ℍ𝔸)ˣ) (τ : (ℍ𝔸)ˣ → (ℍ𝔸)ˣ) (hmτ : (m = 1 ∧ τ = id) ∨ (m = n ∧ τ = fun h => n⁻¹ * h * n))
    (x : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) → ℤ) (v : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R)) :
    CerednikDrinfeld.pushforward
        (fun e : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) => QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m))
        ((CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) TS).mulVecLin x) v =
      (CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer R) TR).mulVecLin
        (CerednikDrinfeld.pushforward
          (fun e : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) => QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m)) x) v := by
  classical
  have hS := isOrder_meetOrder hR n
  have hRn := QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n
  have hloc : ∀ w ∈ Nat.placesOf ℓ, Submodule.localBox (CerednikDrinfeld.meetOrder R n) w = Submodule.localBox R w :=
    fun w hw => localBox_meetOrder_eq_of_mem_placesOf hR hq hℓ hcop hn hw
  have hdisj : Disjoint (Nat.placesOf ℓ) (Nat.placesOf q) := Nat.disjoint_placesOf_of_coprime hℓ hq hcop

  have hfinS := QuaternionAlgebra.IsOrder.finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet hS ℓ TS hTSsub
  have hfinR := QuaternionAlgebra.IsOrder.finite_setOf_exists_mem_quotientMk_eq_of_subset_primeHeckeSet hR ℓ TR hTRsub
  have hCS : ∀ c, c ∈ hfinS.toFinset ↔ ∃ h ∈ TS, (h : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) = c :=
    fun c => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hCR : ∀ c, c ∈ hfinR.toFinset ↔ ∃ h ∈ TR, (h : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer R) = c :=
    fun c => by rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq]

  obtain ⟨r, hr⟩ := exists_rep' hS hℓ hTSsub hTSr
  have hr1 : ∀ c ∈ hfinS.toFinset, r c ∈ TS ∧ (r c : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) = c := fun c hc =>
    ⟨(hr c ((hCS c).mp hc)).1, (hr c ((hCS c).mp hc)).2.1⟩
  have hrsupp : ∀ c ∈ hfinS.toFinset, IsSupportedOn (Nat.placesOf ℓ) (r c) := fun c hc => (hr c ((hCS c).mp hc)).2.2

  have hτsupp : ∀ h, IsSupportedOn (Nat.placesOf ℓ) h → IsSupportedOn (Nat.placesOf ℓ) (τ h) := by
    rcases hmτ with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact fun h hh => hh
    · exact fun h hh => hh.conj n
  have hτmem : ∀ h, IsSupportedOn (Nat.placesOf ℓ) h → (τ h ∈ TR ↔ h ∈ TS) := by
    intro h hh
    rw [htrans h hh]
    rcases hmτ with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Iff.rfl
    · exact hconj h hh
  have hτunit : ∀ w, IsSupportedOn (Nat.placesOf ℓ) w → (τ w ∈ Submodule.finiteIdeleStabilizer R ↔ w ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) := by
    intro w hw
    rw [mem_finiteIdeleStabilizer_iff_of_isSupportedOn hS hR _ hloc hw]
    rcases hmτ with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Iff.rfl
    · exact conj_mem_finiteIdeleStabilizer_iff hR hq hn _ hdisj hw
  have hτmul : ∀ g h : (ℍ𝔸)ˣ, τ (g * h) = τ g * τ h := by
    rcases hmτ with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · intro g h; rfl
    · intro g h; group
  have hτinv : ∀ g : (ℍ𝔸)ˣ, τ g⁻¹ = (τ g)⁻¹ := by
    rcases hmτ with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · intro g; rfl
    · intro g; group
  have hτm : ∀ h : (ℍ𝔸)ˣ, h * m = m * τ h := by
    rcases hmτ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro h; simp
    · intro h; group

  obtain ⟨σ, hστ, hτσ, hσsupp⟩ : ∃ σ : (ℍ𝔸)ˣ → (ℍ𝔸)ˣ, (∀ h, σ (τ h) = h) ∧ (∀ h, τ (σ h) = h) ∧
      ∀ h, IsSupportedOn (Nat.placesOf ℓ) h → IsSupportedOn (Nat.placesOf ℓ) (σ h) := by
    rcases hmτ with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact ⟨id, fun _ => rfl, fun _ => rfl, fun _ hh => hh⟩
    · refine ⟨fun h => n * h * n⁻¹, fun h => by group, fun h => by group, fun h hh => ?_⟩
      have := hh.conj n⁻¹
      rwa [inv_inv] at this

  refine pushforward_classSetHeckeMatrix_mulVec (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) (Submodule.finiteIdeleStabilizer R) TS TR hTSl hTRl
    hfinS.toFinset hfinR.toFinset hCS hCR r hr1 m (mk_mul_eq_of_mk_eq hR n m (hmτ.imp And.left And.left))
    τ (fun c _ => hτm (r c)) (fun c hc => (hτmem _ (hrsupp c hc)).mpr (hr1 c hc).1) ?_ x v

  intro c' hc'
  obtain ⟨h', hh', rfl⟩ := (hCR c').mp hc'

  obtain ⟨β', u', hu', rfl, hβ'⟩ := exists_isSupportedOn_mul_eq hR hℓ (hTRsub hh')
  have hβ'T : β' ∈ TR := by
    have := hTRr u'⁻¹ (inv_mem hu') _ hh'
    rwa [mul_inv_cancel_right] at this

  have hσβ : σ β' ∈ TS := by rw [← hτmem _ (hσsupp _ hβ'), hτσ]; exact hβ'T
  set c : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n) := (σ β' : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) with hcdef
  have hc : c ∈ hfinS.toFinset := (hCS c).mpr ⟨σ β', hσβ, rfl⟩
  refine ⟨c, ⟨hc, ?_⟩, ?_⟩
  ·
    rw [QuotientGroup.mk_mul_of_mem _ hu']

    have hw : (σ β')⁻¹ * r c ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n) := QuotientGroup.eq.mp ((hr1 c hc).2.symm ▸ rfl)
    have hwsupp : IsSupportedOn (Nat.placesOf ℓ) ((σ β')⁻¹ * r c) := (hσsupp _ hβ').inv.mul (hrsupp c hc)
    rw [eq_comm, QuotientGroup.eq]

    have : β'⁻¹ * τ (r c) = τ ((σ β')⁻¹ * r c) := by rw [hτmul, hτinv, hτσ]
    rw [this]
    exact (hτunit _ hwsupp).mpr hw
  ·
    rintro c₂ ⟨hc₂, hc₂eq⟩
    rw [QuotientGroup.mk_mul_of_mem _ hu'] at hc₂eq

    have h1 : (τ (r c))⁻¹ * τ (r c₂) ∈ Submodule.finiteIdeleStabilizer R := by
      apply QuotientGroup.eq.mp
      rw [hc₂eq]

      have hw : (σ β')⁻¹ * r c ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n) := QuotientGroup.eq.mp ((hr1 c hc).2.symm ▸ rfl)
      have hwsupp : IsSupportedOn (Nat.placesOf ℓ) ((σ β')⁻¹ * r c) := (hσsupp _ hβ').inv.mul (hrsupp c hc)
      rw [QuotientGroup.eq]
      have : (τ (r c))⁻¹ * β' = (τ ((σ β')⁻¹ * r c))⁻¹ := by rw [hτmul, hτinv, hτσ, mul_inv_rev, inv_inv]
      rw [this]
      exact inv_mem ((hτunit _ hwsupp).mpr hw)
    have h2 : (r c)⁻¹ * r c₂ ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n) := by
      rw [← hτunit _ ((hrsupp c hc).inv.mul (hrsupp c₂ hc₂)), hτmul, hτinv]
      exact h1

    have : (r c₂ : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) = (r c : (ℍ𝔸)ˣ ⧸ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) := (QuotientGroup.eq.mpr h2).symm
    rw [← (hr1 c₂ hc₂).2, ← (hr1 c hc).2, this]

end Transport

end GOODEQ

namespace GOODEQ

variable {a b : ℚ}

local notation "ℍ𝔸2" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

theorem pushforward_levelHeckeUSet (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (hR : QuaternionAlgebra.IsOrder R) (hRΛ : R ≤ Λ) (q ℓ : ℕ)
    (hq : q ≠ 0) (hℓ : ℓ ≠ 0) (hcop : ℓ.Coprime q) (n : (ℍ𝔸2)ˣ) (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)))]
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R))]
    (m : (ℍ𝔸2)ˣ) (τ : (ℍ𝔸2)ˣ → (ℍ𝔸2)ˣ) (hmτ : (m = 1 ∧ τ = id) ∨ (m = n ∧ τ = fun h => n⁻¹ * h * n))
    (x : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) → ℤ) (v : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R)) :
    CerednikDrinfeld.pushforward
        (fun e : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) => QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m))
        ((CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n))
          (CerednikDrinfeld.levelHeckeUSet Λ (CerednikDrinfeld.meetOrder R n) ℓ)).mulVecLin x) v =
      (CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer R) (CerednikDrinfeld.levelHeckeUSet Λ R ℓ)).mulVecLin
        (CerednikDrinfeld.pushforward
          (fun e : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) => QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m)) x) v := by
  have hS := isOrder_meetOrder hR n
  have hSΛ : CerednikDrinfeld.meetOrder R n ≤ Λ := inf_le_left.trans hRΛ
  have hloc : ∀ w ∈ Nat.placesOf ℓ, Submodule.localBox (CerednikDrinfeld.meetOrder R n) w = Submodule.localBox R w :=
    fun w hw => localBox_meetOrder_eq_of_mem_placesOf hR hq hℓ hcop hn hw

  have hloc' : ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal →
      Submodule.localBox (CerednikDrinfeld.meetOrder R n) v = Submodule.localBox R v :=
    fun v hv => hloc v ((Nat.mem_placesOf_iff hℓ v).mpr hv)
  have hsupp' : ∀ {β : (ℍ𝔸2)ˣ}, IsSupportedOn (Nat.placesOf ℓ) β →
      ∀ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∉ v.asIdeal →
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (β : ℍ𝔸2) = 1 :=
    fun hβ v hv => hβ v (fun h => hv ((Nat.mem_placesOf_iff hℓ v).mp h))
  exact pushforward_of_transport R hR q ℓ hq hℓ hcop n hn _ _ (fun h hh => hh.1) (fun h hh => hh.1)
    (fun u hu s hs => (CerednikDrinfeld.mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer
      Λ _ hΛ hS hSΛ ℓ hu hs).1)
    (fun u hu s hs => (CerednikDrinfeld.mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer
      Λ _ hΛ hS hSΛ ℓ hu hs).2)
    (fun u hu s hs => (CerednikDrinfeld.mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer
      Λ _ hΛ hR hRΛ ℓ hu hs).1)
    (fun u hu s hs => (CerednikDrinfeld.mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer
      Λ _ hΛ hR hRΛ ℓ hu hs).2)
    (fun β hβ => CerednikDrinfeld.mem_levelHeckeUSet_iff_mem_levelHeckeUSet_of_forall_localBox_eq hΛ hS hR inf_le_left hRΛ hℓ
      hloc' (hsupp' hβ))
    (fun β hβ => CerednikDrinfeld.conj_mem_levelHeckeUSet_iff_of_mem_primeHeckeSet hΛ hR hRΛ hq hℓ hcop hn (hsupp' hβ))
    m τ hmτ x v

end GOODEQ

open scoped TensorProduct Quaternion in
open IsDedekindDomain NumberField in

theorem solution
    {a b : ℚ} (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ) (hR : QuaternionAlgebra.IsOrder R)
    (hRΛ : R ≤ Λ) (q ℓ : ℕ)
    (hq : q ≠ 0) (hℓ : ℓ ≠ 0) (hcop : ℓ.Coprime q) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)))]
    [Fintype (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)))]
    [DecidableEq (QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R))]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (τ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ → (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hmτ : (m = 1 ∧ τ = id) ∨ (m = n ∧ τ = fun h => n⁻¹ * h * n))
    (x : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) → ℤ) (v : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer R)) :
    CerednikDrinfeld.pushforward
        (fun e : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) => QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m))
        ((CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n))
          (CerednikDrinfeld.levelHeckeUSet Λ (CerednikDrinfeld.meetOrder R n) ℓ)).mulVecLin x) v =
      (CerednikDrinfeld.classSetHeckeMatrix (Submodule.finiteIdeleStabilizer R) (CerednikDrinfeld.levelHeckeUSet Λ R ℓ)).mulVecLin
        (CerednikDrinfeld.pushforward
          (fun e : QuaternionAlgebra.ClassSet (Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) => QuaternionAlgebra.ClassSet.mk (Submodule.finiteIdeleStabilizer R) (e.out * m)) x) v :=
  GOODEQ.pushforward_levelHeckeUSet Λ R hΛ hR hRΛ q ℓ hq hℓ hcop n hn m τ hmτ x v

end S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin
end P2MW
export P2MW.S_CerednikDrinfeld_pushforward_classSetHeckeMatrix_levelHeckeUSet_meetOrder_mulVecLin (solution)
