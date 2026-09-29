-- Prove2me | solution 1 for CerednikDrinfeld.LevelU.not_le_of_mem_levelHeckeUSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c3d58826-d6e1-5439-9e34-d0d3827830e1

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_finiteAdeleBox_ofFiniteIdele
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_LevelU_not_le_of_mem_levelHeckeUSet
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
open scoped Quaternion TensorProduct NumberField Pointwise
open QuaternionAlgebra CerednikDrinfeld IsDedekindDomain

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace Nat
p2m_export "Nat" "Primes exists_eq_succ_of_ne_zero prime_iff cast_ne_zero prime_dvd_prime_iff_eq Coprime Prime prime_iff_prime_int isCoprime_iff_coprime eq_zero_or_pos cast_zero castRingHom all zero"
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

set_option autoImplicit false

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

noncomputable section

namespace LevelU4

scoped macro "fsr" : tactic => `(tactic| first | (ring; done) | (field_simp; done) | (field_simp; ring; done) | (simp; done) | (simp; ring; done))

theorem valuation_natCast_lt_one {p : ℕ} (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    Valued.v ((p : ℕ) : v.adicCompletion ℚ) < 1 := by
  have e : ((p : ℕ) : v.adicCompletion ℚ) = algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ) := by
    rw [map_natCast]
  have hval : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (p : ℚ)) = v.valuation ℚ (p : ℚ) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
  have e2 : (p : ℚ) = algebraMap (𝓞 ℚ) ℚ (p : 𝓞 ℚ) := by simp
  rw [e, hval, e2, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v _).mpr hpv

theorem natCast_ne_zero_adicCompletion {p : ℕ} (hp : p ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((p : ℕ) : v.adicCompletion ℚ) ≠ 0 := by
  rw [← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hp)

theorem inv_natCast_not_mem_adicCompletionIntegers {p : ℕ} (hp : p ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ))
    (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal) :
    ((p : ℕ) : v.adicCompletion ℚ)⁻¹ ∉ v.adicCompletionIntegers ℚ := by
  intro h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at h
  have hlt := valuation_natCast_lt_one v hpv
  have hne : Valued.v ((p : ℕ) : v.adicCompletion ℚ) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (natCast_ne_zero_adicCompletion hp v)
  have h1 : (1 : _) ≤ Valued.v ((p : ℕ) : v.adicCompletion ℚ) := (inv_le_one₀ (zero_lt_iff.mpr hne)).mp h
  exact absurd (lt_of_lt_of_le hlt h1) (lt_irrefl _)

theorem coe_units_inv (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletionIntegers ℚ)ˣ) :
    (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) =
      (((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)⁻¹ := by
  set f := (v.adicCompletionIntegers ℚ).subtype.toMonoidHom with hf
  calc (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ)
      = f ((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) := rfl
    _ = ((Units.map f u)⁻¹ : (v.adicCompletion ℚ)ˣ) := (Units.coe_map_inv f u).symm
    _ = ((Units.map f u : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)⁻¹ := Units.val_inv_eq_inv_val _
    _ = _ := by rw [Units.coe_map]; rfl

theorem coe_units_ne_zero (v : HeightOneSpectrum (𝓞 ℚ)) (u : (v.adicCompletionIntegers ℚ)ˣ) :
    (((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) ≠ 0 := by
  intro h0
  have h1 : (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) *
      (((u : (v.adicCompletionIntegers ℚ)ˣ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) = 1 := by
    have := congrArg (fun z : v.adicCompletionIntegers ℚ => (z : v.adicCompletion ℚ)) (Units.inv_mul u)
    push_cast at this
    exact this
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

namespace L2Lift
theorem natGenerator_eq {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ((Rat.HeightOneSpectrum.primesEquiv v : Nat.Primes) : ℕ) = ℓ := by
  show Rat.HeightOneSpectrum.natGenerator v = ℓ
  have hdvd : Rat.HeightOneSpectrum.natGenerator v ∣ ℓ := by
    rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff]
    have := Ideal.mem_map_of_mem (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) hv
    rwa [map_natCast] at this
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hℓ).mp hdvd

theorem exists_unit_mul_pow {ℓ : ℕ} (hℓ : ℓ.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (t₀ : v.adicCompletion ℚ) (ht₀ : t₀ ∈ v.adicCompletionIntegers ℚ) (ht₀0 : t₀ ≠ 0) :
    ∃ (n : ℕ) (u : (v.adicCompletionIntegers ℚ)ˣ),
      t₀ = ((u : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) * ((ℓ : ℕ) : v.adicCompletion ℚ) ^ n := by
  set t : v.adicCompletionIntegers ℚ := ⟨t₀, ht₀⟩ with htdef
  have ht : t ≠ 0 := fun h => ht₀0 (by rw [htdef] at h; exact congrArg Subtype.val h)
  haveI : Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv v : ℕ)) := ⟨(Rat.HeightOneSpectrum.primesEquiv v).2⟩
  set ψ := Rat.HeightOneSpectrum.adicCompletionIntegers.padicIntEquiv v with hψ
  have ht' : ψ t ≠ 0 := fun h => ht (by simpa using congrArg ψ.symm h)
  refine ⟨(ψ t).valuation, Units.map ψ.symm.toRingEquiv.toRingHom.toMonoidHom (PadicInt.unitCoeff ht'), ?_⟩
  show (t : v.adicCompletion ℚ) = _
  have key : t = ψ.symm ((PadicInt.unitCoeff ht' : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) *
      ((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) ^ (ψ t).valuation) := by
    rw [← PadicInt.unitCoeff_spec ht']; simp
  have hp : (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) =
      ((ℓ : ℕ) : v.adicCompletion ℚ) := by
    rw [← natGenerator_eq hℓ v hv]; exact map_natCast (algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) _
  have e1 : (t : v.adicCompletion ℚ) =
      ((ψ.symm (PadicInt.unitCoeff ht' : ℤ_[(Rat.HeightOneSpectrum.primesEquiv v : ℕ)]) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) *
        (((Rat.HeightOneSpectrum.primesEquiv v : ℕ) : v.adicCompletionIntegers ℚ) : v.adicCompletion ℚ) ^ (ψ t).valuation := by
    conv_lhs => rw [key]
    rw [map_mul, map_pow, map_natCast]
    push_cast
    rfl
  rw [e1, hp]
  rfl

end L2Lift

section Mat

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "K" => v.adicCompletion ℚ
local notation "O" => v.adicCompletionIntegers ℚ
local notation "M2" => Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)

def IsInt (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) : Prop :=
  ∀ i j, M i j ∈ v.adicCompletionIntegers ℚ

variable {v}

theorem mat_eq {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : K} (h₁ : a₁ = b₁) (h₂ : a₂ = b₂) (h₃ : a₃ = b₃) (h₄ : a₄ = b₄) :
    (!![a₁, a₂; a₃, a₄] : M2) = !![b₁, b₂; b₃, b₄] := by
  rw [h₁, h₂, h₃, h₄]

theorem IsInt.mul {A B : M2} (hA : IsInt v A) (hB : IsInt v B) : IsInt v (A * B) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem (mul_mem (hA i 0) (hB 0 j)) (mul_mem (hA i 1) (hB 1 j))

theorem isInt_of_entries {a b c d : K} (ha : a ∈ O) (hb : b ∈ O) (hc : c ∈ O) (hd : d ∈ O) :
    IsInt v !![a, b; c, d] := by
  intro i j
  fin_cases i <;> fin_cases j <;> simpa

def S (c : v.adicCompletion ℚ) : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := !![c, 0; 0, c]

theorem S_mul_S (c d : K) : S (v := v) c * S d = S (c * d) := by
  unfold S; rw [Matrix.mul_fin_two]; exact mat_eq (by ring) (by ring) (by ring) (by ring)

theorem S_one : S (v := v) 1 = 1 := by
  unfold S; rw [Matrix.one_fin_two]

theorem S_comm (c : K) (Y : M2) : S (v := v) c * Y = Y * S c := by
  unfold S
  rw [Matrix.eta_fin_two Y, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact mat_eq (by ring) (by ring) (by ring) (by ring)

theorem S_inv_conj {c : K} (hc : c ≠ 0) (Y : M2) : S (v := v) c⁻¹ * Y * S c = Y := by
  rw [S_comm, mul_assoc, S_mul_S, inv_mul_cancel₀ hc, S_one, mul_one]

theorem isInt_conj_iff {u ui : M2} (hu : IsInt v u) (hui : IsInt v ui) (h1 : u * ui = 1) (Y : M2) :
    IsInt v (ui * Y * u) ↔ IsInt v Y := by
  constructor
  · intro h
    have e : Y = u * (ui * Y * u) * ui := by
      rw [← mul_assoc, ← mul_assoc, h1, one_mul, mul_assoc, h1, mul_one]
    rw [e]
    exact (hu.mul h).mul hui
  · intro h
    exact (hui.mul h).mul hu

theorem inv_unique {k ki kI : M2} (hki : ki * k = 1) (hkI : k * kI = 1) : ki = kI := by
  calc ki = ki * (k * kI) := by rw [hkI, mul_one]
    _ = kI := by rw [← mul_assoc, hki, one_mul]

theorem forall_isInt_conj_iff_of_eq {k ki B Bi u ui : M2} {c : K} (hc : c ≠ 0)
    (hki : ki * k = 1) (hB : B * Bi = 1)
    (hu : IsInt v u) (hui : IsInt v ui) (h1 : u * ui = 1)
    (he : k = B * u * S c) (X : M2) :
    IsInt v (ki * X * k) ↔ IsInt v (Bi * X * B) := by
  have hkI : k * (S c⁻¹ * ui * Bi) = 1 := by
    rw [he]
    calc B * u * S c * (S c⁻¹ * ui * Bi) = B * (u * (S c * S c⁻¹) * ui) * Bi := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [S_mul_S, mul_inv_cancel₀ hc, S_one, mul_one, h1, mul_one, hB]
  have eki : ki = S c⁻¹ * ui * Bi := inv_unique hki hkI
  have e : ki * X * k = S c⁻¹ * (ui * (Bi * X * B) * u) * S c := by
    rw [eki, he]; simp only [Matrix.mul_assoc]
  rw [e, S_inv_conj hc, isInt_conj_iff hu hui h1]

theorem exists_hnf_of_lowerLeft_eq_mul (k ki : M2) (hk : k * ki = 1)
    (a : K) (ha : a ∈ O) (hra : k 1 0 = a * k 1 1) :
    ∃ (c t x : K) (u ui : M2), c ≠ 0 ∧ t ≠ 0 ∧ IsInt v u ∧ IsInt v ui ∧ u * ui = 1 ∧ ui * u = 1 ∧
      k = !![t, x; 0, 1] * u * S c := by
  have hdet : k.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hk
    rw [Matrix.det_mul, h0, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have hs : k 1 1 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_fin_two, hra, h0]; ring
  have hp : k 0 0 - a * k 0 1 ≠ 0 := by
    intro h0
    apply hdet
    rw [Matrix.det_fin_two, hra]
    have : k 0 0 = a * k 0 1 := sub_eq_zero.mp h0
    rw [this]; ring
  refine ⟨k 1 1, (k 0 0 - a * k 0 1) * (k 1 1)⁻¹, k 0 1 * (k 1 1)⁻¹, !![1, 0; a, 1], !![1, 0; -a, 1],
    hs, mul_ne_zero hp (inv_ne_zero hs), ?_, ?_, ?_, ?_, ?_⟩
  · exact isInt_of_entries (one_mem _) (zero_mem _) ha (one_mem _)
  · exact isInt_of_entries (one_mem _) (zero_mem _) (neg_mem ha) (one_mem _)
  · rw [Matrix.mul_fin_two, Matrix.one_fin_two]; exact mat_eq (by ring) (by ring) (by ring) (by ring)
  · rw [Matrix.mul_fin_two, Matrix.one_fin_two]; exact mat_eq (by ring) (by ring) (by ring) (by ring)
  · unfold S
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    conv_lhs => rw [Matrix.eta_fin_two k]
    exact mat_eq (by fsr) (by fsr) (by rw [hra]; fsr) (by fsr)

theorem exists_hnf (k ki : M2) (hk : k * ki = 1) (hki : ki * k = 1) :
    ∃ (c t x : K) (u ui : M2), c ≠ 0 ∧ t ≠ 0 ∧ IsInt v u ∧ IsInt v ui ∧ u * ui = 1 ∧ ui * u = 1 ∧
      k = !![t, x; 0, 1] * u * S c := by
  by_cases hr : k 1 0 = 0
  · exact exists_hnf_of_lowerLeft_eq_mul k ki hk 0 (zero_mem _) (by rw [hr, zero_mul])

  set J : M2 := !![0, 1; 1, 0] with hJ
  have hJJ : J * J = 1 := by
    rw [hJ, Matrix.mul_fin_two, Matrix.one_fin_two]; exact mat_eq (by ring) (by ring) (by ring) (by ring)
  have hJint : IsInt v J := isInt_of_entries (zero_mem _) (one_mem _) (one_mem _) (zero_mem _)
  have hk' : (k * J) * (J * ki) = 1 := by rw [mul_assoc, ← mul_assoc J, hJJ, one_mul, hk]
  have e10 : (k * J) 1 0 = k 1 1 := by
    rw [Matrix.eta_fin_two k, hJ, Matrix.mul_fin_two]; simp
  have e11 : (k * J) 1 1 = k 1 0 := by
    rw [Matrix.eta_fin_two k, hJ, Matrix.mul_fin_two]; simp
  have key : ∀ a : K, a ∈ O → (k * J) 1 0 = a * (k * J) 1 1 →
      ∃ (c t x : K) (u ui : M2), c ≠ 0 ∧ t ≠ 0 ∧ IsInt v u ∧ IsInt v ui ∧ u * ui = 1 ∧ ui * u = 1 ∧
        k = !![t, x; 0, 1] * u * S c := by
    intro a ha hra
    obtain ⟨c, t, x, u, ui, hc, ht, hu, hui, h1, h2, he⟩ := exists_hnf_of_lowerLeft_eq_mul (k * J) (J * ki) hk' a ha hra
    refine ⟨c, t, x, u * J, J * ui, hc, ht, hu.mul hJint, hJint.mul hui, ?_, ?_, ?_⟩
    · rw [mul_assoc, ← mul_assoc J, hJJ, one_mul, h1]
    · rw [mul_assoc, ← mul_assoc ui, h2, one_mul, hJJ]
    · calc k = k * J * J := by rw [mul_assoc, hJJ, mul_one]
        _ = !![t, x; 0, 1] * u * S c * J := by rw [he]
        _ = !![t, x; 0, 1] * (u * J) * S c := by rw [mul_assoc _ (S c) J, S_comm c J, ← mul_assoc, mul_assoc _ u J]
  by_cases hs : k 1 1 = 0
  · exact key 0 (zero_mem _) (by rw [e10, e11, hs, zero_mul])
  rcases (v.adicCompletionIntegers ℚ).mem_or_inv_mem (k 1 0 * (k 1 1)⁻¹) with h | h
  · exact exists_hnf_of_lowerLeft_eq_mul k ki hk _ h (by rw [inv_mul_cancel_right₀ hs])
  · rw [mul_inv_rev, inv_inv] at h
    exact key _ h (by rw [e10, e11, inv_mul_cancel_right₀ hr])

theorem hnf_inv (t x : K) (ht : t ≠ 0) :
    (!![t, x; 0, 1] : M2) * !![t⁻¹, -x * t⁻¹; 0, 1] = 1 ∧ (!![t⁻¹, -x * t⁻¹; 0, 1] : M2) * !![t, x; 0, 1] = 1 := by
  constructor
  · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact mat_eq (by fsr) (by fsr) (by fsr) (by fsr)
  · rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    exact mat_eq (by fsr) (by fsr) (by fsr) (by fsr)

theorem tests_hnf (p : K) (t x : K) (ht : t ≠ 0)
    (h11 : IsInt v (!![t⁻¹, -x * t⁻¹; 0, 1] * !![1, 0; 0, 0] * !![t, x; 0, 1]))
    (h12 : IsInt v (!![t⁻¹, -x * t⁻¹; 0, 1] * !![0, 1; 0, 0] * !![t, x; 0, 1]))
    (h21 : IsInt v (!![t⁻¹, -x * t⁻¹; 0, 1] * !![0, 0; p, 0] * !![t, x; 0, 1])) :
    x * t⁻¹ ∈ O ∧ t⁻¹ ∈ O ∧ p * t ∈ O := by
  refine ⟨?_, ?_, ?_⟩
  · have h := h11 0 1
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h
    have e : x * t⁻¹ = (t⁻¹ * 1 + -x * t⁻¹ * 0) * x + (t⁻¹ * 0 + -x * t⁻¹ * 0) * 1 := by ring
    rw [e]; simpa using h
  · have h := h12 0 1
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h
    have e : t⁻¹ = (t⁻¹ * 0 + -x * t⁻¹ * 0) * x + (t⁻¹ * 1 + -x * t⁻¹ * 0) * 1 := by ring
    rw [e]; simpa using h
  · have h := h21 1 0
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h
    have e : p * t = (0 * 0 + 1 * p) * t + (0 * 0 + 1 * 0) * 0 := by ring
    rw [e]; simpa using h

variable {p : ℕ}

theorem exists_unit_eq_natCast_mul (hp : p.Prime) (hpv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) {t : K} (ht : t ≠ 0)
    (h1 : t⁻¹ ∈ O) (h2 : t ∉ O) (h3 : (p : K) * t ∈ O) :
    ∃ w : (v.adicCompletionIntegers ℚ)ˣ, ((w : O) : K) = (p : K) * t := by
  obtain ⟨n, u, hu⟩ := L2Lift.exists_unit_mul_pow hp v hpv t⁻¹ h1 (inv_ne_zero ht)
  have hp0 : ((p : ℕ) : K) ≠ 0 := natCast_ne_zero_adicCompletion hp.ne_zero v
  have hu0 := coe_units_ne_zero v u
  have hui := coe_units_inv v u

  have hn : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hu
    apply h2
    have : t = (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : O) : K) := by
      rw [hui, ← hu, inv_inv]
    rw [this]; exact SetLike.coe_mem _
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have ept : (p : K) * t = (((u⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : O) : K) * (((p : ℕ) : K) ^ m)⁻¹ := by
    have e1 : t = (t⁻¹)⁻¹ := (inv_inv t).symm
    rw [e1, hu, hui, pow_succ]
    field_simp
  by_cases hm : m = 0
  · subst hm
    refine ⟨u⁻¹, ?_⟩
    rw [ept, pow_zero, inv_one, mul_one]
  · exfalso
    obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    apply inv_natCast_not_mem_adicCompletionIntegers hp.ne_zero v hpv

    have e : ((p : ℕ) : K)⁻¹ = ((p : K) * t) * ((u : O) : K) * ((p : ℕ) : K) ^ m' := by
      rw [ept, hui, pow_succ]
      field_simp
    rw [e]
    exact mul_mem (mul_mem h3 (SetLike.coe_mem _)) (pow_mem (natCast_mem _ _) _)

theorem diag_eq (c d : K) : Matrix.diagonal ![c, d] = !![c, 0; 0, d] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem diag_inv (p : K) (hp : p ≠ 0) :
    Matrix.diagonal ![(1 : K), p] * Matrix.diagonal ![(1 : K), p⁻¹] = 1 := by
  rw [diag_eq, diag_eq, Matrix.mul_fin_two, Matrix.one_fin_two]
  exact mat_eq (by fsr) (by fsr) (by fsr) (by fsr)

theorem forall_isInt_conj_iff_or (hp : p.Prime) (hpv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (k ki : M2) (hk : k * ki = 1) (hki : ki * k = 1)
    (h11 : IsInt v (ki * !![1, 0; 0, 0] * k)) (h12 : IsInt v (ki * !![0, 1; 0, 0] * k))
    (h21 : IsInt v (ki * !![0, 0; ((p : ℕ) : K), 0] * k)) :
    (∀ X : M2, IsInt v (ki * X * k) ↔ IsInt v X) ∨
      (∀ X : M2, IsInt v (ki * X * k) ↔
        IsInt v (Matrix.diagonal ![(1 : K), ((p : ℕ) : K)⁻¹] * X * Matrix.diagonal ![(1 : K), ((p : ℕ) : K)])) := by
  have hp0 : ((p : ℕ) : K) ≠ 0 := natCast_ne_zero_adicCompletion hp.ne_zero v
  obtain ⟨c, t, x, u, ui, hc, ht, hu, hui, h1, h2, he⟩ := exists_hnf k ki hk hki
  obtain ⟨hH1, hH2⟩ := hnf_inv (v := v) t x ht

  have hT : ∀ X : M2, IsInt v (ki * X * k) ↔ IsInt v (!![t⁻¹, -x * t⁻¹; 0, 1] * X * !![t, x; 0, 1]) :=
    forall_isInt_conj_iff_of_eq hc hki hH1 hu hui h1 he
  obtain ⟨hxt, hti, hpt⟩ := tests_hnf (v := v) ((p : ℕ) : K) t x ht ((hT _).mp h11) ((hT _).mp h12) ((hT _).mp h21)
  by_cases htO : t ∈ O
  ·
    left
    have hx : x ∈ O := by
      have := mul_mem hxt htO
      rwa [inv_mul_cancel_right₀ ht] at this
    have hH : IsInt v !![t, x; 0, 1] := isInt_of_entries htO hx (zero_mem _) (one_mem _)
    have hHi : IsInt v !![t⁻¹, -x * t⁻¹; 0, 1] :=
      isInt_of_entries hti (by rw [neg_mul]; exact neg_mem hxt) (zero_mem _) (one_mem _)
    intro X
    rw [hT, isInt_conj_iff hH hHi hH1]
  ·
    right
    obtain ⟨w, hw⟩ := exists_unit_eq_natCast_mul hp hpv ht hti htO hpt
    have hw0 := coe_units_ne_zero v w
    have hwi := coe_units_inv v w
    set U : M2 := !![1, x * t⁻¹; 0, ((w : O) : K)⁻¹] with hU
    set Ui : M2 := !![1, -(x * t⁻¹) * ((w : O) : K); 0, ((w : O) : K)] with hUi
    have hwiO : ((w : O) : K)⁻¹ ∈ O := by rw [← hwi]; exact SetLike.coe_mem _
    have hUint : IsInt v U := isInt_of_entries (one_mem _) hxt (zero_mem _) hwiO
    have hUiint : IsInt v Ui :=
      isInt_of_entries (one_mem _) (mul_mem (neg_mem hxt) (SetLike.coe_mem _)) (zero_mem _) (SetLike.coe_mem _)
    have hU1 : U * Ui = 1 := by
      rw [hU, hUi, Matrix.mul_fin_two, Matrix.one_fin_two]
      exact mat_eq (by fsr) (by fsr) (by fsr) (by fsr)
    have hD1 := diag_inv (v := v) ((p : ℕ) : K) hp0
    have heH : (!![t, x; 0, 1] : M2) = Matrix.diagonal ![(1 : K), ((p : ℕ) : K)] * U * S t := by
      rw [hU, diag_eq]; unfold S
      rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
      have h3 : ((p : ℕ) : K) * ((w : O) : K)⁻¹ * t = 1 := by rw [hw]; field_simp
      exact mat_eq (by fsr) (by fsr) (by fsr) (by rw [← h3]; fsr)
    intro X
    rw [hT]
    exact forall_isInt_conj_iff_of_eq ht hH2 hD1 hUint hUiint hU1 heH X

end Mat

section Mat4

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "K" => v.adicCompletion ℚ
local notation "O" => v.adicCompletionIntegers ℚ
local notation "M2" => Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)

theorem tests_hnf2 (t x : K)
    (h11 : IsInt v (!![t⁻¹, -x * t⁻¹; 0, 1] * !![1, 0; 0, 0] * !![t, x; 0, 1]))
    (h12 : IsInt v (!![t⁻¹, -x * t⁻¹; 0, 1] * !![0, 1; 0, 0] * !![t, x; 0, 1])) :
    x * t⁻¹ ∈ O ∧ t⁻¹ ∈ O := by
  refine ⟨?_, ?_⟩
  · have h := h11 0 1
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h
    have e : x * t⁻¹ = (t⁻¹ * 1 + -x * t⁻¹ * 0) * x + (t⁻¹ * 0 + -x * t⁻¹ * 0) * 1 := by ring
    rw [e]; simpa using h
  · have h := h12 0 1
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two] at h
    have e : t⁻¹ = (t⁻¹ * 0 + -x * t⁻¹ * 0) * x + (t⁻¹ * 1 + -x * t⁻¹ * 0) * 1 := by ring
    rw [e]; simpa using h

variable {p : ℕ}

theorem isInt_inv_mul_diagonal (hp : p.Prime) (hpv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) {e : ℕ} (he : 1 ≤ e)
    (G Gi : M2) (hG : G * Gi = 1) (hGi : Gi * G = 1)
    (hG1 : IsInt v G) (hG2 : IsInt v (S ((p : ℕ) : K) * Gi)) (hG4 : ¬ IsInt v (S ((p : ℕ) : K)⁻¹ * G))
    (t11 : IsInt v (Gi * !![1, 0; 0, 0] * G)) (t12 : IsInt v (Gi * !![0, 1; 0, 0] * G)) :
    IsInt v (Gi * Matrix.diagonal ![(1 : K), ((p : ℕ) : K) ^ e]) := by
  have hp0 : ((p : ℕ) : K) ≠ 0 := natCast_ne_zero_adicCompletion hp.ne_zero v
  obtain ⟨c, t, x, u, ui, hc, ht, hu, hui, h1u, h2u, heq⟩ := exists_hnf G Gi hG hGi
  obtain ⟨hH1, hH2⟩ := hnf_inv (v := v) t x ht
  set T : M2 := !![t, x; 0, 1] with hTdef
  set Ti : M2 := !![t⁻¹, -x * t⁻¹; 0, 1] with hTidef
  have hT : ∀ X : M2, IsInt v (Gi * X * G) ↔ IsInt v (Ti * X * T) :=
    forall_isInt_conj_iff_of_eq hc hGi hH1 hu hui h1u heq
  obtain ⟨hxt, hti⟩ := tests_hnf2 (v := v) t x ((hT _).mp t11) ((hT _).mp t12)

  have hGI : G * (S c⁻¹ * ui * Ti) = 1 := by
    rw [heq]
    calc T * u * S c * (S c⁻¹ * ui * Ti)
        = T * (u * (S c * S c⁻¹) * ui) * Ti := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [S_mul_S, mul_inv_cancel₀ hc, S_one, mul_one, h1u, mul_one, hH1]
  have eGi : Gi = S c⁻¹ * ui * Ti := inv_unique hGi hGI

  have hTS : IsInt v (T * S c) := by
    have e1 : G * ui = T * S c := by
      rw [heq, show T * u * S c * ui = T * (u * (S c * ui)) by simp only [Matrix.mul_assoc], S_comm c ui,
        ← Matrix.mul_assoc u, h1u, Matrix.one_mul]
    rw [← e1]; exact hG1.mul hui
  have eTS : T * S c = !![t * c, x * c; 0, c] := by
    rw [hTdef]; unfold S; rw [Matrix.mul_fin_two]; exact mat_eq (by fsr) (by fsr) (by fsr) (by fsr)
  rw [eTS] at hTS
  have hct : t * c ∈ O := by simpa using hTS 0 0
  have hcO : c ∈ O := by simpa using hTS 1 1

  have hPT : IsInt v (S (((p : ℕ) : K) * c⁻¹) * Ti) := by
    have e1 : u * (S ((p : ℕ) : K) * Gi) = S (((p : ℕ) : K) * c⁻¹) * Ti := by
      rw [eGi, show S ((p : ℕ) : K) * (S c⁻¹ * ui * Ti) = (S ((p : ℕ) : K) * S c⁻¹) * ui * Ti by
        simp only [Matrix.mul_assoc], S_mul_S, S_comm _ ui,
        show u * (ui * S (((p : ℕ) : K) * c⁻¹) * Ti) = (u * ui) * S (((p : ℕ) : K) * c⁻¹) * Ti by
          simp only [Matrix.mul_assoc], h1u, Matrix.one_mul]
    rw [← e1]; exact hu.mul hG2
  have ePT : S (((p : ℕ) : K) * c⁻¹) * Ti =
      !![((p : ℕ) : K) * c⁻¹ * t⁻¹, -(((p : ℕ) : K) * c⁻¹ * (x * t⁻¹)); 0, ((p : ℕ) : K) * c⁻¹] := by
    rw [hTidef]; unfold S; rw [Matrix.mul_fin_two]; exact mat_eq (by fsr) (by fsr) (by fsr) (by fsr)
  rw [ePT] at hPT
  have hpct : ((p : ℕ) : K) * c⁻¹ * t⁻¹ ∈ O := by simpa using hPT 0 0
  have hpc : ((p : ℕ) : K) * c⁻¹ ∈ O := by simpa using hPT 1 1

  have hcti : (c * t)⁻¹ ∈ O := by
    rcases (v.adicCompletionIntegers ℚ).mem_or_inv_mem (c * t) with hmem | hinv
    swap
    · exact hinv
    by_contra hnot

    have hct0 : c * t ≠ 0 := mul_ne_zero hc ht
    obtain ⟨w, hw⟩ := exists_unit_eq_natCast_mul (v := v) hp hpv (inv_ne_zero hct0)
      (by rw [inv_inv]; exact hmem) hnot (by rw [mul_inv]; simpa [mul_assoc] using hpct)

    have hctp : c * t * ((p : ℕ) : K)⁻¹ ∈ O := by
      have e2 : c * t * ((p : ℕ) : K)⁻¹ = (((w⁻¹ : (v.adicCompletionIntegers ℚ)ˣ) : O) : K) := by
        rw [coe_units_inv, hw]; field_simp
      rw [e2]; exact SetLike.coe_mem _
    apply hG4

    have e3 : S ((p : ℕ) : K)⁻¹ * G = S (((p : ℕ) : K)⁻¹ * c) * T * u := by
      rw [heq, show S ((p : ℕ) : K)⁻¹ * (T * u * S c) = S ((p : ℕ) : K)⁻¹ * (T * (u * S c)) by
        simp only [Matrix.mul_assoc], ← S_comm c u, ← Matrix.mul_assoc T, ← S_comm c T,
        show S ((p : ℕ) : K)⁻¹ * (S c * T * u) = (S ((p : ℕ) : K)⁻¹ * S c) * T * u by simp only [Matrix.mul_assoc],
        S_mul_S]
    have e4 : S (((p : ℕ) : K)⁻¹ * c) * T =
        !![((p : ℕ) : K)⁻¹ * c * t, ((p : ℕ) : K)⁻¹ * c * x; 0, ((p : ℕ) : K)⁻¹ * c] := by
      rw [hTdef]; unfold S; rw [Matrix.mul_fin_two]; exact mat_eq (by fsr) (by fsr) (by fsr) (by fsr)
    rw [e3, e4]
    refine IsInt.mul (isInt_of_entries ?_ ?_ (zero_mem _) ?_) hu
    · have : ((p : ℕ) : K)⁻¹ * c * t = c * t * ((p : ℕ) : K)⁻¹ := by ring
      rw [this]; exact hctp
    · have : ((p : ℕ) : K)⁻¹ * c * x = c * t * ((p : ℕ) : K)⁻¹ * (x * t⁻¹) := by field_simp
      rw [this]; exact mul_mem hctp hxt
    · have : ((p : ℕ) : K)⁻¹ * c = c * t * ((p : ℕ) : K)⁻¹ * t⁻¹ := by field_simp
      rw [this]; exact mul_mem hctp hti

  obtain ⟨e', rfl⟩ := Nat.exists_eq_add_of_le he
  have eF : Gi * Matrix.diagonal ![(1 : K), ((p : ℕ) : K) ^ (1 + e')] =
      ui * !![c⁻¹ * t⁻¹, -(x * t⁻¹) * (((p : ℕ) : K) * c⁻¹) * ((p : ℕ) : K) ^ e';
        0, (((p : ℕ) : K) * c⁻¹) * ((p : ℕ) : K) ^ e'] := by
    rw [eGi, mul_assoc (S c⁻¹) ui, S_comm, mul_assoc, mul_assoc, hTidef, diag_eq]
    congr 1
    unfold S
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    exact mat_eq (by fsr) (by rw [pow_add, pow_one]; fsr) (by fsr) (by rw [pow_add, pow_one]; fsr)
  rw [eF]
  refine hui.mul (isInt_of_entries ?_ ?_ (zero_mem _) ?_)
  · rw [← mul_inv]; exact hcti
  · exact mul_mem (mul_mem (neg_mem hxt) hpc) (pow_mem (natCast_mem _ _) _)
  · exact mul_mem hpc (pow_mem (natCast_mem _ _) _)

end Mat4

section Loc

variable {a b : ℚ}

local notation "𝔸ℍ" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem localBox_mono' {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (v : HeightOneSpectrum (𝓞 ℚ)) :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v := by
  unfold Submodule.localBox
  refine AddSubgroup.closure_mono ?_
  rintro x ⟨z, hz, c, hc, rfl⟩
  exact ⟨z, h hz, c, hc, rfl⟩

theorem rat_smul_eq_one_tmul_mul (v : HeightOneSpectrum (𝓞 ℚ)) (q : ℚ) (z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    q • z = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (algebraMap ℚ (v.adicCompletion ℚ) q)) * z := by
  have h := Algebra.smul_def q z
  rw [Algebra.TensorProduct.algebraMap_apply'] at h
  exact h

theorem smul_one_eq_S (v : HeightOneSpectrum (𝓞 ℚ)) (r : v.adicCompletion ℚ) :
    r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) = S r := by
  unfold S
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem mem_conjByFiniteIdele_iff' (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (𝔸ℍ)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      ((g⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : 𝔸ℍ) ∈ Submodule.finiteAdeleBox Λ := by
  show z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ (Submodule.finiteAdeleBox Λ).map _ ↔ _
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨u, hu, h⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight] at h
    have : ((g⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : 𝔸ℍ) = u := by
      rw [← h, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact hu
  · intro h
    refine ⟨_, h, ?_⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    show (g : 𝔸ℍ) * (((g⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) * (g : 𝔸ℍ)) * ((g⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = _
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem conjByFiniteIdele_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') (g : (𝔸ℍ)ˣ) :
    Submodule.conjByFiniteIdele Λ g ≤ Submodule.conjByFiniteIdele Λ' g := by
  intro z hz
  rw [mem_conjByFiniteIdele_iff'] at hz ⊢
  exact HeckeLocal.box_mono h hz

theorem ofFiniteIdele_mul_le_of_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (x m : (𝔸ℍ)ˣ) (hm : ((m : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ Submodule.finiteAdeleBox Λ) :
    Submodule.ofFiniteIdele Λ (x * m) ≤ Submodule.ofFiniteIdele Λ x := by
  intro z hz
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map] at hz ⊢
  obtain ⟨w, hw, hwz⟩ := hz
  refine ⟨(m : 𝔸ℍ) * w, HeckeLocal.box_mul_mem hΛ hm hw, ?_⟩
  rw [← hwz, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulLeft, Units.val_mul, mul_assoc]

theorem mem_localBox_meetOrder_iff {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : QuaternionAlgebra.IsOrder R)
    (n : (𝔸ℍ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    z ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ↔
      z ∈ Submodule.localBox R v ∧
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((n⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * z *
          Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (n : 𝔸ℍ) ∈ Submodule.localBox R v := by
  have hC : QuaternionAlgebra.IsOrder (Submodule.conjByFiniteIdele R n) := QuaternionAlgebra.IsOrder.conjByFiniteIdele R hRo n
  show z ∈ Submodule.localBox (R ⊓ Submodule.conjByFiniteIdele R n) v ↔ _
  rw [Submodule.localBox_inf R _ hRo.fg hRo.spanTop hC.fg hC.spanTop v, AddSubgroup.mem_inf,
    Submodule.mem_localBox_conjByFiniteIdele_iff R hRo.fg hRo.spanTop n v z]
  have e1 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((n⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) *
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (n : 𝔸ℍ) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  have e2 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (n : 𝔸ℍ) *
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v ((n⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  refine and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    rw [show ∀ A B Y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, B * (A * Y * B) * A = (B * A) * Y * (B * A) from
      fun A B Y => by simp only [mul_assoc], e1, one_mul, mul_one]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    rw [show ∀ A B Y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, A * (B * Y * A) * B = (A * B) * Y * (A * B) from
      fun A B Y => by simp only [mul_assoc], e2, one_mul, mul_one]

variable {v : HeightOneSpectrum (𝓞 ℚ)} {p : ℕ}

theorem isInt_Di_E11_D (d : v.adicCompletion ℚ) (hd : d ≠ 0) :
    IsInt v (Matrix.diagonal ![(1 : v.adicCompletion ℚ), d⁻¹] * !![1, 0; 0, 0] * Matrix.diagonal ![(1 : v.adicCompletion ℚ), d]) := by
  rw [diag_eq, diag_eq, Matrix.mul_fin_two, Matrix.mul_fin_two]
  refine isInt_of_entries ?_ ?_ ?_ ?_ <;> simp

theorem isInt_Di_E12_D (d : v.adicCompletion ℚ) (hdO : d ∈ v.adicCompletionIntegers ℚ) :
    IsInt v (Matrix.diagonal ![(1 : v.adicCompletion ℚ), d⁻¹] * !![0, 1; 0, 0] * Matrix.diagonal ![(1 : v.adicCompletion ℚ), d]) := by
  rw [diag_eq, diag_eq, Matrix.mul_fin_two, Matrix.mul_fin_two]
  exact isInt_of_entries (by simp) (by simpa using hdO) (by simp) (by simp)

theorem core_matrix (hp : p.Prime) (hpv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) {e : ℕ} (he : 1 ≤ e)
    (K₁ K₁i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (hK₁ : K₁ * K₁i = 1) (hK₁' : K₁i * K₁ = 1)
    (iK₁ : IsInt v K₁) (iK₁i : IsInt v K₁i)
    (H Hi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (hHHi : H * Hi = 1) (hHiH : Hi * H = 1)
    (hH1 : IsInt v H) (hH2 : IsInt v (S ((p : ℕ) : v.adicCompletion ℚ) * Hi))
    (hH4 : ¬ IsInt v (S ((p : ℕ) : v.adicCompletion ℚ)⁻¹ * H))
    (htest : ∀ E : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), IsInt v E →
      IsInt v (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((p : ℕ) : v.adicCompletion ℚ) ^ e)⁻¹] * E *
        Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e]) →
      IsInt v (Hi * (K₁ * E * K₁i) * H)) :
    IsInt v (Hi * K₁ * Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e]) := by
  have hp0 : ((p : ℕ) : v.adicCompletion ℚ) ≠ 0 := natCast_ne_zero_adicCompletion hp.ne_zero v
  have hpe0 : ((p : ℕ) : v.adicCompletion ℚ) ^ e ≠ 0 := pow_ne_zero _ hp0
  have hGGi : (K₁i * H) * (Hi * K₁) = 1 := by
    rw [show K₁i * H * (Hi * K₁) = K₁i * (H * Hi) * K₁ by simp only [Matrix.mul_assoc], hHHi, mul_one, hK₁']
  have hGiG : (Hi * K₁) * (K₁i * H) = 1 := by
    rw [show Hi * K₁ * (K₁i * H) = Hi * (K₁ * K₁i) * H by simp only [Matrix.mul_assoc], hK₁, mul_one, hHiH]
  have hG1 : IsInt v (K₁i * H) := iK₁i.mul hH1
  have hG2 : IsInt v (S ((p : ℕ) : v.adicCompletion ℚ) * (Hi * K₁)) := by
    rw [← Matrix.mul_assoc]; exact hH2.mul iK₁
  have hG4 : ¬ IsInt v (S ((p : ℕ) : v.adicCompletion ℚ)⁻¹ * (K₁i * H)) := by
    intro hint
    apply hH4
    have e1 : S ((p : ℕ) : v.adicCompletion ℚ)⁻¹ * H = K₁ * (S ((p : ℕ) : v.adicCompletion ℚ)⁻¹ * (K₁i * H)) := by
      rw [← Matrix.mul_assoc, ← S_comm, Matrix.mul_assoc, ← Matrix.mul_assoc K₁, hK₁, Matrix.one_mul]
    rw [e1]; exact iK₁.mul hint
  have t11 : IsInt v (Hi * K₁ * !![1, 0; 0, 0] * (K₁i * H)) := by
    have := htest _ (isInt_of_entries (one_mem _) (zero_mem _) (zero_mem _) (zero_mem _)) (isInt_Di_E11_D _ hpe0)
    rw [show Hi * (K₁ * !![1, 0; 0, 0] * K₁i) * H = Hi * K₁ * !![1, 0; 0, 0] * (K₁i * H) by
      simp only [Matrix.mul_assoc]] at this
    exact this
  have t12 : IsInt v (Hi * K₁ * !![0, 1; 0, 0] * (K₁i * H)) := by
    have := htest _ (isInt_of_entries (zero_mem _) (one_mem _) (zero_mem _) (zero_mem _))
      (isInt_Di_E12_D _ (pow_mem (natCast_mem _ _) _))
    rw [show Hi * (K₁ * !![0, 1; 0, 0] * K₁i) * H = Hi * K₁ * !![0, 1; 0, 0] * (K₁i * H) by
      simp only [Matrix.mul_assoc]] at this
    exact this
  exact isInt_inv_mul_diagonal hp hpv he (K₁i * H) (Hi * K₁) hGGi hGiG hG1 hG2 hG4 t11 t12

theorem local_step (hp : p.Prime) (hpv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) {e : ℕ} (he : 1 ≤ e)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ r : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (Λv Rv : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hΛv : ∀ z, z ∈ Λv ↔ IsInt v (φ z))
    (K₁ K₁i K₂ K₂i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hK₁ : K₁ * K₁i = 1) (hK₁' : K₁i * K₁ = 1) (hK₂ : K₂ * K₂i = 1)
    (iK₁ : IsInt v K₁) (iK₁i : IsInt v K₁i) (iK₂ : IsInt v K₂) (iK₂i : IsInt v K₂i)
    (mv mvi : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (hmm' : mvi * mv = 1)
    (hmv : φ mv = K₁ * Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e] * K₂)
    (hRv : ∀ z, z ∈ Rv ↔ z ∈ Λv ∧ mvi * z * mv ∈ Λv)
    (hv hvi : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (hhh : hv * hvi = 1) (hhh' : hvi * hv = 1)
    (h1 : hv ∈ Λv) (h2 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((p : ℕ) : v.adicCompletion ℚ)) * hvi ∈ Λv)
    (h4 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((p : ℕ) : v.adicCompletion ℚ)⁻¹) * hv ∉ Λv)
    (hconj : ∀ r ∈ Rv, hvi * r * hv ∈ Λv) :
    hvi * mv ∈ Λv := by
  have hp0 : ((p : ℕ) : v.adicCompletion ℚ) ≠ 0 := natCast_ne_zero_adicCompletion hp.ne_zero v
  have hpe0 : ((p : ℕ) : v.adicCompletion ℚ) ^ e ≠ 0 := pow_ne_zero _ hp0
  have hDDi : Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e] *
      Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((p : ℕ) : v.adicCompletion ℚ) ^ e)⁻¹] = 1 := diag_inv _ hpe0
  have hHHi : φ hv * φ hvi = 1 := by rw [← map_mul, hhh, map_one]
  have hHiH : φ hvi * φ hv = 1 := by rw [← map_mul, hhh', map_one]
  have hH1 : IsInt v (φ hv) := (hΛv _).mp h1
  have hH2 : IsInt v (S ((p : ℕ) : v.adicCompletion ℚ) * φ hvi) := by
    have h2' := (hΛv _).mp h2
    rwa [map_mul, hφ, smul_one_eq_S] at h2'
  have hH4 : ¬ IsInt v (S ((p : ℕ) : v.adicCompletion ℚ)⁻¹ * φ hv) := by
    intro hint
    apply h4
    rw [hΛv, map_mul, hφ, smul_one_eq_S]
    exact hint

  have hM : φ mv * (K₂i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((p : ℕ) : v.adicCompletion ℚ) ^ e)⁻¹] * K₁i) = 1 := by
    rw [hmv]
    calc K₁ * Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e] * K₂ *
          (K₂i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((p : ℕ) : v.adicCompletion ℚ) ^ e)⁻¹] * K₁i)
        = K₁ * (Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e] * (K₂ * K₂i) *
          Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((p : ℕ) : v.adicCompletion ℚ) ^ e)⁻¹]) * K₁i := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hK₂, mul_one, hDDi, mul_one, hK₁]
  have hMi' : φ mvi * φ mv = 1 := by rw [← map_mul, hmm', map_one]
  have eMi : φ mvi = K₂i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((p : ℕ) : v.adicCompletion ℚ) ^ e)⁻¹] * K₁i :=
    inv_unique hMi' hM
  have htest : ∀ E : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), IsInt v E →
      IsInt v (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((p : ℕ) : v.adicCompletion ℚ) ^ e)⁻¹] * E *
        Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e]) →
      IsInt v (φ hvi * (K₁ * E * K₁i) * φ hv) := by
    intro E hE hE'
    set r := φ.symm (K₁ * E * K₁i) with hr
    have hφr : φ r = K₁ * E * K₁i := by rw [hr, RingEquiv.apply_symm_apply]
    have hrR : r ∈ Rv := by
      rw [hRv, hΛv, hΛv, map_mul, map_mul, hφr, eMi, hmv]
      refine ⟨(iK₁.mul hE).mul iK₁i, ?_⟩
      have e1 : K₂i * Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((p : ℕ) : v.adicCompletion ℚ) ^ e)⁻¹] * K₁i *
          (K₁ * E * K₁i) * (K₁ * Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e] * K₂) =
          K₂i * (Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((p : ℕ) : v.adicCompletion ℚ) ^ e)⁻¹] * (K₁i * K₁) * E *
            (K₁i * K₁) * Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e]) * K₂ := by
        simp only [Matrix.mul_assoc]
      rw [e1, hK₁', mul_one, mul_one]
      exact (iK₂i.mul hE').mul iK₂
    have h := (hΛv _).mp (hconj _ hrR)
    rwa [map_mul, map_mul, hφr] at h
  have key := core_matrix hp hpv he K₁ K₁i hK₁ hK₁' iK₁ iK₁i (φ hv) (φ hvi) hHHi hHiH hH1 hH2 hH4 htest
  rw [hΛv, map_mul, hmv, show φ hvi * (K₁ * Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e] * K₂) =
    (φ hvi * K₁ * Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e]) * K₂ by
      simp only [Matrix.mul_assoc]]
  exact key.mul iK₂

end Loc

section Main

variable {a b : ℚ}

local notation "𝔸ℍ" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" w => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w

theorem main (hab : a ≠ 0 ∧ b ≠ 0) {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (𝔸ℍ)ˣ)
    (hm₁ : ((m : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (CerednikDrinfeld.meetOrder Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    {h : (𝔸ℍ)ˣ}
    (hhT : h ∈ QuaternionAlgebra.primeHeckeSet Λ₁ ℓ)
    (hhR : h ∈ QuaternionAlgebra.primeHeckeSet (CerednikDrinfeld.meetOrder Λ₁ m) ℓ)
    (x : (𝔸ℍ)ˣ)
    (hoff : ¬ Submodule.ofFiniteIdele Λ₁ (x * m) ≤ Submodule.ofFiniteIdele Λ₁ (x * h)) :
    h ∈ CerednikDrinfeld.levelHeckeUSet Λ₁ (CerednikDrinfeld.meetOrder Λ₁ m) ℓ := by
  classical
  have hO₁ : QuaternionAlgebra.IsOrder Λ₁ := hΛ₁.isOrder
  haveI : Fact ℓ.Prime := ⟨hℓ⟩

  have c3 : ¬ CerednikDrinfeld.meetOrder Λ₁ m ≤ Submodule.conjByFiniteIdele Λ₁ h := by
    intro hle
    apply hoff

    suffices hbox : (((h⁻¹ * m : (𝔸ℍ)ˣ)) : 𝔸ℍ) ∈ Submodule.finiteAdeleBox Λ₁ by
      have := ofFiniteIdele_mul_le_of_mem_box hO₁ (x * h) (h⁻¹ * m) hbox
      rwa [show x * h * (h⁻¹ * m) = x * m by group] at this
    rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hO₁.fg hO₁.spanTop]

    let v₀ : HeightOneSpectrum (𝓞 ℚ) :=
      ⟨Ideal.span {(ℓ : 𝓞 ℚ)}, (Nat.isMaximal_span_natCast_of_prime hℓ).isPrime, Nat.span_natCast_ne_bot hℓ.ne_zero⟩
    have hℓv₀ : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v₀.asIdeal := Ideal.subset_span rfl

    obtain ⟨hT1, hT2, hT3, hT4⟩ := hhT
    have hm₁w := (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hO₁.fg hO₁.spanTop _).mp hm₁
    have hT1w := (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hO₁.fg hO₁.spanTop _).mp hT1
    have hT2w := (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hO₁.fg hO₁.spanTop _).mp hT2
    intro w
    rw [Units.val_mul, map_mul]
    by_cases hw : ((ℓ : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    ·
      obtain ⟨-, hframe⟩ :=
        QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
          hab hΛ₁ N m hm₁ hmN hRN
      obtain ⟨-, φ, hφ, hΛv, k₁, k₂, hk1, hk1i, hk2, hk2i, hmv⟩ := hframe w ℓ hℓ hw hℓN
      have he : 1 ≤ padicValNat ℓ N := one_le_padicValNat_of_dvd (NeZero.ne N) hℓN

      have h2 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ : ℕ) : w.adicCompletion ℚ)) * (ev w) ((h⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈
          Submodule.localBox Λ₁ w := by
        have := hT2w w
        rwa [map_smul, rat_smul_eq_one_tmul_mul, map_natCast] at this
      have h4 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((ℓ : ℕ) : w.adicCompletion ℚ)⁻¹) * (ev w) (h : 𝔸ℍ) ∉
          Submodule.localBox Λ₁ w := by
        intro hmem
        apply hT4
        rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hO₁.fg hO₁.spanTop]
        intro w'
        rw [map_smul, rat_smul_eq_one_tmul_mul, map_inv₀, map_natCast]
        by_cases hw' : ((ℓ : ℕ) : 𝓞 ℚ) ∈ w'.asIdeal
        · have heq : w' = w := Nat.HeightOneSpectrum.eq_of_natCast_prime_mem hℓ hw' hw
          subst heq; exact hmem
        · refine HeckeLocal.tmul_one_mul_mem_localBox w' ?_ (hT1w w')
          have := Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hℓ.ne_zero
            (fun hm => hw' ((Nat.mem_placesOf_iff hℓ.ne_zero w').mp hm))
          rwa [map_inv₀, map_natCast] at this

      have hRo : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder Λ₁ m) :=
        hO₁.inf (QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ₁ hO₁ m)
      have hconj : ∀ r ∈ Submodule.localBox (CerednikDrinfeld.meetOrder Λ₁ m) w,
          (ev w) ((h⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * r * (ev w) (h : 𝔸ℍ) ∈ Submodule.localBox Λ₁ w := by
        intro r hr
        have hr' := localBox_mono' hle w hr
        rw [Submodule.mem_localBox_conjByFiniteIdele_iff Λ₁ hO₁.fg hO₁.spanTop h w r] at hr'
        obtain ⟨y, hy, rfl⟩ := hr'
        have e1 : (ev w) ((h⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (ev w) (h : 𝔸ℍ) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
        rw [show ∀ A B Y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ, B * (A * Y * B) * A = (B * A) * Y * (B * A) from
          fun A B Y => by simp only [mul_assoc], e1, one_mul, mul_one]
        exact hy
      exact local_step hℓ hw he φ hφ (Submodule.localBox Λ₁ w) (Submodule.localBox (CerednikDrinfeld.meetOrder Λ₁ m) w)
        (fun z => hΛv z) (k₁ : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
        ((k₁⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
        (k₂ : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
        ((k₂⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
        (Units.mul_inv k₁) (Units.inv_mul k₁) (Units.mul_inv k₂) hk1 hk1i hk2 hk2i
        ((ev w) (m : 𝔸ℍ)) ((ev w) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) (by rw [← map_mul, Units.inv_mul, map_one]) hmv
        (fun z => mem_localBox_meetOrder_iff hO₁ m w z)
        ((ev w) (h : 𝔸ℍ)) ((ev w) ((h⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ))
        (by rw [← map_mul, Units.mul_inv, map_one]) (by rw [← map_mul, Units.inv_mul, map_one])
        (hT1w w) h2 h4 hconj
    ·
      have hint : algebraMap ℚ (w.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ :=
        Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hℓ.ne_zero
          (fun hm => hw ((Nat.mem_placesOf_iff hℓ.ne_zero w).mp hm))
      have hu := HeckeLocal.map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet ℓ ⟨hT1, hT2, hT3, hT4⟩ w hint
      have hinv : (ev w) ((h⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ Submodule.localBox Λ₁ w := by
        have := hu.2
        rwa [Units.coe_map_inv] at this
      exact HeckeLocal.localBox_mul_mem hO₁ w hinv (hm₁w w)
  refine ⟨hhR, ?_, c3⟩

  intro heq
  apply c3
  calc CerednikDrinfeld.meetOrder Λ₁ m = Submodule.conjByFiniteIdele (CerednikDrinfeld.meetOrder Λ₁ m) h := heq.symm
    _ ≤ Submodule.conjByFiniteIdele Λ₁ h := conjByFiniteIdele_mono inf_le_left h

end Main

section MatFwd

variable {v : HeightOneSpectrum (𝓞 ℚ)}

local notation "K" => v.adicCompletion ℚ
local notation "O" => v.adicCompletionIntegers ℚ
local notation "M2" => Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)

theorem IsInt.add {A B : M2} (hA : IsInt v A) (hB : IsInt v B) : IsInt v (A + B) := by
  intro i j
  rw [Matrix.add_apply]
  exact add_mem (hA i j) (hB i j)

theorem IsInt.sub {A B : M2} (hA : IsInt v A) (hB : IsInt v B) : IsInt v (A - B) := by
  intro i j
  rw [Matrix.sub_apply]
  exact sub_mem (hA i j) (hB i j)

theorem isInt_S {c : K} (hc : c ∈ O) : IsInt v (S c) :=
  isInt_of_entries hc (zero_mem _) (zero_mem _) hc

theorem isInt_conj_of_isInt_inv_mul_diagonal {d : K} (hd : d ≠ 0)
    (G Gi : M2) (hG : IsInt v G) (hGiG : Gi * G = 1)
    (hGiD : IsInt v (Gi * Matrix.diagonal ![(1 : K), d]))
    (Y : M2) (hY : IsInt v Y)
    (hYD : IsInt v (Matrix.diagonal ![(1 : K), d⁻¹] * Y * Matrix.diagonal ![(1 : K), d])) :
    IsInt v (Gi * Y * G) := by
  set c : K := Y 1 1 with hcdef
  have hc : c ∈ O := hY 1 1

  have h10 : d⁻¹ * Y 1 0 ∈ O := by
    have := hYD 1 0
    rw [diag_eq, diag_eq, Matrix.eta_fin_two Y, Matrix.mul_fin_two, Matrix.mul_fin_two] at this
    simpa using this

  have hint : IsInt v (Matrix.diagonal ![(1 : K), d⁻¹] * (Y - S c)) := by
    rw [diag_eq, Matrix.eta_fin_two Y]
    unfold S
    rw [show (!![Y 0 0, Y 0 1; Y 1 0, Y 1 1] : M2) - !![c, 0; 0, c] = !![Y 0 0 - c, Y 0 1; Y 1 0, Y 1 1 - c] by
      ext i j; fin_cases i <;> fin_cases j <;> simp, Matrix.mul_fin_two]
    refine isInt_of_entries ?_ ?_ ?_ ?_
    · simpa using sub_mem (hY 0 0) hc
    · simpa using hY 0 1
    · simpa using h10
    · simp [hcdef]
  have hDDi : Matrix.diagonal ![(1 : K), d] * Matrix.diagonal ![(1 : K), d⁻¹] = 1 := diag_inv d hd
  have e1 : Gi * Y * G = (Gi * Matrix.diagonal ![(1 : K), d]) * (Matrix.diagonal ![(1 : K), d⁻¹] * (Y - S c)) * G +
      S c := by
    have e2 : Gi * Y * G = Gi * (Y - S c) * G + Gi * S c * G := by noncomm_ring
    have e3 : Gi * S c * G = S c := by rw [Matrix.mul_assoc, S_comm, ← Matrix.mul_assoc, hGiG, Matrix.one_mul]
    rw [e2, e3]
    congr 1
    calc Gi * (Y - S c) * G = Gi * 1 * (Y - S c) * G := by rw [Matrix.mul_one]
      _ = _ := by rw [← hDDi]; simp only [Matrix.mul_assoc]
  rw [e1]
  exact ((hGiD.mul hint).mul hG).add (isInt_S hc)

end MatFwd

section LocFwd

variable {a b : ℚ} {v : HeightOneSpectrum (𝓞 ℚ)} {p : ℕ}

theorem local_step_fwd (hp : p.Prime) {e : ℕ}
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (Λv Rv : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))
    (hΛv : ∀ z, z ∈ Λv ↔ IsInt v (φ z))
    (K₁ K₁i K₂ K₂i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hK₁ : K₁ * K₁i = 1) (hK₁' : K₁i * K₁ = 1) (hK₂ : K₂ * K₂i = 1) (hK₂' : K₂i * K₂ = 1)
    (iK₁ : IsInt v K₁) (iK₁i : IsInt v K₁i) (iK₂ : IsInt v K₂) (iK₂i : IsInt v K₂i)
    (mv mvi : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (hmm' : mvi * mv = 1) (hm'm : mv * mvi = 1)
    (hmv : φ mv = K₁ * Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e] * K₂)
    (hRv : ∀ z, z ∈ Rv ↔ z ∈ Λv ∧ mvi * z * mv ∈ Λv)
    (hv hvi : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (hhh : hv * hvi = 1) (hhh' : hvi * hv = 1)
    (h1 : hv ∈ Λv) (hstep : hvi * mv ∈ Λv) :
    ∀ r ∈ Rv, hvi * r * hv ∈ Λv := by
  intro r hr
  have hp0 : ((p : ℕ) : v.adicCompletion ℚ) ≠ 0 := natCast_ne_zero_adicCompletion hp.ne_zero v
  have hpe0 : ((p : ℕ) : v.adicCompletion ℚ) ^ e ≠ 0 := pow_ne_zero _ hp0
  set D : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
    Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((p : ℕ) : v.adicCompletion ℚ) ^ e] with hD
  set Di : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) :=
    Matrix.diagonal ![(1 : v.adicCompletion ℚ), (((p : ℕ) : v.adicCompletion ℚ) ^ e)⁻¹] with hDi
  have hDDi : D * Di = 1 := diag_inv _ hpe0
  have hDiD : Di * D = 1 := by
    rw [hD, hDi, diag_eq, diag_eq, Matrix.mul_fin_two, Matrix.one_fin_two]
    exact mat_eq (by fsr) (by fsr) (by simp) (by fsr)
  have hHHi : φ hv * φ hvi = 1 := by rw [← map_mul, hhh, map_one]
  have hHiH : φ hvi * φ hv = 1 := by rw [← map_mul, hhh', map_one]
  have hH1 : IsInt v (φ hv) := (hΛv _).mp h1

  have hM : φ mv * (K₂i * Di * K₁i) = 1 := by
    rw [hmv]
    calc K₁ * D * K₂ * (K₂i * Di * K₁i) = K₁ * (D * (K₂ * K₂i) * Di) * K₁i := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hK₂, Matrix.mul_one, hDDi, Matrix.mul_one, hK₁]
  have hMi : φ mvi = K₂i * Di * K₁i := by
    have h1' : φ mvi * φ mv = 1 := by rw [← map_mul, hmm', map_one]
    exact inv_unique h1' hM

  have hGiG : (φ hvi * K₁) * (K₁i * φ hv) = 1 := by
    rw [show φ hvi * K₁ * (K₁i * φ hv) = φ hvi * (K₁ * K₁i) * φ hv by simp only [Matrix.mul_assoc], hK₁,
      Matrix.mul_one, hHiH]
  have hG : IsInt v (K₁i * φ hv) := iK₁i.mul hH1
  have hGiD : IsInt v (φ hvi * K₁ * D) := by
    have hs := (hΛv _).mp hstep
    rw [map_mul, hmv] at hs
    have : φ hvi * K₁ * D = φ hvi * (K₁ * D * K₂) * K₂i := by
      rw [show φ hvi * (K₁ * D * K₂) * K₂i = φ hvi * K₁ * D * (K₂ * K₂i) by simp only [Matrix.mul_assoc], hK₂,
        Matrix.mul_one]
    rw [this]
    exact hs.mul iK₂i

  obtain ⟨hrΛ, hrm⟩ := (hRv r).mp hr
  have hY : IsInt v (K₁i * φ r * K₁) := (iK₁i.mul ((hΛv _).mp hrΛ)).mul iK₁
  have hYD : IsInt v (Di * (K₁i * φ r * K₁) * D) := by
    have h2 := (hΛv _).mp hrm
    rw [map_mul, map_mul, hMi, hmv] at h2

    have e1 : K₂i * Di * K₁i * φ r * (K₁ * D * K₂) = K₂i * (Di * (K₁i * φ r * K₁) * D) * K₂ := by
      simp only [Matrix.mul_assoc]
    rw [e1] at h2
    exact (isInt_conj_iff iK₂ iK₂i hK₂ _).mp h2
  have key := isInt_conj_of_isInt_inv_mul_diagonal hpe0 (K₁i * φ hv) (φ hvi * K₁) hG hGiG hGiD
    (K₁i * φ r * K₁) hY hYD
  rw [hΛv, map_mul, map_mul]
  have e2 : φ hvi * K₁ * (K₁i * φ r * K₁) * (K₁i * φ hv) = φ hvi * (K₁ * K₁i) * φ r * (K₁ * K₁i) * φ hv := by
    simp only [Matrix.mul_assoc]
  rw [e2, hK₁, Matrix.mul_one, Matrix.mul_one] at key
  exact key

end LocFwd

section MainL2

variable {a b : ℚ}

local notation "𝔸ℍ" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" w => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w

theorem mem_finiteAdeleBox_of_ofFiniteIdele_le {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {g g' : (𝔸ℍ)ˣ} (h : Submodule.ofFiniteIdele Λ g ≤ Submodule.ofFiniteIdele Λ g') :
    ((g'⁻¹ * g : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ Submodule.finiteAdeleBox Λ := by
  have hb := HeckeLocal.box_mono h
  rw [Submodule.finiteAdeleBox_ofFiniteIdele Λ hΛ.fg hΛ.spanTop g,
    Submodule.finiteAdeleBox_ofFiniteIdele Λ hΛ.fg hΛ.spanTop g'] at hb
  have h1 : (g : 𝔸ℍ) ∈ (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft (g : 𝔸ℍ)) :=
    ⟨1, HeckeLocal.one_mem_box hΛ, by rw [AddMonoidHom.coe_mulLeft, mul_one]⟩
  obtain ⟨w, hw, hwg⟩ := hb h1
  rw [AddMonoidHom.coe_mulLeft] at hwg
  have : ((g'⁻¹ * g : (𝔸ℍ)ˣ) : 𝔸ℍ) = w := by
    rw [Units.val_mul, ← hwg, ← mul_assoc, Units.inv_mul, one_mul]
  rw [this]; exact hw

theorem mainL2 (hab : a ≠ 0 ∧ b ≠ 0) {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (𝔸ℍ)ˣ)
    (hm₁ : ((m : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (CerednikDrinfeld.meetOrder Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    {h : (𝔸ℍ)ˣ}
    (hh : h ∈ CerednikDrinfeld.levelHeckeUSet Λ₁ (CerednikDrinfeld.meetOrder Λ₁ m) ℓ)
    (x : (𝔸ℍ)ˣ) :
    ¬ Submodule.ofFiniteIdele Λ₁ (x * m) ≤ Submodule.ofFiniteIdele Λ₁ (x * h) := by
  classical
  intro hle
  have hO₁ : QuaternionAlgebra.IsOrder Λ₁ := hΛ₁.isOrder
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨hhR, -, hc3⟩ := hh
  apply hc3
  have hRo : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder Λ₁ m) :=
    hO₁.inf (QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ₁ hO₁ m)
  have hRle : CerednikDrinfeld.meetOrder Λ₁ m ≤ Λ₁ := inf_le_left

  have hbox : ((h⁻¹ * m : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ Submodule.finiteAdeleBox Λ₁ := by
    have := mem_finiteAdeleBox_of_ofFiniteIdele_le hO₁ hle
    rwa [show (x * h)⁻¹ * (x * m) = h⁻¹ * m by group] at this
  have hboxw := (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hO₁.fg hO₁.spanTop _).mp hbox

  obtain ⟨hR1, hR2, hR3, hR4⟩ := hhR
  have hT1 : (h : 𝔸ℍ) ∈ Submodule.finiteAdeleBox Λ₁ := HeckeLocal.box_mono hRle hR1
  have hT1w := (Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hO₁.fg hO₁.spanTop _).mp hT1

  intro z hz
  rw [mem_conjByFiniteIdele_iff' Λ₁ h z,
    Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ₁ hO₁.fg hO₁.spanTop]
  intro w
  rw [map_mul, map_mul]
  have hzw : (ev w) (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈
      Submodule.localBox (CerednikDrinfeld.meetOrder Λ₁ m) w := by
    have := HeckeLocal.tmul_one_mem_localBox hz w
    convert this using 1
    rfl
  by_cases hw : ((ℓ : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
  ·
    obtain ⟨-, hframe⟩ :=
      QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
        hab hΛ₁ N m hm₁ hmN hRN
    obtain ⟨-, φ, hφ, hΛv, k₁, k₂, hk1, hk1i, hk2, hk2i, hmv⟩ := hframe w ℓ hℓ hw hℓN
    have hstep : (ev w) ((h⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) * (ev w) (m : 𝔸ℍ) ∈ Submodule.localBox Λ₁ w := by
      have := hboxw w
      rwa [Units.val_mul, map_mul] at this
    exact local_step_fwd hℓ φ (Submodule.localBox Λ₁ w) (Submodule.localBox (CerednikDrinfeld.meetOrder Λ₁ m) w)
      (fun z => hΛv z) (k₁ : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
      ((k₁⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
      (k₂ : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
      ((k₂⁻¹ : GL (Fin 2) (w.adicCompletion ℚ)) : Matrix (Fin 2) (Fin 2) (w.adicCompletion ℚ))
      (Units.mul_inv k₁) (Units.inv_mul k₁) (Units.mul_inv k₂) (Units.inv_mul k₂) hk1 hk1i hk2 hk2i
      ((ev w) (m : 𝔸ℍ)) ((ev w) ((m⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ)) (by rw [← map_mul, Units.inv_mul, map_one])
      (by rw [← map_mul, Units.mul_inv, map_one]) hmv
      (fun z => mem_localBox_meetOrder_iff hO₁ m w z)
      ((ev w) (h : 𝔸ℍ)) ((ev w) ((h⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ))
      (by rw [← map_mul, Units.mul_inv, map_one]) (by rw [← map_mul, Units.inv_mul, map_one])
      (hT1w w) hstep _ hzw
  ·
    have hint : algebraMap ℚ (w.adicCompletion ℚ) ((ℓ : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ :=
      Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hℓ.ne_zero
        (fun hm => hw ((Nat.mem_placesOf_iff hℓ.ne_zero w).mp hm))
    have hu := HeckeLocal.map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet ℓ ⟨hR1, hR2, hR3, hR4⟩ w hint
    rw [Submodule.mem_localBoxUnits_iff] at hu
    have hinv : (ev w) ((h⁻¹ : (𝔸ℍ)ˣ) : 𝔸ℍ) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder Λ₁ m) w := by
      have := hu.2
      rwa [Units.coe_map_inv] at this
    have hvR : (ev w) (h : 𝔸ℍ) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder Λ₁ m) w := by
      have := hu.1
      exact this
    exact localBox_mono' hRle w
      (HeckeLocal.localBox_mul_mem hRo w (HeckeLocal.localBox_mul_mem hRo w hinv hzw) hvR)

end MainL2

end LevelU4
p2m_reactivate "P2MW.S_CerednikDrinfeld_LevelU_not_le_of_mem_levelHeckeUSet.LevelU4"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_LevelU_not_le_of_mem_levelHeckeUSet.LevelU4"

open LevelU4 in
theorem solution
    {a b : ℚ} (hab : a ≠ 0 ∧ b ≠ 0) {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : QuaternionAlgebra.IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N]
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (CerednikDrinfeld.meetOrder Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ℓ ∣ N)
    {h : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hh : h ∈ CerednikDrinfeld.levelHeckeUSet Λ₁ (CerednikDrinfeld.meetOrder Λ₁ m) ℓ)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    ¬ Submodule.ofFiniteIdele Λ₁ (x * m) ≤ Submodule.ofFiniteIdele Λ₁ (x * h) :=
  mainL2 hab hΛ₁ N m hm₁ hmN hRN hℓ hℓN hh x

end S_CerednikDrinfeld_LevelU_not_le_of_mem_levelHeckeUSet
end P2MW
export P2MW.S_CerednikDrinfeld_LevelU_not_le_of_mem_levelHeckeUSet (solution)
