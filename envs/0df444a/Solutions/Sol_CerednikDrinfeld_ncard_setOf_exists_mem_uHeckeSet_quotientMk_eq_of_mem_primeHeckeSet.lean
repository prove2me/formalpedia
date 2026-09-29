-- Prove2me | solution 1 for CerednikDrinfeld.ncard_setOf_exists_mem_uHeckeSet_quotientMk_eq_of_mem_primeHeckeSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/897bc962-6b02-5bb2-8900-4edb062120dc

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_Order_FiniteIdele
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_CerednikDrinfeld_ncard_setOf_quotientMk_stabilizer_localBox_meetOrder_eq_of_mem_primeHeckeSet
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_ncard_setOf_exists_mem_uHeckeSet_quotientMk_eq_of_mem_primeHeckeSet
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace Nat
p2m_export "Nat" "prime_iff card_eq_fintype_card count coe_castRingHom cast_smul_eq_nsmul Coprime choose Prime prime_iff_prime_int isCoprime_iff_coprime eq_zero_or_pos cast_mul card_fin cast_zero castRingHom zero"
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

private theorem _root_.HeckeLocal.mem_stabilizer_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (u : (ℍ𝔸)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      (u : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox Λ :=
  ⟨fun hu => ⟨coe_mem_box_of_mem_stabilizer hΛ hu, coe_inv_mem_box_of_mem_stabilizer hΛ hu⟩,
   fun h => mem_stabilizer_of_coe_mem_of_coe_inv_mem hΛ h.1 h.2⟩

p2m_export "HeckeLocal" "mem_stabilizer_iff"

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

section LiftedSlice
open scoped TensorProduct
open IsDedekindDomain NumberField

noncomputable section

namespace AdelicSlice

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "HOS" => HeightOneSpectrum (𝓞 ℚ)

def s1_Zhat : Subring 𝔸f where
  carrier := {a | ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ}
  mul_mem' := fun {a b} ha hb v => by
    show (a * b) v ∈ _
    have : (a * b) v = a v * b v := rfl
    rw [this]; exact mul_mem (ha v) (hb v)
  one_mem' := fun v => by
    have : (1 : 𝔸f) v = 1 := rfl
    rw [this]; exact one_mem _
  add_mem' := fun {a b} ha hb v => by
    have : (a + b) v = a v + b v := rfl
    rw [this]; exact add_mem (ha v) (hb v)
  zero_mem' := fun v => by
    have : (0 : 𝔸f) v = 0 := rfl
    rw [this]; exact zero_mem _
  neg_mem' := fun {a} ha v => by
    have : (-a) v = -(a v) := rfl
    rw [this]; exact neg_mem (ha v)

theorem s1_mem_Zhat_iff (a : 𝔸f) : a ∈ s1_Zhat ↔ ∀ v : HOS, a v ∈ v.adicCompletionIntegers ℚ :=
  Iff.rfl

theorem s1_valued_algebraMap_apply (q : ℚ) (v : HOS) :
    Valued.v ((algebraMap ℚ 𝔸f q) v) = v.valuation ℚ q := by
  have h : (algebraMap ℚ 𝔸f q) v = ((WithVal.equiv (v.valuation ℚ)).symm q : v.adicCompletion ℚ) := rfl
  rw [h]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q

theorem s1_algebraMap_apply_mem_integers_iff (q : ℚ) (v : HOS) :
    (algebraMap ℚ 𝔸f q) v ∈ v.adicCompletionIntegers ℚ ↔ v.valuation ℚ q ≤ 1 := by
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, s1_valued_algebraMap_apply]

theorem s1_valuation_intCast_le_one (v : HOS) (m : ℤ) : v.valuation ℚ (m : ℚ) ≤ 1 := by
  have h : v.valuation ℚ (algebraMap (𝓞 ℚ) ℚ (m : 𝓞 ℚ)) ≤ 1 :=
    IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := ℚ) v (m : 𝓞 ℚ)
  rwa [map_intCast] at h

theorem s1_valuation_natCast_le_one (v : HOS) (n : ℕ) : v.valuation ℚ (n : ℚ) ≤ 1 := by
  have h := s1_valuation_intCast_le_one v (n : ℤ)
  rwa [Int.cast_natCast] at h

theorem s1_algebraMap_intCast_mem_Zhat (m : ℤ) : algebraMap ℚ 𝔸f (m : ℚ) ∈ s1_Zhat := fun v =>
  (s1_algebraMap_apply_mem_integers_iff _ v).mpr (s1_valuation_intCast_le_one v m)

theorem s1_exists_intCast_eq (r : 𝓞 ℚ) : ∃ m : ℤ, ((r : ℚ)) = (m : ℚ) := by
  refine ⟨Rat.ringOfIntegersEquiv r, ?_⟩
  have h0 := Rat.ringOfIntegersEquiv.symm_apply_apply r
  rw [eq_intCast Rat.ringOfIntegersEquiv.symm (Rat.ringOfIntegersEquiv r)] at h0
  calc (r : ℚ) = algebraMap (𝓞 ℚ) ℚ r := rfl
    _ = algebraMap (𝓞 ℚ) ℚ ((Rat.ringOfIntegersEquiv r : ℤ) : 𝓞 ℚ) := by rw [h0]
    _ = ((Rat.ringOfIntegersEquiv r : ℤ) : ℚ) := map_intCast _ _

theorem s1_exists_intCast_of_forall_valuation_le_one (q : ℚ)
    (h : ∀ v : HOS, v.valuation ℚ q ≤ 1) : ∃ m : ℤ, q = (m : ℚ) := by
  obtain ⟨r, hr⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ q h
  obtain ⟨m, hm⟩ := s1_exists_intCast_eq r
  refine ⟨m, ?_⟩
  rw [← hm]
  exact hr.symm

section BoxGen

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s1_tmul_mem_finiteAdeleBox {Λ : Submodule ℤ K} {z : K} (hz : z ∈ Λ) {a : 𝔸f}
    (ha : a ∈ s1_Zhat) : z ⊗ₜ[ℚ] a ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨z, hz, a, ha, rfl⟩

theorem s1_finiteAdeleBox_le_iff {Λ : Submodule ℤ K} {H : AddSubgroup (K ⊗[ℚ] 𝔸f)} :
    Submodule.finiteAdeleBox Λ ≤ H ↔ ∀ z ∈ Λ, ∀ a : 𝔸f, a ∈ s1_Zhat → z ⊗ₜ[ℚ] a ∈ H := by
  unfold Submodule.finiteAdeleBox
  rw [AddSubgroup.closure_le]
  constructor
  · intro h z hz a ha
    exact h ⟨z, hz, a, ha, rfl⟩
  · rintro h x ⟨z, hz, a, ha, rfl⟩
    exact h z hz a ha

end BoxGen

section Slice

variable {K : Type*} [Ring K] [Algebra ℚ K]

def s1_coord {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) : K ⊗[ℚ] 𝔸f →ₗ[ℚ] 𝔸f :=
  TensorProduct.lift ((LinearMap.lsmul ℚ 𝔸f).comp (b.coord i))

theorem s1_coord_tmul {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι) (z : K) (a : 𝔸f) :
    s1_coord b i (z ⊗ₜ[ℚ] a) = (b.repr z i) • a := by
  unfold s1_coord
  rw [TensorProduct.lift.tmul]
  rfl

theorem s1_coord_mem_Zhat_of_mem_finiteAdeleBox {ι : Type*} (b : Module.Basis ι ℚ K) (i : ι)
    {t : K ⊗[ℚ] 𝔸f} (ht : t ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))) :
    s1_coord b i t ∈ s1_Zhat := by
  have hle : Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ≤ (s1_Zhat.toAddSubgroup).comap (s1_coord b i).toAddMonoidHom := by
    rw [s1_finiteAdeleBox_le_iff]
    intro z hz a ha
    rw [AddSubgroup.mem_comap]
    show s1_coord b i (z ⊗ₜ[ℚ] a) ∈ s1_Zhat
    rw [s1_coord_tmul]
    obtain ⟨m, hm⟩ := (Module.Basis.mem_span_iff_repr_mem ℤ b z).mp hz i
    rw [← hm, Algebra.smul_def]
    refine mul_mem ?_ ha
    have : (algebraMap ℤ ℚ m) = ((m : ℤ) : ℚ) := by rw [algebraMap_int_eq, Int.coe_castRingHom]
    rw [this]
    exact s1_algebraMap_intCast_mem_Zhat m
  exact hle ht

theorem s1_tmul_one_mem_finiteAdeleBox_iff {ι : Type*} [Fintype ι] (b : Module.Basis ι ℚ K) (z : K) :
    z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox (Submodule.span ℤ (Set.range b))
      ↔ z ∈ Submodule.span ℤ (Set.range b) := by
  constructor
  · intro hz
    rw [Module.Basis.mem_span_iff_repr_mem ℤ b z]
    intro i
    have hc := s1_coord_mem_Zhat_of_mem_finiteAdeleBox b i hz
    rw [s1_coord_tmul, Algebra.smul_def, mul_one] at hc
    have hval : ∀ v : HOS, v.valuation ℚ (b.repr z i) ≤ 1 := fun v =>
      (s1_algebraMap_apply_mem_integers_iff _ v).mp (hc v)
    obtain ⟨m, hm⟩ := s1_exists_intCast_of_forall_valuation_le_one _ hval
    refine ⟨m, ?_⟩
    rw [hm, algebraMap_int_eq, Int.coe_castRingHom]
  · intro hz
    exact s1_tmul_mem_finiteAdeleBox hz (one_mem _)

end Slice

section LatticeBasis

variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s1_exists_basis_of_isLattice (M : Submodule ℤ K) [Submodule.IsLattice ℚ M] :
    ∃ (n : ℕ) (bM : Module.Basis (Fin n) ℚ K), Submodule.span ℤ (Set.range bM) = M := by
  classical
  haveI : Module.Finite ℤ ↥M := Submodule.IsLattice.finite ℚ _
  haveI : Module.Free ℤ ↥M := Submodule.IsLattice.free ℚ _
  let n := Module.finrank ℤ ↥M
  let bZ : Module.Basis (Fin n) ℤ ↥M := Module.finBasis ℤ ↥M
  refine ⟨n, bZ.extendOfIsLattice ℚ, ?_⟩
  have hrange : Set.range (bZ.extendOfIsLattice ℚ) = M.subtype '' Set.range bZ := by
    ext x
    simp only [Set.mem_range, Module.Basis.extendOfIsLattice_apply, Set.mem_image,
      Submodule.coe_subtype]
    exact ⟨fun ⟨k, hk⟩ => ⟨bZ k, ⟨k, rfl⟩, hk⟩, fun ⟨y, ⟨k, hk⟩, hy⟩ => ⟨k, by rw [hk]; exact hy⟩⟩
  rw [hrange, ← Submodule.map_span, bZ.span_eq, Submodule.map_top, Submodule.range_subtype]

end LatticeBasis

section FG
variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s3_fg_of_le {M N : Submodule ℤ K} [Submodule.IsLattice ℚ N] (hle : M ≤ N) : M.FG := by
  haveI : IsNoetherian ℤ ↥N := isNoetherian_of_fg_of_noetherian _ (Submodule.IsLattice.fg (A := ℚ))
  have hrw : M = Submodule.map N.subtype (Submodule.comap N.subtype M) := by
    rw [Submodule.map_comap_subtype]; exact (inf_of_le_right hle).symm
  rw [hrw]; exact (IsNoetherian.noetherian _).map _
end FG

section Multiplier
variable {K : Type*} [Ring K] [Algebra ℚ K]

theorem s3_exists_natCast_smul_mem (Λ : Submodule ℤ K) [Submodule.IsLattice ℚ Λ] (z : K) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : ℚ) • z ∈ Λ := by
  classical
  obtain ⟨m, b, hb⟩ := s1_exists_basis_of_isLattice Λ

  refine ⟨∏ i, (b.repr z i).den, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => (b.repr z i).den_nz
  · rw [← hb, Module.Basis.mem_span_iff_repr_mem ℤ b]
    intro i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    have hdvd : ((b.repr z i).den : ℤ) ∣ ((∏ j, (b.repr z j).den : ℕ) : ℤ) := by
      exact_mod_cast Finset.dvd_prod_of_mem (fun j => (b.repr z j).den) (Finset.mem_univ i)
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k * (b.repr z i).num, ?_⟩
    show ((k * (b.repr z i).num : ℤ) : ℚ) = ((∏ j, (b.repr z j).den : ℕ) : ℚ) * b.repr z i
    have hq : ((b.repr z i).den : ℚ) * (b.repr z i) = (b.repr z i).num := by
      rw [mul_comm]; exact Rat.mul_den_eq_num (b.repr z i)
    have hk' : ((∏ j, (b.repr z j).den : ℕ) : ℚ) = ((b.repr z i).den : ℚ) * (k : ℚ) := by
      exact_mod_cast hk
    rw [hk', mul_comm ((b.repr z i).den : ℚ) (k : ℚ), mul_assoc, hq, Int.cast_mul]

end Multiplier

section ConjBox

variable {K : Type*} [Ring K] [Algebra ℚ K]

abbrev q15_cj (g : (K ⊗[ℚ] 𝔸f)ˣ) : (K ⊗[ℚ] 𝔸f) →+ (K ⊗[ℚ] 𝔸f) :=
  (AddMonoidHom.mulRight ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f)).comp (AddMonoidHom.mulLeft (g : K ⊗[ℚ] 𝔸f))

theorem q15_cj_apply (g : (K ⊗[ℚ] 𝔸f)ˣ) (t : K ⊗[ℚ] 𝔸f) :
    (q15_cj g) t = (g : K ⊗[ℚ] 𝔸f) * t * ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) := by
  rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]

theorem q15_mem_conj_iff_exists (Λ : Submodule ℤ K) (g : (K ⊗[ℚ] 𝔸f)ˣ) (z : K) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      ∃ u ∈ Submodule.finiteAdeleBox Λ,
        (g : K ⊗[ℚ] 𝔸f) * u * ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) = z ⊗ₜ[ℚ] (1 : 𝔸f) := by
  show z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ (Submodule.finiteAdeleBox Λ).map (q15_cj g) ↔ _
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨u, hu, h⟩; exact ⟨u, hu, by rw [← q15_cj_apply]; exact h⟩
  · rintro ⟨u, hu, h⟩; exact ⟨u, hu, by rw [q15_cj_apply]; exact h⟩

theorem q15_mem_conj_iff_conj_mem (Λ : Submodule ℤ K) (g : (K ⊗[ℚ] 𝔸f)ˣ) (z : K) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) * (g : K ⊗[ℚ] 𝔸f)
        ∈ Submodule.finiteAdeleBox Λ := by
  rw [q15_mem_conj_iff_exists]
  constructor
  · rintro ⟨u, hu, h⟩
    have : ((g⁻¹ : (K ⊗[ℚ] 𝔸f)ˣ) : K ⊗[ℚ] 𝔸f) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) * (g : K ⊗[ℚ] 𝔸f) = u := by
      rw [← h, ← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact hu
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

end ConjBox

end AdelicSlice

end

noncomputable section

namespace STAB

open AdelicSlice

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

theorem isLattice_of_isOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) :
    Submodule.IsLattice ℚ Λ := ⟨hΛ.fg, hΛ.spanTop⟩

theorem tmul_one_mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (z : ℍ[ℚ, a, b]) :
    z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ ↔ z ∈ Λ := by
  haveI := isLattice_of_isOrder hΛ
  obtain ⟨n, bΛ, hb⟩ := s1_exists_basis_of_isLattice Λ
  rw [← hb]
  exact s1_tmul_one_mem_finiteAdeleBox_iff bΛ z

theorem conj_mul {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (g g' : (ℍ𝔸)ˣ) :
    Submodule.conjByFiniteIdele Λ (g * g') = Submodule.conjByFiniteIdele (Submodule.conjByFiniteIdele Λ g') g := by
  ext z
  rw [q15_mem_conj_iff_conj_mem, q15_mem_conj_iff_exists,
    Submodule.finiteAdeleBox_conjByFiniteIdele Λ hΛ.fg hΛ.spanTop g']
  set t : ℍ𝔸 := z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) with ht
  constructor
  · intro h
    refine ⟨((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * (g : ℍ𝔸), ?_, ?_⟩
    · refine ⟨(((g * g')⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * ((g * g' : (ℍ𝔸)ˣ) : ℍ𝔸), h, ?_⟩
      rw [mul_inv_rev, Units.val_mul, Units.val_mul]
      show (g' : ℍ𝔸) * (((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * ((g : ℍ𝔸) * (g' : ℍ𝔸))) *
          ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * (g : ℍ𝔸)
      rw [show (g' : ℍ𝔸) * (((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * ((g : ℍ𝔸) * (g' : ℍ𝔸))) *
          ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((g' : ℍ𝔸) * ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * (g : ℍ𝔸)) *
          ((g' : ℍ𝔸) * ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) by noncomm_ring]
      rw [Units.mul_inv, one_mul, mul_one]
    · rw [show (g : ℍ𝔸) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * (g : ℍ𝔸)) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
          ((g : ℍ𝔸) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * t * ((g : ℍ𝔸) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) by noncomm_ring]
      rw [Units.mul_inv, one_mul, mul_one]
  · rintro ⟨u, ⟨w, hw, rfl⟩, hu⟩
    rw [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight] at hu

    have : (((g * g')⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * t * ((g * g' : (ℍ𝔸)ˣ) : ℍ𝔸) = w := by
      rw [← hu, mul_inv_rev, Units.val_mul, Units.val_mul]
      rw [show ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((g : ℍ𝔸) * ((g' : ℍ𝔸) * w * ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) *
          ((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * ((g : ℍ𝔸) * (g' : ℍ𝔸)) =
          ((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (g : ℍ𝔸)) * (g' : ℍ𝔸) * w *
            (((g'⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((g⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (g : ℍ𝔸)) * (g' : ℍ𝔸)) by noncomm_ring]
      rw [Units.inv_mul, mul_one, Units.inv_mul, one_mul, mul_one]
    rw [this]; exact hw

end STAB

end

end LiftedSlice

open QuaternionAlgebra CerednikDrinfeld

namespace F3Kit

variable {a b : ℚ}

theorem mul_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {u w : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hu : u ∈ Submodule.localBoxUnits Λ v) (hw : w ∈ Submodule.localBoxUnits Λ v) :
    u * w ∈ Submodule.localBoxUnits Λ v := by
  rw [Submodule.mem_localBoxUnits_iff] at hu hw ⊢
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]; exact HeckeLocal.localBox_mul_mem hΛ v hu.1 hw.1
  · rw [mul_inv_rev, Units.val_mul]; exact HeckeLocal.localBox_mul_mem hΛ v hw.2 hu.2

theorem inv_mem_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (v : HeightOneSpectrum (𝓞 ℚ))
    {u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ} (hu : u ∈ Submodule.localBoxUnits Λ v) : u⁻¹ ∈ Submodule.localBoxUnits Λ v := by
  rw [Submodule.mem_localBoxUnits_iff] at hu ⊢
  rw [inv_inv]; exact ⟨hu.2, hu.1⟩

theorem coe_eq_coe_iff_map_inv_mul_mem_localBoxUnits
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {h h' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hh : h ∈ primeHeckeSet Λ ℓ) (hh' : h' ∈ primeHeckeSet Λ ℓ) :
    ((h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) = (h' : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer Λ) ↔
      (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h)⁻¹ *
          Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h' ∈ Submodule.localBoxUnits Λ v := by
  rw [QuotientGroup.eq, QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ]
  constructor
  · intro H
    have := H v
    rwa [map_mul, map_inv] at this
  · intro H w
    rw [map_mul, map_inv]
    by_cases hw : ((ℓ : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    · have : w = v := Nat.HeightOneSpectrum.eq_of_natCast_prime_mem hℓ hw hv
      subst this; exact H
    · have hwq : w ∉ Nat.placesOf ℓ := by rwa [Nat.mem_placesOf_iff hℓ.ne_zero]
      have hint := Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hℓ.ne_zero hwq
      exact mul_mem_localBoxUnits hΛ w
        (inv_mem_localBoxUnits w (HeckeLocal.map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet ℓ hh w hint))
        (HeckeLocal.map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet ℓ hh' w hint)

end F3Kit

namespace F3Kit

section Reps

variable {a b : ℚ}

theorem ncard_cosetSet_eq_of_reps (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (T : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (m : ℕ)
    (r : Fin m → (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hrT : ∀ i, r i ∈ T)
    (hinj : ∀ i j, ((r i : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = (r j : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) → i = j)
    (hcov : ∀ h ∈ T, ∃ i, ((h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = (r i : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U)) :
    Set.ncard {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U | ∃ h ∈ T, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = c} = m := by
  classical
  have e : {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U | ∃ h ∈ T, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U) = c} = Set.range (fun i : Fin m => ((r i : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ U)) := by
    ext c
    constructor
    · rintro ⟨h, hh, rfl⟩
      obtain ⟨i, hi⟩ := hcov h hh
      exact ⟨i, hi.symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨r i, hrT i, rfl⟩
  rw [e, Set.ncard_range_of_injective, Nat.card_eq_fintype_card, Fintype.card_fin]
  intro i j hij
  exact hinj i j hij

end Reps

end F3Kit

namespace F3Kit

variable {a b : ℚ}

theorem mem_stabilizer_localBox_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) :
    u ∈ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ((Submodule.localBox Λ v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) ↔
      u ∈ Submodule.localBoxUnits Λ v := by
  rw [MulAction.mem_stabilizer_iff, Submodule.mem_localBoxUnits_iff]
  constructor
  · intro h
    have h1 : (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) * 1 ∈ u • ((Submodule.localBox Λ v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :=
      Set.smul_mem_smul_set (HeckeLocal.one_mem_localBox hΛ v)
    rw [h, mul_one] at h1
    have h2 : ((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) * 1 ∈ u⁻¹ • ((Submodule.localBox Λ v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :=
      Set.smul_mem_smul_set (HeckeLocal.one_mem_localBox hΛ v)
    rw [← h, smul_smul, inv_mul_cancel, one_smul, mul_one] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨hu, hui⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact HeckeLocal.localBox_mul_mem hΛ v hu hx
    · intro x hx
      refine ⟨((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) * x, HeckeLocal.localBox_mul_mem hΛ v hui hx, ?_⟩
      show (u : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) * (((u⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) * x) = x
      rw [← mul_assoc, Units.mul_inv, one_mul]

end F3Kit

namespace F3Kit

variable {a b : ℚ}

def LocPred (R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (q : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) (g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : Prop :=
  ((g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
      (q : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
      ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) ∉ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
      (q : ℚ)⁻¹ • (g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) ∉ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v) ∧
    (∀ x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ), ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) * x * g ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔
        x ∈ Submodule.localBox R v) ∧
    (¬ ∀ x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ), ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) * x * g ∈ Submodule.localBox R v ↔
        x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v)

theorem mem_localBox_conjByFiniteIdele_iff' {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (v : HeightOneSpectrum (𝓞 ℚ)) (x : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) :
    x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R m) v ↔
      (((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) * x *
        (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) ∈ Submodule.localBox R v := by
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff R hR.fg hR.spanTop m v x]
  set M : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ := Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom m with hM
  have hMv : (M : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) = Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) := rfl
  have hMi : ((M⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) = Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((m⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) := by
    rw [← map_inv]; rfl
  rw [← hMv, ← hMi]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem not_mem_localBox_of_not_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {q : ℕ} (hq : q.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) (hx : x ∉ Submodule.finiteAdeleBox Λ)
    (hgood : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ∉ Nat.placesOf q → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w x ∈ Submodule.localBox Λ w) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v x ∉ Submodule.localBox Λ v := by
  intro hxv
  apply hx
  rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop]
  intro w
  by_cases hw : ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
  · have : w = v := Nat.HeightOneSpectrum.eq_of_natCast_prime_mem hq hw hv
    subst this; exact hxv
  · exact hgood w (by rwa [Nat.mem_placesOf_iff hq.ne_zero])

theorem locPred_of_mem_uHeckeSet {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {q : ℕ} (hq : q.Prime) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hnH : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    (hS : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hh : h ∈ CerednikDrinfeld.uHeckeSet R n q) :
    LocPred R n q v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h) := by
  obtain ⟨hhP, hconj, hne⟩ := hh
  obtain ⟨h1, h2, h3, h4⟩ := hhP
  have hqne : q ≠ 0 := hq.ne_zero
  set g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ := Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom h with hg
  have hgv : (g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) = Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) := rfl
  have hgi : ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) = Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) := by rw [← map_inv]; rfl
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact HeckeLocal.finiteAdeleEvalAt_mem_localBox v h1
  · rw [hgi, ← map_smul]; exact HeckeLocal.finiteAdeleEvalAt_mem_localBox v h2
  · rw [hgi]
    refine not_mem_localBox_of_not_mem_box hS hq v hv _ h3 ?_
    intro w hw
    have := GOODEQ.unitsMap_mem_localBoxUnits_of_mem_primeHeckeSet hqne ⟨h1, h2, h3, h4⟩ hw
    rw [Submodule.mem_localBoxUnits_iff] at this
    have e := this.2
    rwa [← map_inv] at e
  · rw [hgv, ← map_smul]
    refine not_mem_localBox_of_not_mem_box hS hq v hv _ h4 ?_
    intro w hw
    rw [map_smul]
    exact GOODEQ.smul_mem_localBox w (Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hqne hw)
      (HeckeLocal.finiteAdeleEvalAt_mem_localBox w h1)
  ·
    intro x
    have hconj' : Submodule.conjByFiniteIdele R (h * n) = R := by rw [STAB.conj_mul hR h n]; exact hconj
    have A := mem_localBox_conjByFiniteIdele_iff' hR n v (((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) * x * g)
    have B := mem_localBox_conjByFiniteIdele_iff' hR (h * n) v x
    rw [hconj'] at B
    rw [A, B, map_mul, mul_inv_rev]
    simp only [Units.val_mul, mul_assoc]
    rfl
  ·
    intro hall
    apply hne
    ext z
    rw [GOODEQ.mem_conjByFiniteIdele_iff, GOODEQ.mem_conjByFiniteIdele_iff,
      Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox R hR.fg hR.spanTop,
      Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox R hR.fg hR.spanTop]
    refine forall_congr' fun w => ?_
    rw [map_mul, map_mul, map_mul, map_mul]
    have i1 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) = (((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := by rw [← map_inv]; rfl
    have i2 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) = (((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom n)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := by rw [← map_inv]; rfl
    have j1 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom h : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := rfl
    have j2 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom n : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := rfl
    rw [i1, i2, j1, j2]
    by_cases hw : ((q : ℕ) : 𝓞 ℚ) ∈ w.asIdeal
    · have : w = v := Nat.HeightOneSpectrum.eq_of_natCast_prime_mem hq hw hv
      subst this
      rw [hall, mem_localBox_conjByFiniteIdele_iff' hR n w]
    · have hw' : w ∉ Nat.placesOf q := by rwa [Nat.mem_placesOf_iff hqne]
      have hSw : Submodule.localBox (CerednikDrinfeld.meetOrder R n) w = Submodule.localBox R w :=
        GOODEQ.localBox_meetOrder_eq hR hnH w (Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hqne hw')
      have hhw : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom h ∈ Submodule.localBoxUnits R w := by
        have := GOODEQ.unitsMap_mem_localBoxUnits_of_mem_primeHeckeSet hqne ⟨h1, h2, h3, h4⟩ hw'
        rwa [Submodule.mem_localBoxUnits_iff, hSw, ← Submodule.mem_localBoxUnits_iff] at this
      have hnw : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom n ∈ Submodule.localBoxUnits R w :=
        GOODEQ.unitsMap_mem_localBoxUnits_of_mem_primeHeckeSet hqne hnH hw'
      have e1 := GOODEQ.conj_mem_localBox_iff hR w hhw (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)))
      have e2 := GOODEQ.conj_mem_localBox_iff hR w hnw (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ)))
      exact e1.trans e2.symm

end F3Kit

namespace F3Kit

variable {a b : ℚ}

theorem exists_place_over (q : ℕ) (hq : q.Prime) : ∃ v : HeightOneSpectrum (𝓞 ℚ), ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal :=
  ⟨⟨Ideal.span {((q : ℕ) : 𝓞 ℚ)}, (Nat.isMaximal_span_natCast_of_prime hq).isPrime, Nat.span_natCast_ne_bot hq.ne_zero⟩,
    Ideal.subset_span rfl⟩

theorem exists_mem_uHeckeSet_of_locPred {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {q : ℕ} (hq : q.Prime) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hnH : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    (hS : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n))
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) (hg : LocPred R n q v g) :
    ∃ β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, β ∈ CerednikDrinfeld.uHeckeSet R n q ∧
      Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom β = g := by
  classical
  obtain ⟨⟨hg1, hg2, hg3, hg4⟩, hg5, hg6⟩ := hg
  have hqne : q ≠ 0 := hq.ne_zero

  let y : ∀ w : HeightOneSpectrum (𝓞 ℚ), (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ := fun w =>
    if hw : w = v then cast (congrArg (fun u : HeightOneSpectrum (𝓞 ℚ) => (ℍ[ℚ, a, b] ⊗[ℚ] u.adicCompletion ℚ)ˣ) hw.symm) g else 1
  have hyv : y v = g := by show (if hw : v = v then _ else _) = g; rw [dif_pos rfl]; rfl
  obtain ⟨β, hβS, hβoff⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq (D := ℍ[ℚ, a, b]) ({v} : Finset (HeightOneSpectrum (𝓞 ℚ))) y
  have hβv : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) = (g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) := by
    rw [hβS v (Finset.mem_singleton_self v), hyv]
  have hBv : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom β = g := Units.ext hβv
  have hβw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) = 1 :=
    fun w hw => hβoff w (by rwa [Finset.mem_singleton])
  have hBw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom β = 1 :=
    fun w hw => Units.ext (hβw w hw)
  have hwv : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ((q : ℕ) : 𝓞 ℚ) ∉ w.asIdeal :=
    fun w hw hqw => hw (Nat.HeightOneSpectrum.eq_of_natCast_prime_mem hq hqw hv)
  have hwv' : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → w ∉ Nat.placesOf q :=
    fun w hw => by rw [Nat.mem_placesOf_iff hqne]; exact hwv w hw

  have hβvi : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((β⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) = ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) := by
    rw [← hBv, ← map_inv]; rfl
  have hβwi : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (((β⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ))) = 1 := by
    intro w hw
    have := hBw w hw
    rw [← inv_eq_one, ← map_inv] at this
    exact congrArg Units.val this
  refine ⟨β, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, hBv⟩

  · rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox _ hS.fg hS.spanTop]
    intro w
    by_cases hw : w = v
    · subst hw; rw [hβv]; exact hg1
    · rw [hβw w hw]; exact HeckeLocal.one_mem_localBox hS w
  · rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox _ hS.fg hS.spanTop]
    intro w
    rw [map_smul]
    by_cases hw : w = v
    · subst hw; rw [hβvi]; exact hg2
    · rw [hβwi w hw]
      exact GOODEQ.smul_mem_localBox w (by rw [map_natCast]; exact natCast_mem _ q) (HeckeLocal.one_mem_localBox hS w)
  · intro hmem
    apply hg3
    rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox _ hS.fg hS.spanTop] at hmem
    have := hmem v
    rwa [hβvi] at this
  · intro hmem
    apply hg4
    rw [Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox _ hS.fg hS.spanTop] at hmem
    have := hmem v
    rwa [map_smul, hβv] at this

  · ext z
    rw [GOODEQ.mem_conjByFiniteIdele_iff, GOODEQ.mem_box_conjByFiniteIdele_iff hR n, ← STAB.tmul_one_mem_box_iff hR z,
      Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox R hR.fg hR.spanTop,
      Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox R hR.fg hR.spanTop]
    refine forall_congr' fun w => ?_
    rw [map_mul, map_mul, map_mul, map_mul]
    have i2 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) = (((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom n)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := by rw [← map_inv]; rfl
    have j2 : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w ((n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom n : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)) := rfl
    rw [i2, j2]
    by_cases hw : w = v
    · subst hw
      rw [hβv, hβvi]
      exact (mem_localBox_conjByFiniteIdele_iff' hR n w _).symm.trans (hg5 _)
    · rw [hβw w hw, hβwi w hw, one_mul, mul_one]
      exact GOODEQ.conj_mem_localBox_iff hR w (GOODEQ.unitsMap_mem_localBoxUnits_of_mem_primeHeckeSet hqne hnH (hwv' w hw)) _

  · intro heq
    apply hg6
    intro x
    have A := mem_localBox_conjByFiniteIdele_iff' hR β v x
    rw [heq, hBv] at A
    exact A.symm

end F3Kit

theorem solution
    (N q q' : ℕ) [NeZero N] [Fact q.Prime] [Fact q'.Prime]
    (hqq' : q' ≠ q) (hqN : ¬ q ∣ N) (hq'N : ¬ q' ∣ N)
    {a b : ℚ} (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hn : IsEichlerOrder (meetOrder R n) (N * q)) (hnH : n ∈ primeHeckeSet R q) :
    Set.ncard {c : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n) |
        ∃ h ∈ uHeckeSet R n q, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n)) = c} = q := by
  classical
  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder
  have hSo : QuaternionAlgebra.IsOrder (meetOrder R n) := hn.isOrder
  have hqP : q.Prime := Fact.out
  obtain ⟨v, hv⟩ := F3Kit.exists_place_over q hqP

  refine (Set.ncard_congr
    (fun c hc => (QuotientGroup.mk (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom
      (Classical.choose hc)) : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸ MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ
          ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v : AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))))
    ?_ ?_ ?_).trans
    (CerednikDrinfeld.ncard_setOf_quotientMk_stabilizer_localBox_meetOrder_eq_of_mem_primeHeckeSet
      (Fact.out : q'.Prime) hdef hR q hqP hqq'.symm hqN n hnH v hv)
  ·
    intro c hc
    obtain ⟨hh, hc'⟩ := Classical.choose_spec hc
    have hP := F3Kit.locPred_of_mem_uHeckeSet hRo hqP n hnH hSo v hv hh
    exact ⟨_, hP.1, hP.2.1, hP.2.2, rfl⟩
  ·
    intro c c' hc hc' hcc
    obtain ⟨hh, hce⟩ := Classical.choose_spec hc
    obtain ⟨hh', hce'⟩ := Classical.choose_spec hc'
    rw [← hce, ← hce']
    rw [F3Kit.coe_eq_coe_iff_map_inv_mul_mem_localBoxUnits hSo hqP v hv hh.1 hh'.1,
      ← F3Kit.mem_stabilizer_localBox_iff hSo v]
    exact QuotientGroup.eq.mp hcc
  ·
    rintro d ⟨g, hgA, hgB, hgC, rfl⟩
    obtain ⟨β, hβ, hβg⟩ := F3Kit.exists_mem_uHeckeSet_of_locPred hRo hqP n hnH hSo v hv g ⟨hgA, hgB, hgC⟩
    have hc : ∃ h ∈ uHeckeSet R n q, (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ Submodule.finiteIdeleStabilizer (meetOrder R n)) = (β : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ ⧸ _) := ⟨β, hβ, rfl⟩
    refine ⟨_, hc, ?_⟩
    obtain ⟨hh', hce'⟩ := Classical.choose_spec hc
    rw [← hβg]
    apply QuotientGroup.eq.mpr
    rw [F3Kit.mem_stabilizer_localBox_iff hSo v, ← F3Kit.coe_eq_coe_iff_map_inv_mul_mem_localBoxUnits hSo hqP v hv hh'.1 hβ.1]
    exact hce'

end S_CerednikDrinfeld_ncard_setOf_exists_mem_uHeckeSet_quotientMk_eq_of_mem_primeHeckeSet
end P2MW
export P2MW.S_CerednikDrinfeld_ncard_setOf_exists_mem_uHeckeSet_quotientMk_eq_of_mem_primeHeckeSet (solution)
