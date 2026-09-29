-- Prove2me | solution 1 for CerednikDrinfeld.ncard_setOf_quotientMk_stabilizer_localBox_meetOrder_eq_of_mem_primeHeckeSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/8fbe4093-2c88-55e3-ba37-13144ac88361

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_nonempty_algEquiv_matrix_of_normForm_eq_zero
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_localBox_eq_localBox_of_isMaximalOrder_of_le_of_not_dvd
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_ncard_setOf_quotientMk_stabilizer_localBox_meetOrder_eq_of_mem_primeHeckeSet
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul"

set_option autoImplicit false

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField

namespace Nat
p2m_export "Nat" "prime_iff card_coe_set_eq log count Coprime divisors Prime Prime.factorization_self prime_iff_prime_int isCoprime_iff_coprime eq_zero_or_pos card_fin cast_zero card_congr all zero coprime_primes"
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

namespace HeckeLocal

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set ℍ𝔸 :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ𝔸} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  have : Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [this]; rfl

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
  have e1 : (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) = f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) :=
    Units.coe_map_inv _ _
  have e2 : f ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (v.adicCompletion ℚ) ((ℓ : ℚ)⁻¹)) * f ((ℓ : ℚ) • ((h⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
    rw [map_smul, ← Algebra.TensorProduct.algebraMap_apply', ← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hℓ0, one_smul]
  show (((Units.map f.toRingHom.toMonoidHom h)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ _
  rw [e1, e2]
  exact tmul_one_mul_mem_localBox v hℓv (finiteAdeleEvalAt_mem_localBox v h2)

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

end HeckeLocal

namespace GOODEQ

variable {a b : ℚ}

local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" v => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v

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

theorem unitsMap_mem_localBoxUnits_of_mem_primeHeckeSet {R : Submodule ℤ ℍ[ℚ, a, b]} {q : ℕ} (hq : q ≠ 0) {n : (ℍ𝔸)ˣ}
    (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q) {v : HeightOneSpectrum (𝓞 ℚ)} (hv : v ∉ Nat.placesOf q) :
    Units.map (ev v).toRingHom.toMonoidHom n ∈ Submodule.localBoxUnits R v :=
  HeckeLocal.map_finiteAdeleEvalAt_mem_localBoxUnits_of_mem_primeHeckeSet q hn v
    (Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hq hv)

end GOODEQ

namespace C8N
namespace LocalAtQ

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))

theorem natCast_notMem_of_prime_mem {P : Ideal (𝓞 ℚ)} (hP : P ≠ ⊤) (q : ℕ) (hqP : ((q : ℕ) : 𝓞 ℚ) ∈ P)
    (n : ℕ) (hn : Nat.Coprime q n) : ((n : ℕ) : 𝓞 ℚ) ∉ P := by
  intro hnP
  apply hP
  rw [Ideal.eq_top_iff_one]
  obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hn
  have : (1 : 𝓞 ℚ) = (u : 𝓞 ℚ) * (q : 𝓞 ℚ) + (w : 𝓞 ℚ) * (n : 𝓞 ℚ) := by
    have := congrArg (Int.cast : ℤ → 𝓞 ℚ) huw
    push_cast at this
    exact this.symm
  rw [this]
  exact P.add_mem (P.mul_mem_left _ hqP) (P.mul_mem_left _ hnP)

theorem exists_splitting {q' : ℕ} (hq' : q'.Prime) (hB : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    (q : ℕ) (hq : q.Prime) (hqq' : q ≠ q') (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), ∀ r : v.adicCompletion ℚ, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) := by
  haveI : CharZero (v.adicCompletion ℚ) := charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  have hq'v : ((q' : ℕ) : 𝓞 ℚ) ∉ v.asIdeal :=
    natCast_notMem_of_prime_mem v.isPrime.ne_top q hqv q' ((Nat.coprime_primes hq hq').mpr hqq')
  have hnd : ¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x := fun hall => hq'v ((hB.2.2 v).mp hall)
  rw [QuaternionAlgebra.forall_tensorProduct_adicCompletion_isUnit_iff_forall_normForm_eq_zero] at hnd
  push Not at hnd
  obtain ⟨x₀, x₁, x₂, x₃, h0, hx⟩ := hnd
  have ha : (a : v.adicCompletion ℚ) ≠ 0 := by exact_mod_cast hB.neg_left.ne
  have hb : (b : v.adicCompletion ℚ) ≠ 0 := by exact_mod_cast hB.neg_right.ne
  have hx' : ¬ (x₀ = 0 ∧ x₁ = 0 ∧ x₂ = 0 ∧ x₃ = 0) := fun h => hx h.1 h.2.1 h.2.2.1 h.2.2.2
  obtain ⟨ψ⟩ := QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero (v.adicCompletion ℚ) two_ne_zero (a : v.adicCompletion ℚ) (b : v.adicCompletion ℚ)
    ha hb x₀ x₁ x₂ x₃ hx' h0
  obtain ⟨φ, hφ, -⟩ := QuaternionAlgebra.exists_ringEquiv_tensorProduct_forall_one_tmul_of_algEquiv
    (R := ℚ) (S := v.adicCompletion ℚ) (c₁ := a) (c₂ := (0 : ℚ)) (c₃ := b) (d₁ := (a : v.adicCompletion ℚ)) (d₂ := (0 : v.adicCompletion ℚ)) (d₃ := (b : v.adicCompletion ℚ))
    (eq_ratCast _ a) (by simp) (eq_ratCast _ b) ψ
  exact ⟨φ, hφ⟩

end C8N.LocalAtQ

namespace F3LOC

open Matrix

variable {K : Type*} [Field K] {𝒪 : ValuationSubring K}

local notation "val" => ValuationSubring.valuation 𝒪

theorem mem_iff_val {x : K} : x ∈ 𝒪 ↔ val x ≤ 1 := (𝒪.valuation_le_one_iff x).symm

def IsU (𝒪 : ValuationSubring K) (x : K) : Prop := 𝒪.valuation x = 1

theorem IsU.mem {x : K} (h : IsU 𝒪 x) : x ∈ 𝒪 := mem_iff_val.mpr h.le
theorem IsU.ne_zero {x : K} (h : IsU 𝒪 x) : x ≠ 0 := by rintro rfl; simp [IsU] at h
theorem IsU.inv {x : K} (h : IsU 𝒪 x) : IsU 𝒪 x⁻¹ := by unfold IsU at *; rw [map_inv₀, h, inv_one]
theorem IsU.mul {x y : K} (hx : IsU 𝒪 x) (hy : IsU 𝒪 y) : IsU 𝒪 (x * y) := by unfold IsU at *; rw [map_mul, hx, hy, one_mul]
theorem isU_one : IsU 𝒪 (1 : K) := by unfold IsU; exact map_one _
theorem isU_of_mem_of_inv_mem {x : K} (hx : x ∈ 𝒪) (hxi : x⁻¹ ∈ 𝒪) (hx0 : x ≠ 0) : IsU 𝒪 x := by
  rw [mem_iff_val] at hx hxi
  rw [map_inv₀] at hxi
  refine le_antisymm hx ?_
  have h0 : 0 < val x := zero_lt_iff.mpr ((map_ne_zero _).mpr hx0)
  exact (inv_le_one₀ h0).mp hxi

theorem val_lt_one_of_not_isU {x : K} (hx : x ∈ 𝒪) (hu : ¬ IsU 𝒪 x) : val x < 1 :=
  lt_of_le_of_ne (mem_iff_val.mp hx) hu

theorem isU_or_isU_of_isU_add {a₀ a₁ b₀ b₁ : K} (ha₀ : a₀ ∈ 𝒪) (ha₁ : a₁ ∈ 𝒪) (hb₀ : b₀ ∈ 𝒪) (hb₁ : b₁ ∈ 𝒪)
    (h : IsU 𝒪 (a₀ * b₀ + a₁ * b₁)) : IsU 𝒪 b₀ ∨ IsU 𝒪 b₁ := by
  by_contra hcon
  push_neg at hcon
  have h0 : val (a₀ * b₀) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (mem_iff_val.mp ha₀)) (val_lt_one_of_not_isU hb₀ hcon.1)
  have h1 : val (a₁ * b₁) < 1 := by
    rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (mem_iff_val.mp ha₁)) (val_lt_one_of_not_isU hb₁ hcon.2)
  have := Valuation.map_add_lt (val) h0 h1
  rw [h] at this
  exact lt_irrefl _ this

def IsInt (𝒪 : ValuationSubring K) (y : Matrix (Fin 2) (Fin 2) K) : Prop := ∀ i j, y i j ∈ 𝒪

def IsIntU (𝒪 : ValuationSubring K) (y : Matrix (Fin 2) (Fin 2) K) : Prop :=
  IsInt 𝒪 y ∧ IsUnit y.det ∧ IsInt 𝒪 y⁻¹

theorem IsInt.mul {y z : Matrix (Fin 2) (Fin 2) K} (hy : IsInt 𝒪 y) (hz : IsInt 𝒪 z) : IsInt 𝒪 (y * z) := by
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact add_mem (mul_mem (hy i 0) (hz 0 j)) (mul_mem (hy i 1) (hz 1 j))

theorem IsInt.one : IsInt 𝒪 (1 : Matrix (Fin 2) (Fin 2) K) := by
  intro i j; rw [Matrix.one_apply]; split_ifs <;> simp [one_mem, zero_mem]

theorem IsInt.smul {y : Matrix (Fin 2) (Fin 2) K} (hy : IsInt 𝒪 y) {c : K} (hc : c ∈ 𝒪) : IsInt 𝒪 (c • y) :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hy i j)

theorem IsIntU.isInt_conj_iff {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) (Y : Matrix (Fin 2) (Fin 2) K) :
    IsInt 𝒪 (k⁻¹ * Y * k) ↔ IsInt 𝒪 Y := by
  have hdet : IsUnit k.det := hk.2.1
  constructor
  · intro h
    have := (hk.1.mul h).mul hk.2.2
    rwa [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hdet, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hdet,
      mul_one] at this
  · intro h; exact (hk.2.2.mul h).mul hk.1

theorem IsIntU.exists_isU_col {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) (j : Fin 2) :
    IsU 𝒪 (k 0 j) ∨ IsU 𝒪 (k 1 j) := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul k hk.2.1) j) j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h
  exact isU_or_isU_of_isU_add (hk.2.2 j 0) (hk.2.2 j 1) (hk.1 0 j) (hk.1 1 j) (by rw [h]; exact isU_one)

theorem IsIntU.exists_isU_inv_row {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) (i : Fin 2) :
    IsU 𝒪 (k⁻¹ i 0) ∨ IsU 𝒪 (k⁻¹ i 1) := by
  have h := congrFun (congrFun (Matrix.nonsing_inv_mul k hk.2.1) i) i
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq] at h

  have h' : k 0 i * k⁻¹ i 0 + k 1 i * k⁻¹ i 1 = 1 := by rw [mul_comm (k 0 i), mul_comm (k 1 i)]; exact h
  exact isU_or_isU_of_isU_add (hk.1 0 i) (hk.1 1 i) (hk.2.2 i 0) (hk.2.2 i 1) (by rw [h']; exact isU_one)

theorem IsIntU.smul {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) {u : K} (hu : IsU 𝒪 u) : IsIntU 𝒪 (u • k) := by
  refine ⟨hk.1.smul hu.mem, ?_, ?_⟩
  · rw [Matrix.det_smul, Fintype.card_fin]; exact (hu.ne_zero.isUnit.pow 2).mul hk.2.1
  · have e : (u • k)⁻¹ = u⁻¹ • k⁻¹ := by
      have h1 : u • k = (Units.mk0 u hu.ne_zero) • k := rfl
      rw [h1, Matrix.inv_smul' k (Units.mk0 u hu.ne_zero) hk.2.1, Units.smul_def]
      simp
    rw [e]
    exact hk.2.2.smul hu.inv.mem

theorem IsInt.det_mem {y : Matrix (Fin 2) (Fin 2) K} (hy : IsInt 𝒪 y) : y.det ∈ 𝒪 := by
  rw [Matrix.det_fin_two]; exact sub_mem (mul_mem (hy 0 0) (hy 1 1)) (mul_mem (hy 0 1) (hy 1 0))

theorem IsIntU.isU_det {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) : IsU 𝒪 k.det := by
  refine isU_of_mem_of_inv_mem hk.1.det_mem ?_ hk.2.1.ne_zero
  have h := hk.2.2.det_mem
  rwa [Matrix.det_nonsing_inv, Ring.inverse_eq_inv'] at h

theorem inv_fin_two (k : Matrix (Fin 2) (Fin 2) K) (hk : IsUnit k.det) :
    k⁻¹ = k.det⁻¹ • !![k 1 1, -k 0 1; -k 1 0, k 0 0] := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']

section pi

variable (ϖ : K)

def Dm : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![(1 : K), ϖ]

def Dm' : Matrix (Fin 2) (Fin 2) K := Matrix.diagonal ![ϖ, (1 : K)]

variable {ϖ}

theorem Dm_inv (hϖ0 : ϖ ≠ 0) : (Dm ϖ)⁻¹ = Matrix.diagonal ![(1 : K), ϖ⁻¹] :=
  Matrix.inv_eq_right_inv (by rw [Dm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [hϖ0])

theorem Dm'_inv (hϖ0 : ϖ ≠ 0) : (Dm' ϖ)⁻¹ = Matrix.diagonal ![ϖ⁻¹, (1 : K)] :=
  Matrix.inv_eq_right_inv (by rw [Dm', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [hϖ0])

theorem det_Dm (hϖ0 : ϖ ≠ 0) : (Dm ϖ).det = ϖ := by simp [Dm, Matrix.det_diagonal]
theorem det_Dm' (hϖ0 : ϖ ≠ 0) : (Dm' ϖ).det = ϖ := by simp [Dm', Matrix.det_diagonal]

theorem smul_Dm_inv (hϖ0 : ϖ ≠ 0) : ϖ • (Dm ϖ)⁻¹ = Dm' ϖ := by
  rw [Dm_inv hϖ0, Dm']; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hϖ0]

theorem Dm_inv_conj (hϖ0 : ϖ ≠ 0) (Y : Matrix (Fin 2) (Fin 2) K) :
    (Dm ϖ)⁻¹ * Y * Dm ϖ = !![Y 0 0, ϖ * Y 0 1; ϖ⁻¹ * Y 1 0, Y 1 1] := by
  rw [Dm_inv hϖ0, Dm]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm, hϖ0]

theorem Dm'_inv_conj (hϖ0 : ϖ ≠ 0) (Y : Matrix (Fin 2) (Fin 2) K) :
    (Dm' ϖ)⁻¹ * Y * Dm' ϖ = !![Y 0 0, ϖ⁻¹ * Y 0 1; ϖ * Y 1 0, Y 1 1] := by
  rw [Dm'_inv hϖ0, Dm']; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm, hϖ0]

theorem Dm_inv_mul_mul_Dm' (hϖ0 : ϖ ≠ 0) (k : Matrix (Fin 2) (Fin 2) K) :
    (Dm ϖ)⁻¹ * k * Dm' ϖ = !![ϖ * k 0 0, k 0 1; k 1 0, ϖ⁻¹ * k 1 1] := by
  rw [Dm_inv hϖ0, Dm']; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm, hϖ0]

theorem Dm'_inv_mul_mul_Dm (hϖ0 : ϖ ≠ 0) (k : Matrix (Fin 2) (Fin 2) K) :
    (Dm' ϖ)⁻¹ * k * Dm ϖ = !![ϖ⁻¹ * k 0 0, k 0 1; k 1 0, ϖ * k 1 1] := by
  rw [Dm'_inv hϖ0, Dm]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm, hϖ0]

theorem mul_Dm' (hϖ0 : ϖ ≠ 0) (k : Matrix (Fin 2) (Fin 2) K) : k * Dm' ϖ = !![ϖ * k 0 0, k 0 1; ϖ * k 1 0, k 1 1] := by
  rw [Dm']; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm]

theorem mul_Dm_inv (hϖ0 : ϖ ≠ 0) (k : Matrix (Fin 2) (Fin 2) K) : k * (Dm ϖ)⁻¹ = !![k 0 0, ϖ⁻¹ * k 0 1; k 1 0, ϖ⁻¹ * k 1 1] := by
  rw [Dm_inv hϖ0]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm]

theorem Dm_mul (hϖ0 : ϖ ≠ 0) (k : Matrix (Fin 2) (Fin 2) K) : Dm ϖ * k = !![k 0 0, k 0 1; ϖ * k 1 0, ϖ * k 1 1] := by
  rw [Dm]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal]

def IsIw (𝒪 : ValuationSubring K) (ϖ : K) (y : Matrix (Fin 2) (Fin 2) K) : Prop := IsInt 𝒪 y ∧ ϖ⁻¹ * y 1 0 ∈ 𝒪

theorem isIw_iff_isInt_and (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {y : Matrix (Fin 2) (Fin 2) K} : IsIw 𝒪 ϖ y ↔ IsInt 𝒪 y ∧ IsInt 𝒪 ((Dm ϖ)⁻¹ * y * Dm ϖ) := by
  rw [IsIw, Dm_inv_conj hϖ0]
  refine and_congr_right fun hy => ⟨fun h i j => ?_, fun h => by simpa using h 1 0⟩
  fin_cases i <;> fin_cases j
  · simpa using hy 0 0
  · simpa using mul_mem hϖ (hy 0 1)
  · simpa using h
  · simpa using hy 1 1

theorem normalForm (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hmax : ∀ x : K, x ∈ 𝒪 → ¬ IsU 𝒪 x → ϖ⁻¹ * x ∈ 𝒪) (y : Matrix (Fin 2) (Fin 2) K) (hy : IsUnit y.det)
    (h1 : IsIw 𝒪 ϖ y) (h2 : IsIw 𝒪 ϖ (ϖ • y⁻¹))
    (hii : ∀ Y : Matrix (Fin 2) (Fin 2) K, IsInt 𝒪 ((Dm ϖ)⁻¹ * (y⁻¹ * Y * y) * Dm ϖ) ↔ IsInt 𝒪 Y)
    (hiii : ¬ ∀ Y : Matrix (Fin 2) (Fin 2) K, IsInt 𝒪 (y⁻¹ * Y * y) ↔ IsInt 𝒪 ((Dm ϖ)⁻¹ * Y * Dm ϖ)) :
    ∃ k : Matrix (Fin 2) (Fin 2) K, IsIntU 𝒪 k ∧ IsU 𝒪 (k 1 1) ∧ y = k * Dm' ϖ := by

  have hDdet : IsUnit (Dm ϖ).det := by rw [det_Dm hϖ0]; exact hϖ0.isUnit
  set g : Matrix (Fin 2) (Fin 2) K := y * Dm ϖ with hg
  have hgdet : IsUnit g.det := by rw [hg, Matrix.det_mul]; exact hy.mul hDdet
  have hginv : g⁻¹ = (Dm ϖ)⁻¹ * y⁻¹ := by rw [hg, Matrix.mul_inv_rev]
  have hgconj : ∀ M : Matrix (Fin 2) (Fin 2) K, IsInt 𝒪 M → IsInt 𝒪 (g⁻¹ * M * g) := by
    intro M hM
    have := (hii M).mpr hM
    rwa [hginv, hg, ← mul_assoc, ← mul_assoc, mul_assoc ((Dm ϖ)⁻¹ * y⁻¹)] at *

  have hginvdet : (g⁻¹).det ≠ 0 := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact inv_ne_zero hgdet.ne_zero
  let G : GL (Fin 2) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (g⁻¹) hginvdet
  have hGcoe : ((G : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = g⁻¹ := rfl
  have hGinv : ((G⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = g := by
    rw [Matrix.coe_units_inv, hGcoe, Matrix.nonsing_inv_nonsing_inv _ hgdet]
  obtain ⟨c, hc1, hc2⟩ :=
    Matrix.GeneralLinearGroup.exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem 𝒪 G
      (fun M hM i j => by rw [hGcoe, hGinv]; exact hgconj M hM i j)
  simp only [hGcoe, hGinv] at hc1 hc2

  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hk₀ : IsIntU 𝒪 ((c : K) • g) := by
    refine ⟨fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hc2 i j, ?_, ?_⟩
    · rw [Matrix.det_smul, Fintype.card_fin]; exact (hc0.isUnit.pow 2).mul hgdet
    · have e : ((c : K) • g)⁻¹ = (c : K)⁻¹ • g⁻¹ := by
        rw [show (c : K) • g = c • g from rfl, Matrix.inv_smul' g c hgdet, Units.smul_def, Units.val_inv_eq_inv_val]
      rw [e]; intro i j; rw [Matrix.smul_apply, smul_eq_mul, ← Units.val_inv_eq_inv_val]; exact hc1 i j

  have hyeq : y = (c : K)⁻¹ • (((c : K) • g) * (Dm ϖ)⁻¹) := by
    rw [Matrix.smul_mul, smul_smul, inv_mul_cancel₀ hc0, one_smul, hg, mul_assoc, Matrix.mul_nonsing_inv _ hDdet, mul_one]
  set k₀ := (c : K) • g with hk₀def

  have ha : (c : K)⁻¹ * ϖ⁻¹ ∈ 𝒪 := by
    have hcol : ∀ i, y i 1 = (c : K)⁻¹ * ϖ⁻¹ * k₀ i 1 := by
      intro i; rw [hyeq, Matrix.smul_apply, smul_eq_mul, mul_Dm_inv hϖ0]
      fin_cases i <;> simp [mul_assoc, mul_comm, mul_left_comm]
    rcases hk₀.exists_isU_col 1 with hu | hu
    · have := mul_mem (h1.1 0 1) hu.inv.mem
      rwa [hcol 0, mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one] at this
    · have := mul_mem (h1.1 1 1) hu.inv.mem
      rwa [hcol 1, mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one] at this

  have hyinv : y⁻¹ = (c : K) • (Dm ϖ * k₀⁻¹) := by
    rw [hyeq, show ((c : K)⁻¹ • (k₀ * (Dm ϖ)⁻¹)) = (c⁻¹ : Kˣ) • (k₀ * (Dm ϖ)⁻¹) from by rw [Units.smul_def, Units.val_inv_eq_inv_val],
      Matrix.inv_smul' _ c⁻¹ (by rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact hk₀.2.1.mul hDdet.ne_zero.isUnit.inv),
      inv_inv, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hDdet, Units.smul_def]
  have hb : ϖ * (c : K) ∈ 𝒪 := by
    have hrow : ∀ j, (ϖ • y⁻¹) 0 j = ϖ * (c : K) * k₀⁻¹ 0 j := by
      intro j; rw [hyinv, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Dm_mul hϖ0]
      fin_cases j <;> simp [mul_assoc]
    rcases hk₀.exists_isU_inv_row 0 with hu | hu
    · have := mul_mem (h2.1 0 0) hu.inv.mem
      rwa [hrow 0, mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one] at this
    · have := mul_mem (h2.1 0 1) hu.inv.mem
      rwa [hrow 1, mul_assoc, mul_inv_cancel₀ hu.ne_zero, mul_one] at this

  have hu : IsU 𝒪 (ϖ * (c : K)) :=
    isU_of_mem_of_inv_mem hb (by rwa [_root_.mul_inv_rev]) (mul_ne_zero hϖ0 hc0)
  refine ⟨(ϖ * (c : K))⁻¹ • k₀, hk₀.smul hu.inv, ?_, ?_⟩
  rotate_left
  ·
    rw [Matrix.smul_mul, hyeq, ← smul_Dm_inv hϖ0, Matrix.mul_smul, smul_smul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hϖ0, mul_one]
  ·
    by_contra hnu
    apply hiii
    set k := (ϖ * (c : K))⁻¹ • k₀ with hkdef
    have hk : IsIntU 𝒪 k := hk₀.smul hu.inv
    have hyk : y = k * Dm' ϖ := by
      rw [hkdef, Matrix.smul_mul, hyeq, ← smul_Dm_inv hϖ0, Matrix.mul_smul, smul_smul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hϖ0, mul_one]

    have hdiv : ϖ⁻¹ * k 1 1 ∈ 𝒪 := hmax _ (hk.1 1 1) hnu
    have hkdet : IsU 𝒪 k.det := hk.isU_det
    set Z := (Dm ϖ)⁻¹ * k * Dm' ϖ with hZ
    have hZdet : IsUnit Z.det := by
      rw [hZ, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, det_Dm hϖ0, det_Dm' hϖ0, Ring.inverse_eq_inv']
      exact (hϖ0.isUnit.inv.mul hk.2.1).mul hϖ0.isUnit
    have hZint : IsInt 𝒪 Z := by
      rw [hZ, Dm_inv_mul_mul_Dm' hϖ0]
      intro i j; fin_cases i <;> fin_cases j
      · simpa using mul_mem hϖ (hk.1 0 0)
      · simpa using hk.1 0 1
      · simpa using hk.1 1 0
      · simpa using hdiv
    have hZinv : Z⁻¹ = (Dm' ϖ)⁻¹ * k⁻¹ * Dm ϖ := by
      rw [hZ, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hDdet, mul_assoc]
    have hZinvint : IsInt 𝒪 Z⁻¹ := by
      rw [hZinv, Dm'_inv_mul_mul_Dm hϖ0, inv_fin_two k hk.2.1]
      intro i j; fin_cases i <;> fin_cases j
      · simpa [mul_comm, mul_left_comm, mul_assoc] using mul_mem hdiv hkdet.inv.mem
      · simpa using mul_mem hkdet.inv.mem (neg_mem (hk.1 0 1))
      · simpa using mul_mem hkdet.inv.mem (neg_mem (hk.1 1 0))
      · simpa [mul_comm, mul_left_comm] using mul_mem hϖ (mul_mem hkdet.inv.mem (hk.1 0 0))
    have hZU : IsIntU 𝒪 Z := ⟨hZint, hZdet, hZinvint⟩

    have hyZ : y = Dm ϖ * Z := by rw [hZ, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hDdet, one_mul, hyk]
    intro Y
    rw [hyZ, Matrix.mul_inv_rev, show Z⁻¹ * (Dm ϖ)⁻¹ * Y * (Dm ϖ * Z) = Z⁻¹ * ((Dm ϖ)⁻¹ * Y * Dm ϖ) * Z by
      simp only [mul_assoc]]
    exact hZU.isInt_conj_iff _

def IsB (𝒪 : ValuationSubring K) (ϖ : K) (z : Matrix (Fin 2) (Fin 2) K) : Prop := IsIw 𝒪 ϖ z ∧ IsUnit z.det ∧ IsIw 𝒪 ϖ z⁻¹

def yRep (ϖ t : K) : Matrix (Fin 2) (Fin 2) K := !![ϖ, t; 0, 1]

theorem det_yRep (hϖ0 : ϖ ≠ 0) (t : K) : (yRep ϖ t).det = ϖ := by simp [yRep, Matrix.det_fin_two]

theorem yRep_inv (hϖ0 : ϖ ≠ 0) (t : K) : (yRep ϖ t)⁻¹ = !![ϖ⁻¹, -(ϖ⁻¹ * t); 0, 1] := by
  rw [inv_fin_two _ (by rw [det_yRep hϖ0]; exact hϖ0.isUnit), det_yRep hϖ0]
  ext i j; fin_cases i <;> fin_cases j <;> simp [yRep, hϖ0]

theorem yRep_eq (hϖ0 : ϖ ≠ 0) (t : K) : yRep ϖ t = !![1, t; 0, 1] * Dm' ϖ := by
  rw [mul_Dm' hϖ0]; ext i j; fin_cases i <;> fin_cases j <;> simp [yRep]

theorem isIw_yRep (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {t : K} (ht : t ∈ 𝒪) : IsIw 𝒪 ϖ (yRep ϖ t) := by
  refine ⟨fun i j => ?_, by simp [yRep]⟩
  fin_cases i <;> fin_cases j <;> simp [yRep, hϖ, ht, one_mem, zero_mem]

theorem isIw_smul_yRep_inv (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {t : K} (ht : t ∈ 𝒪) : IsIw 𝒪 ϖ (ϖ • (yRep ϖ t)⁻¹) := by
  rw [yRep_inv hϖ0]
  refine ⟨fun i j => ?_, by simp⟩
  fin_cases i <;> fin_cases j <;> simp [hϖ0, hϖ, ht, neg_mem, one_mem, zero_mem]

theorem not_isIw_yRep_inv (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hϖu : ¬ IsU 𝒪 ϖ) (t : K) : ¬ IsIw 𝒪 ϖ (yRep ϖ t)⁻¹ := by
  rw [yRep_inv hϖ0]; intro h
  have := h.1 0 0; simp at this
  exact hϖu (isU_of_mem_of_inv_mem hϖ this hϖ0)

theorem not_isIw_smul_yRep (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hϖu : ¬ IsU 𝒪 ϖ) (t : K) : ¬ IsIw 𝒪 ϖ (ϖ⁻¹ • yRep ϖ t) := by
  intro h
  have := h.1 1 1; simp [yRep] at this
  exact hϖu (isU_of_mem_of_inv_mem hϖ this hϖ0)

theorem isInt_conj_yRep_Dm_iff (hϖ0 : ϖ ≠ 0) {t : K} (ht : t ∈ 𝒪) (Y : Matrix (Fin 2) (Fin 2) K) :
    IsInt 𝒪 ((Dm ϖ)⁻¹ * ((yRep ϖ t)⁻¹ * Y * yRep ϖ t) * Dm ϖ) ↔ IsInt 𝒪 Y := by

  have hU : IsIntU 𝒪 !![(1 : K), t; 0, 1] := by
    refine ⟨fun i j => ?_, by simp [Matrix.det_fin_two], ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [ht, one_mem, zero_mem]
    · rw [inv_fin_two _ (by simp [Matrix.det_fin_two])]
      intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two, ht, neg_mem, one_mem, zero_mem]
  have hyD : yRep ϖ t * Dm ϖ = ϖ • !![(1 : K), t; 0, 1] := by
    rw [yRep, Dm]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal, mul_comm]
  have e : (Dm ϖ)⁻¹ * ((yRep ϖ t)⁻¹ * Y * yRep ϖ t) * Dm ϖ = (!![(1 : K), t; 0, 1])⁻¹ * Y * !![(1 : K), t; 0, 1] := by
    have h1 : (Dm ϖ)⁻¹ * (yRep ϖ t)⁻¹ = (yRep ϖ t * Dm ϖ)⁻¹ := by rw [Matrix.mul_inv_rev]
    calc (Dm ϖ)⁻¹ * ((yRep ϖ t)⁻¹ * Y * yRep ϖ t) * Dm ϖ
        = ((Dm ϖ)⁻¹ * (yRep ϖ t)⁻¹) * Y * (yRep ϖ t * Dm ϖ) := by simp only [mul_assoc]
      _ = (ϖ • !![(1 : K), t; 0, 1])⁻¹ * Y * (ϖ • !![(1 : K), t; 0, 1]) := by rw [h1, hyD]
      _ = (!![(1 : K), t; 0, 1])⁻¹ * Y * !![(1 : K), t; 0, 1] := by
          rw [show ϖ • !![(1 : K), t; 0, 1] = (Units.mk0 ϖ hϖ0) • !![(1 : K), t; 0, 1] from rfl,
            Matrix.inv_smul' _ (Units.mk0 ϖ hϖ0) hU.2.1, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel, one_smul]
  rw [e]; exact hU.isInt_conj_iff Y

theorem not_forall_isInt_conj_yRep_iff (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hϖu : ¬ IsU 𝒪 ϖ) (t : K) :
    ¬ ∀ Y : Matrix (Fin 2) (Fin 2) K, IsInt 𝒪 ((yRep ϖ t)⁻¹ * Y * yRep ϖ t) ↔ IsInt 𝒪 ((Dm ϖ)⁻¹ * Y * Dm ϖ) := by
  intro h
  have h1 := (h !![(0 : K), 1; 0, 0]).mpr (by
    rw [Dm_inv_conj hϖ0]; intro i j; fin_cases i <;> fin_cases j <;> simp [hϖ, one_mem, zero_mem])
  have := h1 0 1
  rw [yRep_inv hϖ0, yRep] at this
  simp [Matrix.mul_apply, Fin.sum_univ_two] at this
  exact hϖu (isU_of_mem_of_inv_mem hϖ this hϖ0)

theorem isB_conj_unipotent_iff (hϖ0 : ϖ ≠ 0) {s : K} (hs : s ∈ 𝒪) :
    IsB 𝒪 ϖ ((Dm' ϖ)⁻¹ * !![(1 : K), s; 0, 1] * Dm' ϖ) ↔ ϖ⁻¹ * s ∈ 𝒪 := by
  rw [Dm'_inv_conj hϖ0]
  have hdet : (!![(1 : K), ϖ⁻¹ * s; (ϖ * 0 : K), 1]).det = 1 := by simp [Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  constructor
  · intro h; simpa using h.1.1 0 1
  · intro h
    have hinv : (!![(1 : K), ϖ⁻¹ * s; ϖ * 0, 1])⁻¹ = !![(1 : K), -(ϖ⁻¹ * s); 0, 1] := by
      rw [inv_fin_two _ (by rw [hdet]; exact isUnit_one), hdet]; ext i j; fin_cases i <;> fin_cases j <;> simp
    refine ⟨⟨fun i j => ?_, by simp⟩, by rw [hdet]; exact isUnit_one, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp [h, one_mem, zero_mem]
    · rw [hinv]; refine ⟨fun i j => ?_, by simp⟩
      fin_cases i <;> fin_cases j <;> simp [h, neg_mem, one_mem, zero_mem]

theorem isB_yRep_inv_mul (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) {k : Matrix (Fin 2) (Fin 2) K} (hk : IsIntU 𝒪 k) (hk11 : IsU 𝒪 (k 1 1)) :
    IsB 𝒪 ϖ ((yRep ϖ (k 0 1 * (k 1 1)⁻¹))⁻¹ * (k * Dm' ϖ)) := by
  set t := k 0 1 * (k 1 1)⁻¹ with ht
  have htO : t ∈ 𝒪 := mul_mem (hk.1 0 1) hk11.inv.mem

  have hkdet := hk.isU_det
  set k' : Matrix (Fin 2) (Fin 2) K := !![k 0 0 - t * k 1 0, 0; k 1 0, k 1 1] with hk'
  have hUk : !![(1 : K), -t; 0, 1] * k = k' := by
    rw [hk']; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ht, hk11.ne_zero] <;> ring
  have hk'det : k'.det = k.det := by
    rw [← hUk, Matrix.det_mul]; simp [Matrix.det_fin_two]
  have hk'00 : IsU 𝒪 (k 0 0 - t * k 1 0) := by

    have e : (k 0 0 - t * k 1 0) = k.det * (k 1 1)⁻¹ := by
      rw [Matrix.det_fin_two, ht]; field_simp [hk11.ne_zero]
    rw [e]; exact hkdet.mul hk11.inv
  have hz : (yRep ϖ t)⁻¹ * (k * Dm' ϖ) = (Dm' ϖ)⁻¹ * k' * Dm' ϖ := by
    rw [yRep_eq hϖ0, Matrix.mul_inv_rev, ← hUk]
    have : (!![(1 : K), t; 0, 1])⁻¹ = !![(1 : K), -t; 0, 1] := by
      rw [inv_fin_two _ (by simp [Matrix.det_fin_two])]; ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two]
    rw [this]; simp only [mul_assoc]
  rw [hz]
  have hconj : (Dm' ϖ)⁻¹ * k' * Dm' ϖ = !![k 0 0 - t * k 1 0, 0; ϖ * k 1 0, k 1 1] := by
    rw [Dm'_inv_conj hϖ0, hk']; ext i j; fin_cases i <;> fin_cases j <;> simp
  have hdetZ : (!![k 0 0 - t * k 1 0, 0; ϖ * k 1 0, k 1 1]).det = k.det := by
    rw [← hk'det, hk']; simp [Matrix.det_fin_two]
  rw [hconj]
  refine ⟨⟨fun i j => ?_, by simpa using mul_mem hϖ (hk.1 1 0) |> fun h => by simpa [mul_comm, ← mul_assoc, hϖ0] using hk.1 1 0⟩,
    by rw [hdetZ]; exact hk.2.1, ?_⟩
  · fin_cases i <;> fin_cases j
    · simpa using hk'00.mem
    · simp [zero_mem]
    · simpa using mul_mem hϖ (hk.1 1 0)
    · simpa using hk.1 1 1
  · rw [inv_fin_two _ (by rw [hdetZ]; exact hk.2.1), hdetZ]
    refine ⟨fun i j => ?_, ?_⟩
    · fin_cases i <;> fin_cases j
      · simpa using mul_mem hkdet.inv.mem (hk.1 1 1)
      · simp [zero_mem]
      · simpa using mul_mem hkdet.inv.mem (neg_mem (mul_mem hϖ (hk.1 1 0)))
      · simpa using mul_mem hkdet.inv.mem hk'00.mem
    · simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.cons_val_zero,
        Matrix.empty_val', Matrix.cons_val_fin_one]
      have : ϖ⁻¹ * (k.det⁻¹ * -(ϖ * k 1 0)) = -(k.det⁻¹ * k 1 0) := by field_simp
      rw [this]; exact neg_mem (mul_mem hkdet.inv.mem (hk.1 1 0))

theorem IsIntU.mul' {y z : Matrix (Fin 2) (Fin 2) K} (hy : IsIntU 𝒪 y) (hz : IsIntU 𝒪 z) : IsIntU 𝒪 (y * z) := by
  refine ⟨hy.1.mul hz.1, by rw [Matrix.det_mul]; exact hy.2.1.mul hz.2.1, ?_⟩
  rw [Matrix.mul_inv_rev]; exact hz.2.2.mul hy.2.2

theorem IsIntU.inv' {y : Matrix (Fin 2) (Fin 2) K} (hy : IsIntU 𝒪 y) : IsIntU 𝒪 y⁻¹ := by
  refine ⟨hy.2.2, ?_, by rw [Matrix.nonsing_inv_nonsing_inv _ hy.2.1]; exact hy.1⟩
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']; exact hy.2.1.ne_zero.isUnit.inv |> fun h => by simpa using h

theorem isIntU_upper {s : K} (hs : s ∈ 𝒪) : IsIntU 𝒪 !![(1 : K), s; 0, 1] := by
  refine ⟨fun i j => ?_, by simp [Matrix.det_fin_two], ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [hs, one_mem, zero_mem]
  · rw [inv_fin_two _ (by simp [Matrix.det_fin_two])]
    intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two, hs, neg_mem, one_mem, zero_mem]

theorem isIntU_lower {s : K} (hs : s ∈ 𝒪) : IsIntU 𝒪 !![(1 : K), 0; s, 1] := by
  refine ⟨fun i j => ?_, by simp [Matrix.det_fin_two], ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [hs, one_mem, zero_mem]
  · rw [inv_fin_two _ (by simp [Matrix.det_fin_two])]
    intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two, hs, neg_mem, one_mem, zero_mem]

theorem isIntU_diag {a d : K} (ha : IsU 𝒪 a) (hd : IsU 𝒪 d) : IsIntU 𝒪 (Matrix.diagonal ![a, d]) := by
  refine ⟨fun i j => ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ha.mem, hd.mem, zero_mem]
  · rw [Matrix.det_diagonal]; simpa using (ha.ne_zero.isUnit.mul hd.ne_zero.isUnit)
  · rw [show (Matrix.diagonal ![a, d])⁻¹ = Matrix.diagonal ![a⁻¹, d⁻¹] from
      Matrix.inv_eq_right_inv (by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [ha.ne_zero, hd.ne_zero])]
    intro i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, ha.inv.mem, hd.inv.mem, zero_mem]

theorem isIntU_swap : IsIntU 𝒪 !![(0 : K), 1; 1, 0] := by
  have hdet : (!![(0 : K), 1; 1, 0]).det = -1 := by simp [Matrix.det_fin_two]
  refine ⟨fun i j => ?_, by rw [hdet]; exact isUnit_one.neg, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem]
  · rw [inv_fin_two _ (by rw [hdet]; exact isUnit_one.neg), hdet]
    intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem]

theorem swap_mul_swap : !![(0 : K), 1; 1, 0] * !![(0 : K), 1; 1, 0] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem snf_of_isU00 (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hmax : ∀ x : K, x ∈ 𝒪 → ¬ IsU 𝒪 x → ϖ⁻¹ * x ∈ 𝒪)
    (m : Matrix (Fin 2) (Fin 2) K) (hmdet : IsUnit m.det)
    (hm1 : IsInt 𝒪 m) (hm2 : IsInt 𝒪 (ϖ • m⁻¹)) (hm3 : ¬ IsInt 𝒪 m⁻¹) (h00 : IsU 𝒪 (m 0 0)) :
    ∃ k₁ k₂ : Matrix (Fin 2) (Fin 2) K, IsIntU 𝒪 k₁ ∧ IsIntU 𝒪 k₂ ∧ m = k₁ * Dm ϖ * k₂ := by
  set a := m 0 0 with ha
  set d := m 1 1 - m 1 0 * a⁻¹ * m 0 1 with hd
  have hdet : m.det = a * d := by rw [Matrix.det_fin_two, hd, ← ha]; field_simp [h00.ne_zero]
  have hdO : d ∈ 𝒪 := sub_mem (hm1 1 1) (mul_mem (mul_mem (hm1 1 0) h00.inv.mem) (hm1 0 1))
  have hd0 : d ≠ 0 := by intro h; apply hmdet.ne_zero; rw [hdet, h, mul_zero]

  set L : Matrix (Fin 2) (Fin 2) K := !![(1 : K), 0; -(m 1 0 * a⁻¹), 1] with hL
  set Rt : Matrix (Fin 2) (Fin 2) K := !![(1 : K), -(a⁻¹ * m 0 1); 0, 1] with hRt
  have hLU : IsIntU 𝒪 L := isIntU_lower (neg_mem (mul_mem (hm1 1 0) h00.inv.mem))
  have hRtU : IsIntU 𝒪 Rt := isIntU_upper (neg_mem (mul_mem h00.inv.mem (hm1 0 1)))
  have hLmR : L * m * Rt = Matrix.diagonal ![a, d] := by
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;>
      simp [hL, hRt, Matrix.diagonal, ← ha, hd] <;> (try field_simp [h00.ne_zero]) <;> (try ring)

  have hdu : ¬ IsU 𝒪 d := by
    intro hdu
    apply hm3
    have hdiag : IsIntU 𝒪 (Matrix.diagonal ![a, d]) := isIntU_diag h00 hdu
    have : m = L⁻¹ * Matrix.diagonal ![a, d] * Rt⁻¹ := by
      rw [← hLmR]; simp only [← mul_assoc]
      rw [Matrix.nonsing_inv_mul _ hLU.2.1, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hRtU.2.1, mul_one]
    rw [this]; exact ((hLU.inv'.mul' hdiag).mul' hRtU.inv').2.2
  have hϖd : ϖ * d⁻¹ ∈ 𝒪 := by

    have hint : IsInt 𝒪 (Rt⁻¹ * (ϖ • m⁻¹) * L⁻¹) := (hRtU.2.2.mul hm2).mul hLU.2.2
    have e : Rt⁻¹ * (ϖ • m⁻¹) * L⁻¹ = ϖ • (L * m * Rt)⁻¹ := by
      rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_smul, Matrix.smul_mul, mul_assoc]
    rw [e, hLmR, show (Matrix.diagonal ![a, d])⁻¹ = Matrix.diagonal ![a⁻¹, d⁻¹] from
      Matrix.inv_eq_right_inv (by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; ext i; fin_cases i <;> simp [h00.ne_zero, hd0])] at hint
    simpa [Matrix.diagonal] using hint 1 1
  have hu : IsU 𝒪 (ϖ⁻¹ * d) :=
    isU_of_mem_of_inv_mem (hmax d hdO hdu) (by rw [_root_.mul_inv_rev, inv_inv, mul_comm]; exact hϖd) (mul_ne_zero (inv_ne_zero hϖ0) hd0)

  have hsplit : Matrix.diagonal ![a, d] = Dm ϖ * Matrix.diagonal ![a, ϖ⁻¹ * d] := by
    rw [Dm, Matrix.diagonal_mul_diagonal]; congr 1; ext i; fin_cases i <;> simp [hϖ0]
  refine ⟨L⁻¹, Matrix.diagonal ![a, ϖ⁻¹ * d] * Rt⁻¹, hLU.inv', (isIntU_diag h00 hu).mul' hRtU.inv', ?_⟩
  rw [mul_assoc, ← mul_assoc (Dm ϖ), ← hsplit, ← hLmR]; simp only [← mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hLU.2.1, one_mul, mul_assoc, Matrix.mul_nonsing_inv _ hRtU.2.1, mul_one]

theorem snf (hϖ0 : ϖ ≠ 0) (hϖ : ϖ ∈ 𝒪) (hmax : ∀ x : K, x ∈ 𝒪 → ¬ IsU 𝒪 x → ϖ⁻¹ * x ∈ 𝒪)
    (m : Matrix (Fin 2) (Fin 2) K) (hmdet : IsUnit m.det)
    (hm1 : IsInt 𝒪 m) (hm2 : IsInt 𝒪 (ϖ • m⁻¹)) (hm3 : ¬ IsInt 𝒪 m⁻¹) (hm4 : ¬ IsInt 𝒪 (ϖ⁻¹ • m)) :
    ∃ k₁ k₂ : Matrix (Fin 2) (Fin 2) K, IsIntU 𝒪 k₁ ∧ IsIntU 𝒪 k₂ ∧ m = k₁ * Dm ϖ * k₂ := by

  have hex : ∃ i j, IsU 𝒪 (m i j) := by
    by_contra hno
    push_neg at hno
    exact hm4 fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact hmax _ (hm1 i j) (hno i j)
  obtain ⟨i, j, hij⟩ := hex
  set σ : Matrix (Fin 2) (Fin 2) K := !![(0 : K), 1; 1, 0] with hσ
  have hσU : IsIntU 𝒪 σ := isIntU_swap
  have hσσ : σ * σ = 1 := swap_mul_swap
  have hσinv : σ⁻¹ = σ := Matrix.inv_eq_right_inv hσσ

  obtain ⟨P, Q, hP, hQ, hPP, hQQ, h00⟩ : ∃ P Q : Matrix (Fin 2) (Fin 2) K, IsIntU 𝒪 P ∧ IsIntU 𝒪 Q ∧ P * P = 1 ∧ Q * Q = 1 ∧
      IsU 𝒪 ((P * m * Q) 0 0) := by
    have h1U : IsIntU 𝒪 (1 : Matrix (Fin 2) (Fin 2) K) := ⟨IsInt.one, by simp, by rw [inv_one]; exact IsInt.one⟩
    fin_cases i <;> fin_cases j
    · exact ⟨1, 1, h1U, h1U, one_mul 1, one_mul 1, by simpa using hij⟩
    · exact ⟨1, σ, h1U, hσU, one_mul 1, hσσ, by rw [one_mul, Matrix.mul_apply, Fin.sum_univ_two, hσ]; simpa using hij⟩
    · exact ⟨σ, 1, hσU, h1U, hσσ, one_mul 1, by rw [mul_one, Matrix.mul_apply, Fin.sum_univ_two, hσ]; simpa using hij⟩
    · exact ⟨σ, σ, hσU, hσU, hσσ, hσσ, by rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two, hσ]; simpa using hij⟩
  have hPinv : P⁻¹ = P := Matrix.inv_eq_right_inv hPP
  have hQinv : Q⁻¹ = Q := Matrix.inv_eq_right_inv hQQ
  set m' := P * m * Q with hm'
  have hm'det : IsUnit m'.det := by rw [hm', Matrix.det_mul, Matrix.det_mul]; exact (hP.2.1.mul hmdet).mul hQ.2.1
  have hm'inv : m'⁻¹ = Q * m⁻¹ * P := by rw [hm', Matrix.mul_inv_rev, Matrix.mul_inv_rev, hPinv, hQinv, mul_assoc]
  have hback : m = P * m' * Q := by
    rw [hm', ← mul_assoc, ← mul_assoc, hPP, one_mul, mul_assoc, hQQ, mul_one]
  have hm'1 : IsInt 𝒪 m' := (hP.1.mul hm1).mul hQ.1
  have hm'2 : IsInt 𝒪 (ϖ • m'⁻¹) := by
    rw [hm'inv, show ϖ • (Q * m⁻¹ * P) = Q * (ϖ • m⁻¹) * P by rw [Matrix.mul_smul, Matrix.smul_mul]]; exact (hQ.1.mul hm2).mul hP.1
  have hm'3 : ¬ IsInt 𝒪 m'⁻¹ := by
    intro h; apply hm3
    have : m⁻¹ = Q * m'⁻¹ * P := by rw [hm'inv, ← mul_assoc, ← mul_assoc, hQQ, one_mul, mul_assoc, hPP, mul_one]
    rw [this]; exact (hQ.1.mul h).mul hP.1
  obtain ⟨k₁, k₂, hk₁, hk₂, hsnf⟩ := snf_of_isU00 hϖ0 hϖ hmax m' hm'det hm'1 hm'2 hm'3 h00
  refine ⟨P * k₁, k₂ * Q, hP.mul' hk₁, hk₂.mul' hQ, ?_⟩
  rw [hback, hsnf]; simp only [mul_assoc]

end pi

end F3LOC

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField
open Matrix

namespace F3LOC

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))

local notation "Kv" => HeightOneSpectrum.adicCompletion ℚ v
local notation "Ov" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "Dv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v

section unif

theorem isU_iff (x : Kv) : IsU (Ov) x ↔ Valued.v x = 1 := by
  constructor
  · intro h
    have h1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp h.mem
    have h2 : Valued.v x⁻¹ ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mp h.inv.mem
    rw [map_inv₀] at h2
    have h0 : Valued.v x ≠ 0 := by rw [ne_eq, map_eq_zero]; exact h.ne_zero
    exact le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.mpr h0)).mp h2)
  · intro h
    have hx0 : x ≠ 0 := by intro hx; rw [hx, map_zero] at h; exact zero_ne_one h
    refine isU_of_mem_of_inv_mem ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).mpr h.le) ?_ hx0
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]

variable (q : ℕ) (hq : q.Prime) (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)

theorem natCast_mem_Ov : ((q : ℕ) : Kv) ∈ Ov := _root_.natCast_mem _ q

include hq in
theorem natCast_ne_zero' : ((q : ℕ) : Kv) ≠ 0 := by
  haveI : CharZero (Kv) := charZero_of_injective_algebraMap (algebraMap ℚ (Kv)).injective
  exact_mod_cast hq.ne_zero

include hq hqv

theorem valued_natCast_eq_exp_neg_one : Valued.v ((q : ℕ) : Kv) = WithZero.exp (-1 : ℤ) := by
  have hspan : v.asIdeal = Ideal.span {((q : ℕ) : 𝓞 ℚ)} :=
    ((Nat.isMaximal_span_natCast_of_prime hq).eq_of_le v.isPrime.ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hqv)).symm
  have hq0 : ((q : ℕ) : 𝓞 ℚ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have h1 : ((q : ℕ) : Kv) = algebraMap (𝓞 ℚ) (Kv) ((q : ℕ) : 𝓞 ℚ) := by rw [map_natCast]
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) v ((q : ℕ) : 𝓞 ℚ)
  erw [h2, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_singleton _ hq0 hspan]

theorem not_isU_natCast : ¬ IsU (Ov) ((q : ℕ) : Kv) := by
  rw [isU_iff, valued_natCast_eq_exp_neg_one v q hq hqv]; decide

theorem hmax_natCast (x : Kv) (hx : x ∈ Ov) (hu : ¬ IsU (Ov) x) : ((q : ℕ) : Kv)⁻¹ * x ∈ Ov := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  by_cases hx0 : x = 0
  · rw [hx0, mul_zero, map_zero]; exact zero_le'
  have hV0 : Valued.v x ≠ 0 := by rwa [ne_eq, map_eq_zero]
  obtain ⟨n, hn⟩ : ∃ n : ℤ, Valued.v x = WithZero.exp n := ⟨WithZero.log (Valued.v x), (WithZero.exp_log hV0).symm⟩
  have hne : Valued.v x ≠ 1 := by rw [isU_iff] at hu; exact hu
  rw [map_mul, map_inv₀, valued_natCast_eq_exp_neg_one v q hq hqv, hn, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  rw [hn, ← WithZero.exp_zero, WithZero.exp_le_exp] at hx
  rw [hn, ← WithZero.exp_zero, ne_eq, WithZero.exp_inj] at hne
  omega

end unif

section psi

variable (φ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
  (P : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))

noncomputable def psiP (x : Dv) : Matrix (Fin 2) (Fin 2) Kv := P⁻¹ * φ x * P

variable {P} (hP : IsUnit P.det)
include hP

theorem psiP_mul (x y : Dv) : psiP v φ P (x * y) = psiP v φ P x * psiP v φ P y := by
  unfold psiP; rw [map_mul]; simp only [mul_assoc]; rw [← mul_assoc P P⁻¹, Matrix.mul_nonsing_inv _ hP, one_mul]

theorem psiP_one : psiP v φ P 1 = 1 := by
  unfold psiP; rw [map_one, mul_one, Matrix.nonsing_inv_mul _ hP]

theorem psiP_surj (Y : Matrix (Fin 2) (Fin 2) Kv) : ∃ x : Dv, psiP v φ P x = Y := by
  refine ⟨φ.symm (P * Y * P⁻¹), ?_⟩
  unfold psiP; rw [RingEquiv.apply_symm_apply]; simp only [mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hP, mul_one, ← mul_assoc, Matrix.nonsing_inv_mul _ hP, one_mul]

theorem psiP_injective : Function.Injective (psiP v φ P) := by
  intro x y h
  unfold psiP at h
  have : φ x = φ y := by
    have h' := congrArg (fun Z => P * Z * P⁻¹) h
    simp only [mul_assoc] at h'
    rwa [Matrix.mul_nonsing_inv _ hP, mul_one, mul_one, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ hP, one_mul, one_mul] at h'
  exact φ.injective this

theorem psiP_units_inv (g : (Dv)ˣ) : psiP v φ P ((g⁻¹ : (Dv)ˣ) : Dv) = (psiP v φ P (g : Dv))⁻¹ := by
  symm; apply Matrix.inv_eq_left_inv
  rw [← psiP_mul v φ hP, Units.inv_mul, psiP_one v φ hP]

theorem isUnit_det_psiP (g : (Dv)ˣ) : IsUnit (psiP v φ P (g : Dv)).det := by
  apply Matrix.isUnit_det_of_left_inverse (B := psiP v φ P ((g⁻¹ : (Dv)ˣ) : Dv))
  rw [← psiP_mul v φ hP, Units.inv_mul, psiP_one v φ hP]

variable (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ v, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)))
include hφ

theorem psiP_ratSmul (c : ℚ) (x : Dv) : psiP v φ P (c • x) = (c : Kv) • psiP v φ P x := by
  have e : c • x = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (c : Kv)) * x := by
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, mul_zero]
    | tmul z s =>
        rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def,
          eq_ratCast]
    | add x y hx hy => rw [smul_add, mul_add, hx, hy]
  unfold psiP
  rw [e, map_mul, hφ, Matrix.smul_mul, one_mul, Matrix.mul_smul, Matrix.smul_mul]

end psi

section dict

variable (φ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
  {P : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)} (hP : IsUnit P.det)
  (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ v, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)))
  {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
  (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (q : ℕ) (hq0 : ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) ≠ 0)
  (hq : ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) ∈ HeightOneSpectrum.adicCompletionIntegers ℚ v)

  (hRv : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v,
      x ∈ Submodule.localBox R v ↔ IsInt (HeightOneSpectrum.adicCompletionIntegers ℚ v) (psiP v φ P x))
  (hR'v : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v,
      x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔
        IsInt (HeightOneSpectrum.adicCompletionIntegers ℚ v) ((Dm ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))⁻¹ * psiP v φ P x * Dm ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)))

local notation "ϖ" => ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)
local notation "ψ" => psiP v φ P
local notation "Sv" => Submodule.localBox (CerednikDrinfeld.meetOrder R n) v

include hR in
theorem isOrder_meetOrder : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n) :=
  hR.inf (QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n)

include hR hq0 hq hRv hR'v in

theorem mem_Sv_iff (x : Dv) : x ∈ Sv ↔ IsIw (Ov) ϖ (ψ x) := by
  have hRc := QuaternionAlgebra.IsOrder.conjByFiniteIdele R hR n
  rw [show CerednikDrinfeld.meetOrder R n = R ⊓ Submodule.conjByFiniteIdele R n from rfl,
    Submodule.localBox_inf R _ hR.fg hR.spanTop hRc.fg hRc.spanTop v, AddSubgroup.mem_inf, hRv, hR'v,
    isIw_iff_isInt_and hq0 hq]

include hR in

private theorem _root_.F3LOC.mem_stabilizer_iff (u : (Dv)ˣ) :
    u ∈ MulAction.stabilizer (Dv)ˣ ((Sv : AddSubgroup (Dv)) : Set (Dv)) ↔ (u : Dv) ∈ Sv ∧ ((u⁻¹ : (Dv)ˣ) : Dv) ∈ Sv := by
  have hS := isOrder_meetOrder hR n
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have h1 : (u : Dv) ∈ Sv := by
      have : (u : Dv) • (1 : Dv) ∈ u • ((Sv : AddSubgroup (Dv)) : Set (Dv)) := Set.smul_mem_smul_set (HeckeLocal.one_mem_localBox hS v)
      rw [h] at this; simpa using this
    have h2 : ((u⁻¹ : (Dv)ˣ) : Dv) ∈ Sv := by
      have : (1 : Dv) ∈ u • ((Sv : AddSubgroup (Dv)) : Set (Dv)) := by rw [h]; exact HeckeLocal.one_mem_localBox hS v
      obtain ⟨s, hs, hs1⟩ := this
      have : s = ((u⁻¹ : (Dv)ˣ) : Dv) := by
        simp only [Units.smul_def, smul_eq_mul] at hs1
        calc s = ((u⁻¹ : (Dv)ˣ) : Dv) * ((u : Dv) * s) := by rw [← mul_assoc, Units.inv_mul, one_mul]
          _ = _ := by rw [hs1, mul_one]
      rw [← this]; exact hs
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    apply Set.Subset.antisymm
    · rintro _ ⟨s, hs, rfl⟩
      simp only [Units.smul_def, smul_eq_mul]; exact HeckeLocal.localBox_mul_mem hS v h1 hs
    · intro s hs
      refine ⟨((u⁻¹ : (Dv)ˣ) : Dv) * s, HeckeLocal.localBox_mul_mem hS v h2 hs, ?_⟩
      simp only [Units.smul_def, smul_eq_mul]; rw [← mul_assoc, Units.mul_inv, one_mul]

p2m_export "F3LOC" "mem_stabilizer_iff"
include hR hq0 hq hRv hR'v hP in

theorem mem_stabilizer_iff_isB (u : (Dv)ˣ) :
    u ∈ MulAction.stabilizer (Dv)ˣ ((Sv : AddSubgroup (Dv)) : Set (Dv)) ↔ IsB (Ov) ϖ (ψ (u : Dv)) := by
  rw [mem_stabilizer_iff v hR n u, mem_Sv_iff v φ hR n q hq0 hq hRv hR'v, mem_Sv_iff v φ hR n q hq0 hq hRv hR'v,
    psiP_units_inv v φ hP, IsB]
  exact ⟨fun h => ⟨h.1, isUnit_det_psiP v φ hP u, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

include hq0 hq hRv hR'v hP hφ hR in

theorem clause_i_iff (g : (Dv)ˣ) :
    ((g : Dv) ∈ Sv ∧ (q : ℚ) • ((g⁻¹ : (Dv)ˣ) : Dv) ∈ Sv ∧ ((g⁻¹ : (Dv)ˣ) : Dv) ∉ Sv ∧ (q : ℚ)⁻¹ • (g : Dv) ∉ Sv) ↔
      (IsIw (Ov) ϖ (ψ g) ∧ IsIw (Ov) ϖ (ϖ • (ψ g)⁻¹) ∧ ¬ IsIw (Ov) ϖ (ψ g)⁻¹ ∧ ¬ IsIw (Ov) ϖ (ϖ⁻¹ • ψ g)) := by
  haveI : CharZero (Kv) := charZero_of_injective_algebraMap (algebraMap ℚ (Kv)).injective
  simp only [mem_Sv_iff v φ hR n q hq0 hq hRv hR'v, psiP_ratSmul v φ hP hφ, psiP_units_inv v φ hP, Rat.cast_inv,
    Rat.cast_natCast]

include hq0 hRv hR'v hP in

theorem clause_ii_iff (g : (Dv)ˣ) :
    (∀ x : Dv, ((g⁻¹ : (Dv)ˣ) : Dv) * x * g ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔ x ∈ Submodule.localBox R v) ↔
      (∀ Y : Matrix (Fin 2) (Fin 2) Kv, IsInt (Ov) ((Dm ϖ)⁻¹ * ((ψ g)⁻¹ * Y * ψ g) * Dm ϖ) ↔ IsInt (Ov) Y) := by
  constructor
  · intro h Y
    obtain ⟨x, rfl⟩ := psiP_surj v φ hP Y
    rw [← hRv x, ← h x, hR'v, psiP_mul v φ hP, psiP_mul v φ hP, psiP_units_inv v φ hP]
  · intro h x
    rw [hR'v, hRv, psiP_mul v φ hP, psiP_mul v φ hP, psiP_units_inv v φ hP]
    exact h _

include hq0 hRv hR'v hP in

theorem clause_iii_iff (g : (Dv)ˣ) :
    (¬ ∀ x : Dv, ((g⁻¹ : (Dv)ˣ) : Dv) * x * g ∈ Submodule.localBox R v ↔ x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v) ↔
      (¬ ∀ Y : Matrix (Fin 2) (Fin 2) Kv, IsInt (Ov) ((ψ g)⁻¹ * Y * ψ g) ↔ IsInt (Ov) ((Dm ϖ)⁻¹ * Y * Dm ϖ)) := by
  refine not_congr ⟨fun h Y => ?_, fun h x => ?_⟩
  · obtain ⟨x, rfl⟩ := psiP_surj v φ hP Y
    rw [← psiP_units_inv v φ hP, ← psiP_mul v φ hP, ← psiP_mul v φ hP, ← hRv, ← hR'v]; exact h x
  · rw [hRv, hR'v, psiP_mul v φ hP, psiP_mul v φ hP, psiP_units_inv v φ hP]; exact h _

end dict

section unitOf

variable (φ : (ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
  {P : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)} (hP : IsUnit P.det)
include hP

noncomputable def unitOf (Y : Matrix (Fin 2) (Fin 2) Kv) (hY : IsUnit Y.det) : (Dv)ˣ where
  val := φ.symm (P * Y * P⁻¹)
  inv := φ.symm (P * Y⁻¹ * P⁻¹)
  val_inv := by
    rw [← map_mul, show P * Y * P⁻¹ * (P * Y⁻¹ * P⁻¹) = 1 by
      rw [show P * Y * P⁻¹ * (P * Y⁻¹ * P⁻¹) = P * (Y * (P⁻¹ * P) * Y⁻¹) * P⁻¹ by simp only [mul_assoc],
        Matrix.nonsing_inv_mul _ hP, mul_one, Matrix.mul_nonsing_inv _ hY, mul_one, Matrix.mul_nonsing_inv _ hP], map_one]
  inv_val := by
    rw [← map_mul, show P * Y⁻¹ * P⁻¹ * (P * Y * P⁻¹) = 1 by
      rw [show P * Y⁻¹ * P⁻¹ * (P * Y * P⁻¹) = P * (Y⁻¹ * (P⁻¹ * P) * Y) * P⁻¹ by simp only [mul_assoc],
        Matrix.nonsing_inv_mul _ hP, mul_one, Matrix.nonsing_inv_mul _ hY, mul_one, Matrix.mul_nonsing_inv _ hP], map_one]

theorem psiP_unitOf (Y : Matrix (Fin 2) (Fin 2) Kv) (hY : IsUnit Y.det) : psiP v φ P (unitOf v φ hP Y hY : Dv) = Y := by
  show P⁻¹ * φ (φ.symm (P * Y * P⁻¹)) * P = Y
  rw [RingEquiv.apply_symm_apply]; simp only [mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hP, mul_one, ← mul_assoc, Matrix.nonsing_inv_mul _ hP, one_mul]

end unitOf

theorem mem_localBox_conj_iff' {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    (g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x : Dv) :
    x ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ g) v ↔
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _)) * x *
        Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (g : _) ∈ Submodule.localBox Λ v := by
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff (D := ℍ[ℚ, a, b]) Λ hΛ.fg hΛ.spanTop g v x]
  have hgi : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _)) *
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (g : _) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hgi' : Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (g : _) *
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : _)) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← mul_assoc, ← mul_assoc, hgi, one_mul, mul_assoc, hgi, mul_one]; exact hy
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, ← mul_assoc, hgi', one_mul, mul_assoc, hgi', mul_one]⟩

section main

open QuaternionAlgebra CerednikDrinfeld

theorem local_clauses_of_mem_primeHeckeSet {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
    (q : ℕ) (hq : q.Prime) {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hnH : n ∈ primeHeckeSet R q)
    (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (n : _) ∈ Submodule.localBox R v ∧
    (q : ℚ) • Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) : _) ∈ Submodule.localBox R v ∧
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) : _) ∉ Submodule.localBox R v ∧
    (q : ℚ)⁻¹ • Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (n : _) ∉ Submodule.localBox R v := by
  have hbox := fun x => Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox (D := ℍ[ℚ, a, b]) R hR.fg hR.spanTop x
  obtain ⟨h1, h2, h3, h4⟩ := hnH
  rw [hbox] at h1 h2 h3 h4

  have huniq : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → w ∉ Nat.placesOf q := by
    intro w hw hmem; rw [Nat.mem_placesOf_iff hq.ne_zero] at hmem
    exact hw (Nat.HeightOneSpectrum.eq_of_natCast_prime_mem hq hmem hqv)
  have hunit : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w).toRingHom.toMonoidHom n ∈ Submodule.localBoxUnits R w :=
    fun w hw => GOODEQ.unitsMap_mem_localBoxUnits_of_mem_primeHeckeSet hq.ne_zero ⟨by rwa [hbox], by rwa [hbox], by rwa [hbox], by rwa [hbox]⟩ (huniq w hw)
  refine ⟨h1 v, by simpa only [map_smul] using h2 v, ?_, ?_⟩
  · intro hv; apply h3; intro w
    by_cases hw : w = v
    · subst hw; exact hv
    · have := (Submodule.mem_localBoxUnits_iff _ _ _).mp (hunit w hw)
      simpa [Units.coe_map_inv] using this.2
  · intro hv; apply h4; intro w
    rw [map_smul]
    by_cases hw : w = v
    · subst hw; exact hv
    · have hu := (Submodule.mem_localBoxUnits_iff _ _ _).mp (hunit w hw)
      have hqw : algebraMap ℚ (w.adicCompletion ℚ) ((q : ℚ)⁻¹) ∈ w.adicCompletionIntegers ℚ :=
        Nat.inv_natCast_mem_adicCompletionIntegers_of_not_mem_placesOf hq.ne_zero (huniq w hw)
      have := GOODEQ.smul_mem_localBox w hqw (by simpa [Units.coe_map] using hu.1)
      exact this

theorem main {q' : ℕ} (hq' : q'.Prime) (hB : IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : IsEichlerOrder R N)
    (q : ℕ) (hq : q.Prime) (hqq' : q ≠ q') (hqN : ¬ q ∣ N)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hnH : n ∈ primeHeckeSet R q)
    (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Set.ncard {c : (Dv)ˣ ⧸ MulAction.stabilizer (Dv)ˣ ((Submodule.localBox (meetOrder R n) v : AddSubgroup (Dv)) : Set (Dv)) |
      ∃ g : (Dv)ˣ,
        ((g : Dv) ∈ Submodule.localBox (meetOrder R n) v ∧
          (q : ℚ) • ((g⁻¹ : (Dv)ˣ) : Dv) ∈ Submodule.localBox (meetOrder R n) v ∧
          ((g⁻¹ : (Dv)ˣ) : Dv) ∉ Submodule.localBox (meetOrder R n) v ∧
          (q : ℚ)⁻¹ • (g : Dv) ∉ Submodule.localBox (meetOrder R n) v) ∧
        (∀ x : Dv, ((g⁻¹ : (Dv)ˣ) : _) * x * g ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔ x ∈ Submodule.localBox R v) ∧
        (¬ ∀ x : Dv, ((g⁻¹ : (Dv)ˣ) : _) * x * g ∈ Submodule.localBox R v ↔ x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v) ∧
        (g : (Dv)ˣ ⧸ MulAction.stabilizer (Dv)ˣ ((Submodule.localBox (meetOrder R n) v : AddSubgroup (Dv)) : Set (Dv))) = c} = q := by
  classical
  haveI : CharZero (Kv) := charZero_of_injective_algebraMap (algebraMap ℚ (Kv)).injective

  have hϖ0 : ((q : ℕ) : Kv) ≠ 0 := natCast_ne_zero' v q hq
  have hϖO : ((q : ℕ) : Kv) ∈ Ov := natCast_mem_Ov v q
  have hϖu : ¬ IsU (Ov) ((q : ℕ) : Kv) := not_isU_natCast v q hq hqv
  have hmax := hmax_natCast v q hq hqv

  obtain ⟨φ, hφ⟩ := C8N.LocalAtQ.exists_splitting v hq' hB q hq hqq' hqv
  obtain ⟨Λ₁, Λ₂, hΛ₁, hΛ₂, hR12, hidx⟩ := id hR
  have hle₁ : R ≤ Λ₁ := by rw [hR12]; exact inf_le_left
  have hRo : IsOrder R := by rw [hR12]; exact hΛ₁.isOrder.inf hΛ₂.isOrder
  have hbox : Submodule.localBox Λ₁ v = Submodule.localBox R v :=
    IsEichlerOrder.localBox_eq_localBox_of_isMaximalOrder_of_le_of_not_dvd hq' hB hR q hq hqq' hqN v hqv hΛ₁ hle₁
  obtain ⟨h, hh⟩ := hΛ₁.exists_localBox_iff_generalLinearGroup_conj_mem_adicCompletionIntegers v φ hφ
  have hhdet : IsUnit (h : Matrix (Fin 2) (Fin 2) Kv).det := (Matrix.isUnits_det_units h)
  have hRvh : ∀ x : Dv, x ∈ Submodule.localBox R v ↔ IsInt (Ov) (psiP v φ (h : Matrix (Fin 2) (Fin 2) Kv) x) := by
    intro x; rw [← hbox, hh x]; unfold psiP IsInt; rw [← Matrix.coe_units_inv]

  obtain ⟨hn1, hn2, hn3, hn4⟩ := local_clauses_of_mem_primeHeckeSet v hRo q hq hnH hqv
  set nv : (Dv)ˣ := Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n with hnv
  have hnv_val : (nv : Dv) = Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (n : _) := rfl
  have hnv_inv : ((nv⁻¹ : (Dv)ˣ) : Dv) = Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v (((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)) : _) := by
    rw [hnv, Units.coe_map_inv]; rfl
  set m := psiP v φ (h : Matrix (Fin 2) (Fin 2) Kv) (nv : Dv) with hm
  have hmdet : IsUnit m.det := isUnit_det_psiP v φ hhdet nv
  have hm1 : IsInt (Ov) m := (hRvh _).mp hn1
  have hm2 : IsInt (Ov) (((q : ℕ) : Kv) • m⁻¹) := by
    have := (hRvh _).mp hn2
    rwa [psiP_ratSmul v φ hhdet hφ, ← hnv_inv, psiP_units_inv v φ hhdet, Rat.cast_natCast] at this
  have hm3 : ¬ IsInt (Ov) m⁻¹ := by
    intro h'; apply hn3; rw [hRvh, ← hnv_inv, psiP_units_inv v φ hhdet]; exact h'
  have hm4 : ¬ IsInt (Ov) (((q : ℕ) : Kv)⁻¹ • m) := by
    intro h'; apply hn4; rw [hRvh, psiP_ratSmul v φ hhdet hφ, Rat.cast_inv, Rat.cast_natCast]; exact h'
  obtain ⟨k₁, k₂, hk₁, hk₂, hsnf⟩ := snf hϖ0 hϖO hmax m hmdet hm1 hm2 hm3 hm4

  set P : Matrix (Fin 2) (Fin 2) Kv := (h : Matrix (Fin 2) (Fin 2) Kv) * k₁ with hPdef
  have hP : IsUnit P.det := by rw [hPdef, Matrix.det_mul]; exact hhdet.mul hk₁.2.1
  have hψP : ∀ x : Dv, psiP v φ P x = k₁⁻¹ * psiP v φ (h : Matrix (Fin 2) (Fin 2) Kv) x * k₁ := by
    intro x; unfold psiP; rw [hPdef, Matrix.mul_inv_rev]; simp only [mul_assoc]
  have hRv : ∀ x : Dv, x ∈ Submodule.localBox R v ↔ IsInt (Ov) (psiP v φ P x) := by
    intro x; rw [hRvh, hψP, hk₁.isInt_conj_iff]
  have hR'v : ∀ x : Dv, x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔
      IsInt (Ov) ((Dm ((q : ℕ) : Kv))⁻¹ * psiP v φ P x * Dm ((q : ℕ) : Kv)) := by
    intro x
    rw [mem_localBox_conj_iff' v hRo n x, hRv, ← hnv_val, ← hnv_inv, psiP_mul v φ hP, psiP_mul v φ hP, psiP_units_inv v φ hP]

    have e : psiP v φ P (nv : Dv) = Dm ((q : ℕ) : Kv) * (k₂ * k₁) := by
      rw [hψP, ← hm, hsnf]; simp only [mul_assoc]; rw [← mul_assoc k₁⁻¹, Matrix.nonsing_inv_mul _ hk₁.2.1, one_mul]
    have hkk : IsIntU (Ov) (k₂ * k₁) := hk₂.mul' hk₁
    have hDdet : IsUnit (Dm ((q : ℕ) : Kv)).det := by rw [det_Dm hϖ0]; exact hϖ0.isUnit
    rw [e, Matrix.mul_inv_rev, show (k₂ * k₁)⁻¹ * (Dm ((q : ℕ) : Kv))⁻¹ * psiP v φ P x * (Dm ((q : ℕ) : Kv) * (k₂ * k₁))
        = (k₂ * k₁)⁻¹ * ((Dm ((q : ℕ) : Kv))⁻¹ * psiP v φ P x * Dm ((q : ℕ) : Kv)) * (k₂ * k₁) by simp only [mul_assoc],
      hkk.isInt_conj_iff]

  set H := MulAction.stabilizer (Dv)ˣ ((Submodule.localBox (meetOrder R n) v : AddSubgroup (Dv)) : Set (Dv)) with hH
  have hmemH : ∀ u : (Dv)ˣ, u ∈ H ↔ IsB (Ov) ((q : ℕ) : Kv) (psiP v φ P (u : Dv)) :=
    fun u => mem_stabilizer_iff_isB v φ hP hRo n q hϖ0 hϖO hRv hR'v u

  have hYdet : ∀ t : Kv, IsUnit (yRep ((q : ℕ) : Kv) t).det := fun t => by rw [det_yRep hϖ0]; exact hϖ0.isUnit
  let gRep : Ov → (Dv)ˣ := fun t => unitOf v φ hP (yRep ((q : ℕ) : Kv) (t : Kv)) (hYdet _)
  have hgRep : ∀ t : Ov, psiP v φ P (gRep t : Dv) = yRep ((q : ℕ) : Kv) (t : Kv) := fun t => psiP_unitOf v φ hP _ _
  let F : Ov → (Dv)ˣ ⧸ H := fun t => (gRep t : (Dv)ˣ ⧸ H)

  have hker : ∀ s t : Ov, F s = F t ↔ ((q : ℕ) : Kv)⁻¹ * ((t : Kv) - (s : Kv)) ∈ Ov := by
    intro s t
    show ((gRep s : (Dv)ˣ ⧸ H)) = (gRep t : (Dv)ˣ ⧸ H) ↔ _
    rw [QuotientGroup.eq, hmemH, Units.val_mul, psiP_mul v φ hP, psiP_units_inv v φ hP, hgRep, hgRep,
      yRep_eq hϖ0, yRep_eq hϖ0, Matrix.mul_inv_rev,
      show (Dm' ((q : ℕ) : Kv))⁻¹ * (!![(1 : Kv), (s : Kv); 0, 1])⁻¹ * (!![(1 : Kv), (t : Kv); 0, 1] * Dm' ((q : ℕ) : Kv))
        = (Dm' ((q : ℕ) : Kv))⁻¹ * ((!![(1 : Kv), (s : Kv); 0, 1])⁻¹ * !![(1 : Kv), (t : Kv); 0, 1]) * Dm' ((q : ℕ) : Kv) by simp only [mul_assoc],
      show (!![(1 : Kv), (s : Kv); 0, 1])⁻¹ * !![(1 : Kv), (t : Kv); 0, 1] = !![(1 : Kv), (t : Kv) - (s : Kv); 0, 1] by
        rw [inv_fin_two _ (by simp [Matrix.det_fin_two])]; ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.det_fin_two, Matrix.mul_apply] <;> ring]
    exact isB_conj_unipotent_iff hϖ0 (sub_mem t.2 s.2)

  have hclause_i := clause_i_iff v φ hP hφ hRo n q hϖ0 hϖO hRv hR'v
  have hclause_ii := clause_ii_iff v φ hP (R := R) n q hϖ0 hRv hR'v
  have hclause_iii := clause_iii_iff v φ hP (R := R) n q hϖ0 hRv hR'v
  have hrange : Set.range F = {c : (Dv)ˣ ⧸ H | ∃ g : (Dv)ˣ,
        ((g : Dv) ∈ Submodule.localBox (meetOrder R n) v ∧
          (q : ℚ) • ((g⁻¹ : (Dv)ˣ) : Dv) ∈ Submodule.localBox (meetOrder R n) v ∧
          ((g⁻¹ : (Dv)ˣ) : Dv) ∉ Submodule.localBox (meetOrder R n) v ∧
          (q : ℚ)⁻¹ • (g : Dv) ∉ Submodule.localBox (meetOrder R n) v) ∧
        (∀ x : Dv, ((g⁻¹ : (Dv)ˣ) : _) * x * g ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔ x ∈ Submodule.localBox R v) ∧
        (¬ ∀ x : Dv, ((g⁻¹ : (Dv)ˣ) : _) * x * g ∈ Submodule.localBox R v ↔ x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v) ∧
        (g : (Dv)ˣ ⧸ H) = c} := by
    apply Set.Subset.antisymm
    · rintro _ ⟨t, rfl⟩
      refine ⟨gRep t, ?_, ?_, ?_, rfl⟩
      · rw [hclause_i, hgRep]
        exact ⟨isIw_yRep hϖ0 hϖO t.2, isIw_smul_yRep_inv hϖ0 hϖO t.2, not_isIw_yRep_inv hϖ0 hϖO hϖu _, not_isIw_smul_yRep hϖ0 hϖO hϖu _⟩
      · rw [hclause_ii, hgRep]; exact fun Y => isInt_conj_yRep_Dm_iff hϖ0 t.2 Y
      · rw [hclause_iii, hgRep]; exact not_forall_isInt_conj_yRep_iff hϖ0 hϖO hϖu _
    · rintro c ⟨g, hi, hii, hiii, rfl⟩
      rw [hclause_i] at hi
      rw [hclause_ii] at hii
      rw [hclause_iii] at hiii
      obtain ⟨k, hk, hk11, hyk⟩ := normalForm hϖ0 hϖO hmax _ (isUnit_det_psiP v φ hP g) hi.1 hi.2.1 hii hiii
      have ht : k 0 1 * (k 1 1)⁻¹ ∈ Ov := mul_mem (hk.1 0 1) hk11.inv.mem
      refine ⟨⟨_, ht⟩, ?_⟩
      show (gRep ⟨_, ht⟩ : (Dv)ˣ ⧸ H) = (g : (Dv)ˣ ⧸ H)
      rw [QuotientGroup.eq, hmemH, Units.val_mul, psiP_mul v φ hP, psiP_units_inv v φ hP, hgRep, hyk]
      exact isB_yRep_inv_mul hϖ0 hϖO hk hk11

  let I : Ideal (Ov) := Ideal.span {((q : ℕ) : Ov)}
  have hmemI : ∀ r : Ov, r ∈ I ↔ ((q : ℕ) : Kv)⁻¹ * (r : Kv) ∈ Ov := by
    intro r
    rw [Ideal.mem_span_singleton']
    constructor
    · rintro ⟨c, rfl⟩
      have : ((q : ℕ) : Kv)⁻¹ * ((c * ((q : ℕ) : Ov) : Ov) : Kv) = c := by
        push_cast; rw [mul_comm (c : Kv), ← mul_assoc, inv_mul_cancel₀ hϖ0, one_mul]
      rw [this]; exact c.2
    · intro hr
      refine ⟨⟨_, hr⟩, Subtype.ext ?_⟩
      push_cast; rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ hϖ0, one_mul]
  have hrel : ∀ s t : Ov, I.quotientRel s t ↔ Setoid.ker F s t := by
    intro s t
    rw [Submodule.quotientRel_def, Setoid.ker_def, hker, hmemI]
    push_cast
    rw [show ((q : ℕ) : Kv)⁻¹ * ((s : Kv) - (t : Kv)) = -(((q : ℕ) : Kv)⁻¹ * ((t : Kv) - (s : Kv))) by ring]
    exact ⟨fun h => by simpa using neg_mem h, fun h => neg_mem h⟩
  have e : (Ov) ⧸ I ≃ Set.range F := (Quotient.congrRight hrel).trans (Setoid.quotientKerEquivRange F)
  have hcard : Nat.card ((Ov) ⧸ I) = q := by
    rw [IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_rat_quotient_span_natCast_eq_prime_pow_factorization
      v q hq hqv q hq.ne_zero, Nat.Prime.factorization_self hq, pow_one]
  rw [← hrange, ← Nat.card_coe_set_eq, ← Nat.card_congr e, hcard]

end main

end F3LOC

theorem solution
    {a b : ℚ} {q' : ℕ} (hq' : q'.Prime) (hB : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (q : ℕ) (hq : q.Prime) (hqq' : q ≠ q') (hqN : ¬ q ∣ N)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hnH : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hqv : ((q : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) :
    Set.ncard {c : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸
        MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ
          ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v :
              AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) |
      ∃ g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ,
        ((g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
          (q : ℚ) • ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∈
            Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
          ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉
            Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ∧
          (q : ℚ)⁻¹ • (g : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) ∉ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v) ∧
        (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
          ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) * x * g ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔
            x ∈ Submodule.localBox R v) ∧
        (¬ ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
          ((g⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ) : _) * x * g ∈ Submodule.localBox R v ↔
            x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v) ∧
        (g : (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ ⧸
          MulAction.stabilizer (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)ˣ
            ((Submodule.localBox (CerednikDrinfeld.meetOrder R n) v :
                AddSubgroup (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ)) : Set (ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ))) = c} = q :=
  F3LOC.main v hq' hB hR q hq hqq' hqN n hnH hqv

end S_CerednikDrinfeld_ncard_setOf_quotientMk_stabilizer_localBox_meetOrder_eq_of_mem_primeHeckeSet
end P2MW
export P2MW.S_CerednikDrinfeld_ncard_setOf_quotientMk_stabilizer_localBox_meetOrder_eq_of_mem_primeHeckeSet (solution)
