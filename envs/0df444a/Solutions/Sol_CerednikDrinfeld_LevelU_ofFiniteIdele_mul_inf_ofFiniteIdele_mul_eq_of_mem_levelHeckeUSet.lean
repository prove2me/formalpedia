-- Prove2me | solution 1 for CerednikDrinfeld.LevelU.ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/03963e32-dbe6-57b0-a7be-c370f3053b7f

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_FiniteAdeleBox
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_IsMaximalOrder_localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
import Theorems.Thm_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
import Theorems.Thm_Submodule_exists_mem_add_one_tmul_pow_mul_of_mem_localBox
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_exists_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Theorems.Thm_Submodule_finiteAdeleBox_ofFiniteIdele
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

section Pen20Lift
open scoped Quaternion TensorProduct NumberField Pointwise
p2m_open "QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.CerednikDrinfeld IsDedekindDomain"

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "meetOrder levelHeckeUSet"
namespace LevelU
namespace Pen20
p2m_open "CerednikDrinfeld"

variable {a b : ℚ}

def boxGen (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) :=
  {x | ∃ z ∈ Λ, ∃ c : FiniteAdeleRing (𝓞 ℚ) ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), c v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] c}

theorem mem_box_iff_span {Λ : Submodule ℤ ℍ[ℚ, a, b]} {x : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ} :
    x ∈ Submodule.finiteAdeleBox Λ ↔ x ∈ Submodule.span ℤ (boxGen Λ) := by
  have e : Submodule.finiteAdeleBox Λ = (Submodule.span ℤ (boxGen Λ)).toAddSubgroup := by
    rw [Submodule.span_int_eq_addSubgroupClosure]; rfl
  rw [e]; rfl

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : QuaternionAlgebra.IsOrder Λ)
    {x y : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ}
    (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff_span] at hx hy ⊢
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

theorem tmul_one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} {z : ℍ[ℚ, a, b]} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ Submodule.finiteAdeleBox Λ := by
  unfold Submodule.finiteAdeleBox
  refine AddSubgroup.subset_closure ⟨z, hz, 1, fun v => ?_, rfl⟩
  have e : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
  rw [e]; exact one_mem _

theorem box_mono {O Λ : Submodule ℤ ℍ[ℚ, a, b]} (hOΛ : O ≤ Λ) :
    Submodule.finiteAdeleBox O ≤ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, hOΛ hz, c, hc, hx⟩

theorem le_conjByFiniteIdele_of_forall {O Λ : Submodule ℤ ℍ[ℚ, a, b]}
    (h : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (H : ∀ z ∈ O, ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) *
        z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
          Submodule.finiteAdeleBox Λ) :
    O ≤ Submodule.conjByFiniteIdele Λ h := by
  intro z hz
  rw [Submodule.mem_conjByFiniteIdele_iff, AddSubgroup.mem_map]
  refine ⟨_, H z hz, ?_⟩
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
  rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem levelHeckeUSet_subset_primeHeckeSet_self (Λ O : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) :
    CerednikDrinfeld.levelHeckeUSet Λ O ℓ ⊆ QuaternionAlgebra.primeHeckeSet O ℓ :=
  fun _ hh => hh.1

theorem levelHeckeUSet_subset_primeHeckeSet (Λ O : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : QuaternionAlgebra.IsOrder Λ)
    (hOΛ : O ≤ Λ) (ℓ : ℕ) :
    CerednikDrinfeld.levelHeckeUSet Λ O ℓ ⊆ QuaternionAlgebra.primeHeckeSet Λ ℓ := by
  intro h hh
  obtain ⟨⟨hhO, hℓhiO, hhiO, hℓihO⟩, -, hnle⟩ := hh
  have hhΛ := box_mono hOΛ hhO
  have hℓhiΛ := box_mono hOΛ hℓhiO
  refine ⟨hhΛ, hℓhiΛ, fun hhiΛ => hnle ?_, fun hℓihΛ => hnle ?_⟩
  ·
    exact le_conjByFiniteIdele_of_forall h fun z hz =>
      box_mul_mem hΛ (box_mul_mem hΛ hhiΛ (tmul_one_mem_box (hOΛ hz))) hhΛ
  ·
    refine le_conjByFiniteIdele_of_forall h fun z hz => ?_
    have hℓ0 : (ℓ : ℚ) ≠ 0 := by
      rintro hℓ0
      rw [hℓ0, inv_zero, zero_smul] at hℓihO
      exact hℓihO (zero_mem _)
    have e : ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) *
          z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) * (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) =
        ((ℓ : ℚ) • ((h⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) *
          z ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) *
          ((ℓ : ℚ)⁻¹ • (h : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
      rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hℓ0, one_smul]
    rw [e]
    exact box_mul_mem hΛ (box_mul_mem hΛ hℓhiΛ (tmul_one_mem_box (hOΛ hz))) hℓihΛ

end CerednikDrinfeld.LevelU.Pen20

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "meetOrder levelHeckeUSet" namespace LevelU end CerednikDrinfeld.LevelU
p2m_open_scoped "CerednikDrinfeld" in

theorem CerednikDrinfeld.LevelU.levelHeckeUSet_meetOrder_subset
    {a b : ℚ} {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : QuaternionAlgebra.IsOrder Λ₁)
    (m : (ℍ[ℚ, a, b] ⊗[ℚ] IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (ℓ : ℕ) :
    CerednikDrinfeld.levelHeckeUSet Λ₁ (CerednikDrinfeld.meetOrder Λ₁ m) ℓ ⊆ QuaternionAlgebra.primeHeckeSet Λ₁ ℓ :=
  CerednikDrinfeld.LevelU.Pen20.levelHeckeUSet_subset_primeHeckeSet Λ₁ _ hΛ₁
    (by unfold CerednikDrinfeld.meetOrder; exact inf_le_left) ℓ

end Pen20Lift

section LevelULocalBlock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LevelULocal

section Places

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

def pr : ℕ := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v : ℕ)

theorem pr_prime : (pr v).Prime := (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v).2

scoped instance factPr : Fact (pr v).Prime := ⟨pr_prime v⟩

theorem pr_ne_zero : pr v ≠ 0 := (pr_prime v).ne_zero
theorem natGenerator_eq_pr : Rat.HeightOneSpectrum.natGenerator v = pr v := rfl
theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natCast_mem_asIdeal_iff_pr_dvd (n : ℕ) : (n : 𝓞 ℚ) ∈ v.asIdeal ↔ pr v ∣ n := by
  rw [natCast_mem_asIdeal_iff, natGenerator_eq_pr]
theorem pr_mem_asIdeal : (pr v : 𝓞 ℚ) ∈ v.asIdeal := by
  rw [natCast_mem_asIdeal_iff, natGenerator_eq_pr]
theorem pr_notMem_asIdeal_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) :
    (pr v : 𝓞 ℚ) ∉ w.asIdeal := by
  rw [natCast_mem_asIdeal_iff]
  intro h
  have : Rat.HeightOneSpectrum.natGenerator w = pr v :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) (pr_prime v)).mp h
  apply hw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  exact Subtype.ext this

theorem asIdeal_eq_span_pr : v.asIdeal = Ideal.span {(pr v : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v
  rw [natGenerator_eq_pr] at h
  have h2 : v.asIdeal = Ideal.map ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ)
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) v.asIdeal) := by
    rw [Ideal.map_map]
    have : ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ).comp
        (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) = RingHom.id _ := by
      ext x; simp
    rw [this, Ideal.map_id]
  rw [h2]
  erw [← h]
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  simp

theorem valuation_pr : v.valuation ℚ (pr v : ℚ) = WithZero.exp (-1) := by
  rw [show (pr v : ℚ) = algebraMap (𝓞 ℚ) ℚ (pr v) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton v (by exact_mod_cast pr_ne_zero v)
    (asIdeal_eq_span_pr v)

theorem valued_algebraMap (r : ℚ) : Valued.v (algebraMap ℚ 𝕂 r) = v.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v r

theorem algebraMap_natCast (n : ℕ) : algebraMap ℚ 𝕂 (n : ℚ) = (n : 𝕂) := map_natCast _ n
theorem valued_pr : Valued.v ((pr v : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [← algebraMap_natCast, valued_algebraMap, valuation_pr]
theorem pr_ne_zero' : ((pr v : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_pr v
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem natCast_mem_integers (n : ℕ) : ((n : ℕ) : 𝕂) ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← algebraMap_natCast, valued_algebraMap,
    show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one v _

theorem pr_mem_integers : ((pr v : ℕ) : 𝕂) ∈ 𝓞v := natCast_mem_integers v _
theorem valued_natCast_eq_one {n : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    Valued.v (n : w.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (n : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w)).mpr hn] at h
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) n) = 1 at h
  rwa [map_natCast] at h

theorem natCast_ne_zero_of_notMem {n : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    (n : w.adicCompletion ℚ) ≠ 0 := by
  intro h
  have := valued_natCast_eq_one w hn
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem natCast_inv_mem_integers {n : ℕ} (w : HeightOneSpectrum (𝓞 ℚ)) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    (n : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one w hn, inv_one]

theorem valued_le_one_of_mem {x : 𝕂} (hx : x ∈ 𝓞v) : Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hx
theorem mem_integers_of_valued_le_one {x : 𝕂} (hx : Valued.v x ≤ 1) : x ∈ 𝓞v :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hx

theorem pr_inv_mul_mem_integers_iff {x : 𝕂} (hx : x ∈ 𝓞v) :
    ((pr v : ℕ) : 𝕂)⁻¹ * x ∈ 𝓞v ↔ Valued.v x < 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, valued_pr]
  by_cases hx0 : x = 0
  · simp [hx0]
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
      ⟨WithZero.log (Valued.v x), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx0)).symm⟩
    rw [hm, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp,
      WithZero.exp_lt_exp]
    omega

theorem valued_eq_one_of_mul_eq_one {x y : 𝕂} (hx : x ∈ 𝓞v) (hy : y ∈ 𝓞v) (h : x * y = 1) :
    Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, h, map_one]
  have hx1 := valued_le_one_of_mem v hx
  have hy1 := valued_le_one_of_mem v hy
  by_contra hne
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne
  have : Valued.v x * Valued.v y < 1 := by
    calc Valued.v x * Valued.v y ≤ Valued.v x * 1 := mul_le_mul_right hy1 _
      _ = Valued.v x := mul_one _
      _ < 1 := hlt
  rw [h1] at this
  exact lt_irrefl _ this

theorem inv_mem_integers_of_valued_eq_one {x : 𝕂} (h : Valued.v x = 1) : x⁻¹ ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]

end Places

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : 𝕂} (hc : c ∈ 𝓞v) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem tmul_one_mem_localBox {z : D} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : 𝕂) ∈ Submodule.localBox Λ v :=
  tmul_mem_localBox Λ v hz (one_mem _)

omit Λ in
theorem localBox_mono {Λ Λ' : Submodule ℤ D} (h : Λ ≤ Λ') :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

theorem one_tmul_mul_mem_localBox {x : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) {c : 𝕂}
    (hc : c ∈ 𝓞v) : ((1 : D) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_mem_localBox Λ v hz (mul_mem hc hc')
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => exact (mul_neg _ x).symm ▸ neg_mem hx

theorem mul_mem_localBox (hmul : ∀ x y : D, x ∈ Λ → y ∈ Λ → x * y ∈ Λ)
    {x y : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) (hy : y ∈ Submodule.localBox Λ v) :
    x * y ∈ Submodule.localBox Λ v := by
  induction hy using AddSubgroup.closure_induction with
  | mem y' hy' =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy'
    induction hx using AddSubgroup.closure_induction with
    | mem x' hx' =>
      obtain ⟨z', hz', c', hc', rfl⟩ := hx'
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact tmul_mem_localBox Λ v (hmul _ _ hz' hz) (mul_mem hc' hc)
    | zero => rw [zero_mul]; exact zero_mem _
    | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
    | neg x _ hx => exact (neg_mul x _).symm ▸ neg_mem hx
  | zero => rw [mul_zero]; exact zero_mem _
  | add x' y' _ _ hx' hy' => rw [mul_add]; exact add_mem hx' hy'
  | neg x' _ hx' => exact (mul_neg _ x').symm ▸ neg_mem hx'

omit Λ in
theorem ratCast_smul_eq_one_tmul_mul (r : ℚ) (x : D ⊗[ℚ] 𝕂) :
    r • x = ((1 : D) ⊗ₜ[ℚ] (algebraMap ℚ 𝕂 r)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z c =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

theorem localBox_le_of_nsmul_mem {Λ Λ' : Submodule ℤ D} {m : ℕ} (hm : (m : 𝓞 ℚ) ∉ v.asIdeal)
    (h : ∀ z ∈ Λ', (m : ℤ) • z ∈ Λ) :
    Submodule.localBox Λ' v ≤ Submodule.localBox Λ v := by
  unfold Submodule.localBox
  rw [AddSubgroup.closure_le]
  rintro _ ⟨z, hz, c, hc, rfl⟩
  have hm0 := natCast_ne_zero_of_notMem v hm
  have : z ⊗ₜ[ℚ] c = ((m : ℤ) • z) ⊗ₜ[ℚ] ((m : 𝕂)⁻¹ * c) := by
    rw [← Int.cast_smul_eq_zsmul ℚ, TensorProduct.smul_tmul, Int.cast_natCast, Algebra.smul_def,
      map_natCast, ← mul_assoc, mul_inv_cancel₀ hm0, one_mul]
  rw [this]
  exact AddSubgroup.subset_closure ⟨(m : ℤ) • z, h z hz, _, mul_mem (natCast_inv_mem_integers v hm) hc, rfl⟩

end Box

section LocalMatrix

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def intMat : Subring M₂ where
  carrier := {M | ∀ i j, M i j ∈ 𝓞v}
  mul_mem' {A B} hA hB i j := by
    rw [Matrix.mul_apply]
    exact Subring.sum_mem _ fun k _ => mul_mem (hA i k) (hB k j)
  one_mem' i j := by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  add_mem' {A B} hA hB i j := by rw [Matrix.add_apply]; exact add_mem (hA i j) (hB i j)
  zero_mem' i j := by rw [Matrix.zero_apply]; exact zero_mem _
  neg_mem' {A} hA i j := by rw [Matrix.neg_apply]; exact neg_mem (hA i j)

theorem mem_intMat_iff (M : M₂) : M ∈ intMat v ↔ ∀ i j, M i j ∈ 𝓞v := Iff.rfl
theorem smul_mem_intMat {c : 𝕂} (hc : c ∈ 𝓞v) {M : M₂} (hM : M ∈ intMat v) : c • M ∈ intMat v :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)
theorem det_mem_integers {M : M₂} (hM : M ∈ intMat v) : M.det ∈ 𝓞v := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

theorem adjugate_mem_intMat {M : M₂} (hM : M ∈ intMat v) : M.adjugate ∈ intMat v := by
  rw [Matrix.adjugate_fin_two]
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using hM 1 1
  · simpa using neg_mem (hM 0 1)
  · simpa using neg_mem (hM 1 0)
  · simpa using hM 0 0

theorem eq_smul_adjugate {M Mi : M₂} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    Mi = M.det⁻¹ • M.adjugate := by
  have hdet : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det h1
    rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
    exact zero_ne_one this
  have key : Mi * (M * M.adjugate) = M.det • Mi := by
    rw [Matrix.mul_adjugate, Matrix.mul_smul, mul_one]
  rw [← mul_assoc, h2, one_mul] at key
  rw [key, smul_smul, inv_mul_cancel₀ hdet, one_smul]

theorem det_mul_det_eq_one {M Mi : M₂} (h1 : M * Mi = 1) : M.det * Mi.det = 1 := by
  rw [← Matrix.det_mul, h1, Matrix.det_one]

theorem valued_det_eq_one {M Mi : M₂} (hM : M ∈ intMat v) (hMi : Mi ∈ intMat v) (h1 : M * Mi = 1) :
    Valued.v M.det = 1 :=
  valued_eq_one_of_mul_eq_one v (det_mem_integers v hM) (det_mem_integers v hMi) (det_mul_det_eq_one v h1)

theorem inv_mem_intMat_of_valued_det {M Mi : M₂} (hM : M ∈ intMat v) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hdet : Valued.v M.det = 1) : Mi ∈ intMat v := by
  rw [eq_smul_adjugate v h1 h2]
  exact smul_mem_intMat v (inv_mem_integers_of_valued_eq_one v hdet) (adjugate_mem_intMat v hM)

theorem inv_apply_one_zero {M Mi : M₂} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    Mi 1 0 = -(M.det⁻¹ * M 1 0) := by
  rw [eq_smul_adjugate v h1 h2, Matrix.adjugate_fin_two]
  simp

theorem inv_apply_zero_zero {M Mi : M₂} (h1 : M * Mi = 1) (h2 : Mi * M = 1) :
    Mi 0 0 = M.det⁻¹ * M 1 1 := by
  rw [eq_smul_adjugate v h1 h2, Matrix.adjugate_fin_two]
  simp

def tM : M₂ := !![1, 0; 0, ϖ]

def tMi : M₂ := !![1, 0; 0, ϖ⁻¹]

def tbM : M₂ := !![ϖ, 0; 0, 1]

def tbMi : M₂ := !![ϖ⁻¹, 0; 0, 1]

def wM : M₂ := !![0, 1; 1, 0]

theorem tM_mul_tMi : tM v * tMi v = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tM, tMi, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ (pr_ne_zero' v)]

theorem tMi_mul_tM : tMi v * tM v = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tM, tMi, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ (pr_ne_zero' v)]

theorem tbM_mul_tM : tbM v * tM v = ϖ • (1 : M₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tM, tbM, Matrix.mul_apply, Fin.sum_univ_two]
theorem tM_mul_tbM : tM v * tbM v = ϖ • (1 : M₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tM, tbM, Matrix.mul_apply, Fin.sum_univ_two]
theorem tMi_mul_tbMi : tMi v * tbMi v = ϖ⁻¹ • (1 : M₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tMi, tbMi, Matrix.mul_apply, Fin.sum_univ_two]
theorem smul_tMi : ϖ • tMi v = tbM v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tMi, tbM, mul_inv_cancel₀ (pr_ne_zero' v)]
theorem smul_tbMi : ϖ • tbMi v = tM v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tbMi, tM, mul_inv_cancel₀ (pr_ne_zero' v)]
theorem wM_mul_wM : wM v * wM v = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wM, Matrix.mul_apply, Fin.sum_univ_two]
theorem tM_mul_wM : tM v * wM v = wM v * tbM v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wM, tM, tbM, Matrix.mul_apply, Fin.sum_univ_two]
theorem wM_mul_tMi : wM v * tMi v = tbMi v * wM v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [wM, tMi, tbMi, Matrix.mul_apply, Fin.sum_univ_two]
theorem det_tM : (tM v).det = ϖ := by simp [tM, Matrix.det_fin_two_of]

theorem det_tbM : (tbM v).det = ϖ := by simp [tbM, Matrix.det_fin_two_of]

theorem tM_mem : tM v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [tM, one_mem, zero_mem, pr_mem_integers v]

theorem tbM_mem : tbM v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [tbM, one_mem, zero_mem, pr_mem_integers v]

theorem wM_mem : wM v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [wM, one_mem, zero_mem]

theorem wM_apply_one_one (k : M₂) : (k * wM v) 1 1 = k 1 0 := by
  simp [wM, Matrix.mul_apply, Fin.sum_univ_two]

theorem tMi_mul_mul_tM (Y : M₂) : tMi v * Y * tM v = !![Y 0 0, ϖ * Y 0 1; ϖ⁻¹ * Y 1 0, Y 1 1] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have hp := pr_ne_zero' v
  fin_cases i <;> fin_cases j <;> simp [tM, tMi] <;> field_simp

theorem tMi_mul_mul_tbM (Y : M₂) : tMi v * Y * tbM v = !![ϖ * Y 0 0, Y 0 1; Y 1 0, ϖ⁻¹ * Y 1 1] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have hp := pr_ne_zero' v
  fin_cases i <;> fin_cases j <;> simp [tbM, tMi] <;> field_simp

theorem tbMi_mul_mul_tM (Y : M₂) : tbMi v * Y * tM v = !![ϖ⁻¹ * Y 0 0, Y 0 1; Y 1 0, ϖ * Y 1 1] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have hp := pr_ne_zero' v
  fin_cases i <;> fin_cases j <;> simp [tM, tbMi] <;> field_simp

theorem tMi_mul_mul_tM_mem_iff {Y : M₂} (hY : Y ∈ intMat v) :
    tMi v * Y * tM v ∈ intMat v ↔ Valued.v (Y 1 0) < 1 := by
  rw [← pr_inv_mul_mem_integers_iff v (hY 1 0), tMi_mul_mul_tM, mem_intMat_iff]
  constructor
  · intro h; simpa using h 1 0
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using hY 0 0
    · simpa using mul_mem (pr_mem_integers v) (hY 0 1)
    · simpa using h
    · simpa using hY 1 1

theorem tMi_mul_mul_tbM_mem_iff {Y : M₂} (hY : Y ∈ intMat v) :
    tMi v * Y * tbM v ∈ intMat v ↔ Valued.v (Y 1 1) < 1 := by
  rw [← pr_inv_mul_mem_integers_iff v (hY 1 1), tMi_mul_mul_tbM, mem_intMat_iff]
  constructor
  · intro h; simpa using h 1 1
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using mul_mem (pr_mem_integers v) (hY 0 0)
    · simpa using hY 0 1
    · simpa using hY 1 0
    · simpa using h

theorem tbMi_mul_mul_tM_mem_iff {Y : M₂} (hY : Y ∈ intMat v) :
    tbMi v * Y * tM v ∈ intMat v ↔ Valued.v (Y 0 0) < 1 := by
  rw [← pr_inv_mul_mem_integers_iff v (hY 0 0), tbMi_mul_mul_tM, mem_intMat_iff]
  constructor
  · intro h; simpa using h 0 0
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using h
    · simpa using hY 0 1
    · simpa using hY 1 0
    · simpa using mul_mem (pr_mem_integers v) (hY 1 1)

theorem exists_exp_valued_det {Y : M₂} (hY : Y ∈ intMat v) (hdet : Y.det ≠ 0) :
    ∃ m : ℤ, m ≤ 0 ∧ Valued.v Y.det = WithZero.exp m := by
  have h0 : Valued.v Y.det ≠ 0 := (Valuation.ne_zero_iff _).2 hdet
  have hm : Valued.v Y.det = WithZero.exp (WithZero.log (Valued.v Y.det)) := (WithZero.exp_log h0).symm
  refine ⟨WithZero.log (Valued.v Y.det), ?_, hm⟩
  have := valued_le_one_of_mem v (det_mem_integers v hY)
  rw [hm, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
  exact this

theorem valued_det_bounds {Y Yi : M₂} (h1 : Y * Yi = 1) (hY : Y ∈ intMat v) (hpYi : ϖ • Yi ∈ intMat v) :
    ∃ m : ℤ, -2 ≤ m ∧ m ≤ 0 ∧ Valued.v Y.det = WithZero.exp m := by
  have hdet0 : Y.det ≠ 0 := fun h => by
    have := det_mul_det_eq_one v h1; rw [h, zero_mul] at this; exact zero_ne_one this
  obtain ⟨m, hm0, hm⟩ := exists_exp_valued_det v hY hdet0
  refine ⟨m, ?_, hm0, hm⟩

  have h2 := valued_le_one_of_mem v (det_mem_integers v hpYi)
  rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, valued_pr] at h2
  have hYi : Valued.v Yi.det = (Valued.v Y.det)⁻¹ := by
    have := det_mul_det_eq_one v h1
    have h' : Valued.v Y.det * Valued.v Yi.det = 1 := by rw [← map_mul, this, map_one]
    exact eq_inv_of_mul_eq_one_right h'
  rw [hYi, hm, ← WithZero.exp_nsmul, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero,
    WithZero.exp_le_exp] at h2
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at h2
  omega

theorem exists_eq_mul_tM_mul {Y Yi : M₂} (h1 : Y * Yi = 1) (h2 : Yi * Y = 1) (hY : Y ∈ intMat v)
    (hpYi : ϖ • Yi ∈ intMat v) (hYi : Yi ∉ intMat v) (hpY : ϖ⁻¹ • Y ∉ intMat v) :
    ∃ K1 K1i K2 K2i : M₂, K1 ∈ intMat v ∧ K1i ∈ intMat v ∧ K2 ∈ intMat v ∧ K2i ∈ intMat v ∧
      K1 * K1i = 1 ∧ K1i * K1 = 1 ∧ K2 * K2i = 1 ∧ K2i * K2 = 1 ∧ Y = K1 * tM v * K2 :=
  Matrix.exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers (pr v) (pr_prime v) v
    (pr_mem_asIdeal v) Y Yi h1 h2 hY hpYi hYi hpY

end LocalMatrix

section LocalMatrix2

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

theorem tbMi_mul_tMi : tbMi v * tMi v = ϖ⁻¹ • (1 : M₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tMi, tbMi, Matrix.mul_apply, Fin.sum_univ_two]

theorem det_tbMi : (tbMi v).det = ϖ⁻¹ := by simp [tbMi, Matrix.det_fin_two_of]

theorem det_tMi : (tMi v).det = ϖ⁻¹ := by simp [tMi, Matrix.det_fin_two_of]

theorem conj_mem_intMat {P Pi Y : M₂} (hP : P ∈ intMat v) (hPi : Pi ∈ intMat v) (hY : Y ∈ intMat v) :
    Pi * Y * P ∈ intMat v :=
  (intMat v).mul_mem ((intMat v).mul_mem hPi hY) hP

theorem conj_mem_intMat_iff {P Pi Y : M₂} (hP : P ∈ intMat v) (hPi : Pi ∈ intMat v)
    (h1 : P * Pi = 1) (h2 : Pi * P = 1) : Pi * Y * P ∈ intMat v ↔ Y ∈ intMat v := by
  refine ⟨fun h => ?_, conj_mem_intMat v hP hPi⟩
  have := conj_mem_intMat v hPi hP h
  have e : P * (Pi * Y * P) * Pi = (P * Pi) * Y * (P * Pi) := by noncomm_ring
  rwa [e, h1, one_mul, mul_one] at this

theorem valued_det_eq_sq {X Xi : M₂} {c : 𝕂} (hc : c ≠ 0) (h1 : X * Xi = 1)
    (hX : c⁻¹ • X ∈ intMat v) (hXi : c • Xi ∈ intMat v) : Valued.v X.det = Valued.v c ^ 2 := by
  have hprod : (c⁻¹ • X) * (c • Xi) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc, one_smul, h1]
  have := valued_det_eq_one v hX hXi hprod
  rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, map_inv₀] at this
  have hcv : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  calc Valued.v X.det = Valued.v c ^ 2 * ((Valued.v c)⁻¹ ^ 2 * Valued.v X.det) := by field_simp
    _ = Valued.v c ^ 2 := by rw [this, mul_one]

end LocalMatrix2

section Global

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

p2m_open "QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.CerednikDrinfeld"

theorem box_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (h : Λ ≤ Λ') :
    Submodule.finiteAdeleBox Λ ≤ Submodule.finiteAdeleBox Λ' :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (x : 𝔹) :
    x ∈ Submodule.finiteAdeleBox Λ ↔ ∀ w, ev w x ∈ Submodule.localBox Λ w :=
  Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop x

theorem mem_stab_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (𝔹)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔ ∀ w, ev w (u : 𝔹) ∈ Submodule.localBox Λ w ∧
      ev w ((u⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox Λ w := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
    Λ hΛ u]
  exact forall_congr' fun w => Iff.rfl

theorem ev_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    ev w (z ⊗ₜ[ℚ] (1 : 𝔸f)) = z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Submodule.finiteAdeleEvalAt_tmul]; rfl

theorem ev_ratCast_smul (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) (x : 𝔹) :
    ev w (r • x) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (algebraMap ℚ _ r)) * ev w x := by
  rw [map_smul, ratCast_smul_eq_one_tmul_mul]

theorem ev_units_mul_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    ev w (g : 𝔹) * ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) = 1 := by rw [← map_mul, Units.mul_inv, map_one]

theorem ev_units_inv_mul (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) * ev w (g : 𝔹) = 1 := by rw [← map_mul, Units.inv_mul, map_one]

theorem mem_iff_tmul_one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (z : ℍ[ℚ, a, b]) :
    z ∈ Λ ↔ z ⊗ₜ[ℚ] (1 : 𝔸f) ∈ Submodule.finiteAdeleBox Λ := by
  conv_lhs => rw [← Submodule.ofFiniteIdele_one Λ hΛ.fg hΛ.spanTop]
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  simp

theorem mem_conj_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (𝔹)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.conjByFiniteIdele Λ g ↔
      ((g⁻¹ : (𝔹)ˣ) : 𝔹) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) * (g : 𝔹) ∈ Submodule.finiteAdeleBox Λ := by
  rw [Submodule.mem_conjByFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyz⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      AddMonoidHom.coe_mulRight] at hyz
    rw [← hyz]
    have : ((g⁻¹ : (𝔹)ˣ) : 𝔹) * ((g : 𝔹) * y * ((g⁻¹ : (𝔹)ˣ) : 𝔹)) * (g : 𝔹) = y := by
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      AddMonoidHom.coe_mulRight]
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem mem_map_conj_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (𝔹)ˣ) (x : 𝔹) :
    x ∈ (Submodule.finiteAdeleBox Λ).map
        ((AddMonoidHom.mulRight ((g⁻¹ : (𝔹)ˣ) : 𝔹)).comp (AddMonoidHom.mulLeft (g : 𝔹))) ↔
      ((g⁻¹ : (𝔹)ˣ) : 𝔹) * x * (g : 𝔹) ∈ Submodule.finiteAdeleBox Λ := by
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyz⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      AddMonoidHom.coe_mulRight] at hyz
    rw [← hyz]
    have : ((g⁻¹ : (𝔹)ˣ) : 𝔹) * ((g : 𝔹) * y * ((g⁻¹ : (𝔹)ˣ) : 𝔹)) * (g : 𝔹) = y := by
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      AddMonoidHom.coe_mulRight]
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem conj_mem_box_iff_of_conj_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {g₁ g₂ : (𝔹)ˣ}
    (h : Submodule.conjByFiniteIdele Λ g₁ = Submodule.conjByFiniteIdele Λ g₂) (x : 𝔹) :
    ((g₁⁻¹ : (𝔹)ˣ) : 𝔹) * x * (g₁ : 𝔹) ∈ Submodule.finiteAdeleBox Λ ↔
      ((g₂⁻¹ : (𝔹)ˣ) : 𝔹) * x * (g₂ : 𝔹) ∈ Submodule.finiteAdeleBox Λ := by
  have h1 := Submodule.finiteAdeleBox_conjByFiniteIdele Λ hΛ.fg hΛ.spanTop g₁
  have h2 := Submodule.finiteAdeleBox_conjByFiniteIdele Λ hΛ.fg hΛ.spanTop g₂
  rw [← mem_map_conj_iff, ← mem_map_conj_iff, ← h1, ← h2, h]

theorem conj_conj_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (g h : (𝔹)ˣ) :
    Submodule.conjByFiniteIdele (Submodule.conjByFiniteIdele Λ g) h =
      Submodule.conjByFiniteIdele Λ (h * g) := by
  ext z
  rw [mem_conj_iff, mem_conj_iff, Submodule.finiteAdeleBox_conjByFiniteIdele Λ hΛ.fg hΛ.spanTop g,
    mem_map_conj_iff, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
  constructor <;> intro H
  · have e : ((g⁻¹ : (𝔹)ˣ) : 𝔹) * ((h⁻¹ : (𝔹)ˣ) : 𝔹) * z ⊗ₜ[ℚ] (1 : 𝔸f) * ((h : 𝔹) * (g : 𝔹)) =
        ((g⁻¹ : (𝔹)ˣ) : 𝔹) * (((h⁻¹ : (𝔹)ˣ) : 𝔹) * z ⊗ₜ[ℚ] (1 : 𝔸f) * (h : 𝔹)) * (g : 𝔹) := by
      noncomm_ring
    rw [e]; exact H
  · have e : ((g⁻¹ : (𝔹)ˣ) : 𝔹) * (((h⁻¹ : (𝔹)ˣ) : 𝔹) * z ⊗ₜ[ℚ] (1 : 𝔸f) * (h : 𝔹)) * (g : 𝔹) =
        ((g⁻¹ : (𝔹)ˣ) : 𝔹) * ((h⁻¹ : (𝔹)ˣ) : 𝔹) * z ⊗ₜ[ℚ] (1 : 𝔸f) * ((h : 𝔹) * (g : 𝔹)) := by
      noncomm_ring
    rw [e]; exact H

theorem conj_one_eq {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) : Submodule.conjByFiniteIdele Λ 1 = Λ := by
  ext z
  rw [mem_conj_iff, inv_one, Units.val_one, one_mul, mul_one, ← mem_iff_tmul_one_mem_box hΛ]

theorem exists_adele_at {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    (Y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) :
    ∃ x : 𝔹, ev v x = Y ∧ ∀ w, w ≠ v → ev w x = 0 := by
  classical
  let X : (w : HeightOneSpectrum (𝓞 ℚ)) → ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ :=
    fun w => if hw : w = v then cast (by rw [hw]) Y else 0
  have hXv : X v = Y := by simp [X]
  have hXw : ∀ w, w ≠ v → X w = 0 := fun w hw => by simp [X, hw]
  have hev : ∀ᶠ w in Filter.cofinite, X w ∈ Submodule.localBox Λ w := by
    refine Filter.eventually_cofinite.2 ((Set.finite_singleton v).subset fun w hw => ?_)
    by_contra hne
    exact hw (by rw [hXw w hne]; exact zero_mem _)
  obtain ⟨x, hx⟩ := Submodule.exists_forall_finiteAdeleEvalAt_eq Λ hΛ.fg hΛ.spanTop X hev
  exact ⟨x, by rw [hx, hXv], fun w hw => by rw [hx, hXw w hw]⟩

theorem exists_unit_patch {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    (y yi : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ) (hy : y * yi = 1) (hy' : yi * y = 1) (g : (𝔹)ˣ)
    (hg : ∀ w, w ≠ v → ev w (g : 𝔹) ∈ Submodule.localBox Λ w ∧
      ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox Λ w) :
    ∃ h : (𝔹)ˣ, ev v (h : 𝔹) = y ∧ ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹) = yi ∧
      ∀ w, w ≠ v → ev w (h : 𝔹) = ev w (g : 𝔹) ∧ ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) = ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) :=
  Submodule.exists_units_finiteAdeleEvalAt_eq_of_forall_ne Λ hΛ.fg hΛ.spanTop v y yi hy hy' g hg

theorem units_conj_mem_localBox_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ)
    (w : HeightOneSpectrum (𝓞 ℚ)) {u ui y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ}
    (hu : u ∈ Submodule.localBox Λ w) (hui : ui ∈ Submodule.localBox Λ w) (h1 : u * ui = 1) (h2 : ui * u = 1) :
    ui * y * u ∈ Submodule.localBox Λ w ↔ y ∈ Submodule.localBox Λ w := by
  have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ → y ∈ Λ → x * y ∈ Λ := fun x y hx hy => hΛ.mul_mem hx hy
  refine ⟨fun h => ?_, fun h => mul_mem_localBox Λ w hmul (mul_mem_localBox Λ w hmul hui h) hu⟩
  have := mul_mem_localBox Λ w hmul (mul_mem_localBox Λ w hmul hu h) hui
  have e : u * (ui * y * u) * ui = (u * ui) * y * (u * ui) := by noncomm_ring
  rwa [e, h1, one_mul, mul_one] at this

theorem exists_approx {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (v : HeightOneSpectrum (𝓞 ℚ))
    {Y : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ} (hY : Y ∈ Submodule.localBox Λ v) :
    ∃ z ∈ Λ, ∃ E ∈ Submodule.localBox Λ v,
      Y = z ⊗ₜ[ℚ] (1 : v.adicCompletion ℚ) +
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((pr v : ℕ) : v.adicCompletion ℚ)) * E := by
  obtain ⟨z, hz, E, hE, h⟩ := Submodule.exists_mem_add_one_tmul_pow_mul_of_mem_localBox Λ hΛ.fg
    hΛ.spanTop (pr v) (pr_prime v) v (pr_mem_asIdeal v) 1 hY
  exact ⟨z, hz, E, hE, by rw [h, pow_one]⟩

end Global

section Eichler

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def dM (e : ℕ) : M₂ := !![1, 0; 0, ϖ ^ e]

def dMi (e : ℕ) : M₂ := !![1, 0; 0, (ϖ ^ e)⁻¹]

def E00 : M₂ := !![1, 0; 0, 0]

def E01 : M₂ := !![0, 1; 0, 0]

theorem prpow_ne_zero (e : ℕ) : (ϖ ^ e : 𝕂) ≠ 0 := pow_ne_zero _ (pr_ne_zero' v)
theorem prpow_mem_integers (e : ℕ) : (ϖ ^ e : 𝕂) ∈ 𝓞v := pow_mem (pr_mem_integers v) e

theorem dM_mul_dMi (e : ℕ) : dM v e * dMi v e = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dM, dMi, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ (prpow_ne_zero v e)]
theorem dMi_mul_dM (e : ℕ) : dMi v e * dM v e = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [dM, dMi, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ (prpow_ne_zero v e)]
theorem dM_mem (e : ℕ) : dM v e ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [dM, one_mem, zero_mem, prpow_mem_integers v e]
theorem E00_mem : E00 v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E00, one_mem, zero_mem]
theorem E01_mem : E01 v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E01, one_mem, zero_mem]

theorem mul_E00_apply (Y : M₂) :
    (Y * E00 v) 0 0 = Y 0 0 ∧ (Y * E00 v) 0 1 = 0 ∧ (Y * E00 v) 1 0 = Y 1 0 ∧ (Y * E00 v) 1 1 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [E00, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_E00_mem_iff (Y : M₂) : Y * E00 v ∈ intMat v ↔ Y 0 0 ∈ 𝓞v ∧ Y 1 0 ∈ 𝓞v := by
  obtain ⟨h00, h01, h10, h11⟩ := mul_E00_apply v Y
  rw [mem_intMat_iff]
  constructor
  · intro h; exact ⟨h00 ▸ h 0 0, h10 ▸ h 1 0⟩
  · rintro ⟨a0, a1⟩ i j
    fin_cases i <;> fin_cases j
    · simpa [h00] using a0
    · simp [h01, zero_mem]
    · simpa [h10] using a1
    · simp [h11, zero_mem]

theorem E00_mul_mul_eq (X : M₂) : E00 v * X * (1 - E00 v) = (X 0 1) • E01 v := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E00, E01]

theorem dMi_mul_mul_dM (e : ℕ) (Y : M₂) :
    dMi v e * Y * dM v e = !![Y 0 0, ϖ ^ e * Y 0 1; (ϖ ^ e)⁻¹ * Y 1 0, Y 1 1] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have hp := prpow_ne_zero v e
  fin_cases i <;> fin_cases j <;> simp [dM, dMi] <;> field_simp

theorem dMi_mul' (e : ℕ) (Y : M₂) :
    dMi v e * Y = !![Y 0 0, Y 0 1; (ϖ ^ e)⁻¹ * Y 1 0, (ϖ ^ e)⁻¹ * Y 1 1] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [dMi]

theorem dMi_mul_mul_dM_mem_iff (e : ℕ) {Y : M₂} (hY : Y ∈ intMat v) :
    dMi v e * Y * dM v e ∈ intMat v ↔ (ϖ ^ e)⁻¹ * Y 1 0 ∈ 𝓞v := by
  rw [dMi_mul_mul_dM, mem_intMat_iff]
  constructor
  · intro h; simpa using h 1 0
  · intro h i j
    fin_cases i <;> fin_cases j
    · simpa using hY 0 0
    · simpa using mul_mem (prpow_mem_integers v e) (hY 0 1)
    · simpa using h
    · simpa using hY 1 1

theorem dMi_mul_mem_iff (e : ℕ) (Y : M₂) :
    dMi v e * Y ∈ intMat v ↔
      (Y 0 0 ∈ 𝓞v ∧ Y 0 1 ∈ 𝓞v) ∧ ((ϖ ^ e)⁻¹ * Y 1 0 ∈ 𝓞v ∧ (ϖ ^ e)⁻¹ * Y 1 1 ∈ 𝓞v) := by
  rw [dMi_mul', mem_intMat_iff]
  constructor
  · intro h; exact ⟨⟨by simpa using h 0 0, by simpa using h 0 1⟩, ⟨by simpa using h 1 0, by simpa using h 1 1⟩⟩
  · rintro ⟨⟨h00, h01⟩, ⟨h10, h11⟩⟩ i j
    fin_cases i <;> fin_cases j
    · simpa using h00
    · simpa using h01
    · simpa using h10
    · simpa using h11

theorem conj_mem_intMat_of_inv_mul_dM_mem (e : ℕ) {η ηi X : M₂} (h2 : ηi * η = 1)
    (hη : η ∈ intMat v) (hηid : ηi * dM v e ∈ intMat v)
    (hX : X ∈ intMat v) (hXd : dMi v e * X * dM v e ∈ intMat v) :
    ηi * X * η ∈ intMat v := by
  have key : ∀ Z : M₂, dMi v e * Z ∈ intMat v → ηi * Z * η ∈ intMat v := by
    intro Z hZ
    have eq : ηi * Z * η = (ηi * dM v e) * (dMi v e * Z) * η := by
      calc ηi * Z * η = ηi * (dM v e * dMi v e) * Z * η := by rw [dM_mul_dMi, mul_one]
        _ = (ηi * dM v e) * (dMi v e * Z) * η := by noncomm_ring
    rw [eq]; exact (intMat v).mul_mem ((intMat v).mul_mem hηid hZ) hη
  have h10 : (ϖ ^ e)⁻¹ * X 1 0 ∈ 𝓞v := (dMi_mul_mul_dM_mem_iff v e hX).1 hXd
  obtain ⟨s00, s01, s10, s11⟩ := mul_E00_apply v X

  have hdec : X = X * E00 v + (X 0 1) • E01 v + ((X 1 1) • (1 : M₂) - (X 1 1) • E00 v) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [E00, E01, Matrix.mul_apply, Fin.sum_univ_two]
  have h1 : ηi * (X * E00 v) * η ∈ intMat v := by
    refine key _ ((dMi_mul_mem_iff v e _).2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩)
    · rw [s00]; exact hX 0 0
    · rw [s01]; exact zero_mem _
    · rw [s10]; exact h10
    · rw [s11, mul_zero]; exact zero_mem _
  have h2' : ηi * ((X 0 1) • E01 v) * η ∈ intMat v := by
    refine key _ ((dMi_mul_mem_iff v e _).2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩) <;>
      simp [E01, Matrix.smul_apply, hX 0 1, zero_mem]
  have h3 : ηi * ((X 1 1) • (1 : M₂) - (X 1 1) • E00 v) * η ∈ intMat v := by
    have eq : ηi * ((X 1 1) • (1 : M₂) - (X 1 1) • E00 v) * η =
        (X 1 1) • (ηi * η) - (X 1 1) • (ηi * E00 v * η) := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    rw [eq, h2]
    refine sub_mem (smul_mem_intMat v (hX 1 1) (one_mem _)) (smul_mem_intMat v (hX 1 1) (key _ ?_))
    refine (dMi_mul_mem_iff v e _).2 ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp [E00, one_mem, zero_mem]
  rw [hdec, Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul]
  exact add_mem (add_mem h1 h2') h3

theorem valued_mul_lt_one_of_lt {x y : 𝕂} (hx : Valued.v x < 1) (hy : Valued.v y ≤ 1) : Valued.v (x * y) < 1 := by
  rw [map_mul]
  calc Valued.v x * Valued.v y ≤ Valued.v x * 1 := mul_le_mul_right hy _
    _ = Valued.v x := mul_one _
    _ < 1 := hx

theorem valued_eq_one_or {K1 K1i : M₂} (hK1 : K1 ∈ intMat v) (hK1i : K1i ∈ intMat v) (hKK1 : K1 * K1i = 1) :
    Valued.v (K1 0 0) = 1 ∨ Valued.v (K1 1 0) = 1 := by
  by_contra hne
  push Not at hne
  have h00 : Valued.v (K1 0 0) < 1 := lt_of_le_of_ne (valued_le_one_of_mem v (hK1 0 0)) hne.1
  have h10 : Valued.v (K1 1 0) < 1 := lt_of_le_of_ne (valued_le_one_of_mem v (hK1 1 0)) hne.2
  have hdet := valued_det_eq_one v hK1 hK1i hKK1
  rw [Matrix.det_fin_two] at hdet
  have hlt : Valued.v (K1 0 0 * K1 1 1 - K1 0 1 * K1 1 0) < 1 := by
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · exact valued_mul_lt_one_of_lt v h00 (valued_le_one_of_mem v (hK1 1 1))
    · rw [mul_comm]; exact valued_mul_lt_one_of_lt v h10 (valued_le_one_of_mem v (hK1 0 1))
  rw [hdet] at hlt
  exact lt_irrefl _ hlt

theorem inv_mul_E00_mem_of_conj_mem {η ηi K1 K1i K2 K2i : M₂}
    (hK1 : K1 ∈ intMat v) (hK1i : K1i ∈ intMat v) (hK2i : K2i ∈ intMat v)
    (hKK1 : K1 * K1i = 1) (hKK2 : K2 * K2i = 1) (hη : η = K1 * tM v * K2)
    (hc00 : ηi * E00 v * η ∈ intMat v) (hc01 : ηi * E01 v * η ∈ intMat v) :
    ηi * E00 v ∈ intMat v := by
  have m00 : E00 v * (K1 * tM v * K2) * K2i * E00 v = (K1 0 0) • E00 v := by
    have : E00 v * (K1 * tM v * K2) * K2i * E00 v = E00 v * K1 * tM v * (K2 * K2i) * E00 v := by noncomm_ring
    rw [this, hKK2, mul_one]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [E00, tM]
  have m01 : E01 v * (K1 * tM v * K2) * K2i * E00 v = (K1 1 0) • E00 v := by
    have : E01 v * (K1 * tM v * K2) * K2i * E00 v = E01 v * K1 * tM v * (K2 * K2i) * E00 v := by noncomm_ring
    rw [this, hKK2, mul_one]
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> simp [E00, E01, tM]
  have hα : (K1 0 0) • (ηi * E00 v) ∈ intMat v := by
    have eq : (K1 0 0) • (ηi * E00 v) = (ηi * E00 v * η) * K2i * E00 v := by
      rw [hη, ← Matrix.mul_smul, ← m00]; noncomm_ring
    rw [eq]; exact (intMat v).mul_mem ((intMat v).mul_mem hc00 hK2i) (E00_mem v)
  have hγ : (K1 1 0) • (ηi * E00 v) ∈ intMat v := by
    have eq : (K1 1 0) • (ηi * E00 v) = (ηi * E01 v * η) * K2i * E00 v := by
      rw [hη, ← Matrix.mul_smul, ← m01]; noncomm_ring
    rw [eq]; exact (intMat v).mul_mem ((intMat v).mul_mem hc01 hK2i) (E00_mem v)
  rcases valued_eq_one_or v hK1 hK1i hKK1 with hu | hu
  · have hne : K1 0 0 ≠ 0 := fun h0 => by rw [h0, map_zero] at hu; exact zero_ne_one hu
    have : ηi * E00 v = (K1 0 0)⁻¹ • ((K1 0 0) • (ηi * E00 v)) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]; exact smul_mem_intMat v (inv_mem_integers_of_valued_eq_one v hu) hα
  · have hne : K1 1 0 ≠ 0 := fun h0 => by rw [h0, map_zero] at hu; exact zero_ne_one hu
    have : ηi * E00 v = (K1 1 0)⁻¹ • ((K1 1 0) • (ηi * E00 v)) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]; exact smul_mem_intMat v (inv_mem_integers_of_valued_eq_one v hu) hγ

theorem inv_mul_dM_mem_of_inv_mul_E00_mem {e : ℕ} (he : 1 ≤ e) {ηi : M₂}
    (hpηi : ϖ • ηi ∈ intMat v) (h00 : ηi * E00 v ∈ intMat v) : ηi * dM v e ∈ intMat v := by
  have hd : dM v e = E00 v + (ϖ ^ (e - 1)) • (ϖ • ((1 : M₂) - E00 v)) := by
    rw [smul_smul, ← pow_succ, Nat.sub_add_cancel he]
    ext i j; fin_cases i <;> fin_cases j <;> simp [dM, E00]
  rw [hd, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, ← Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_one]
  exact add_mem h00 (smul_mem_intMat v (prpow_mem_integers v _) (sub_mem hpηi ((intMat v).mul_mem hpηi (E00_mem v))))

theorem valued_apply_one_one_eq_one {e : ℕ} (he : 1 ≤ e) {η ηi : M₂} (h1 : η * ηi = 1) (h2 : ηi * η = 1)
    (hη : η ∈ intMat v) (hdet : Valued.v η.det = Valued.v ϖ)
    (h10 : (ϖ ^ e)⁻¹ * η 1 0 ∈ 𝓞v) (h00 : ηi * E00 v ∉ intMat v) :
    Valued.v (η 1 1) = 1 := by
  by_contra hne
  have hlt : Valued.v (η 1 1) < 1 := lt_of_le_of_ne (valued_le_one_of_mem v (hη 1 1)) hne
  have hp0 := pr_ne_zero' v
  have hdet0 : η.det ≠ 0 := fun h => by
    have := det_mul_det_eq_one v h1; rw [h, zero_mul] at this; exact zero_ne_one this
  have hu : Valued.v (η.det⁻¹ * ϖ) = 1 := by
    rw [map_mul, map_inv₀, hdet, inv_mul_cancel₀]
    rw [valued_pr]; exact WithZero.coe_ne_zero
  have hdp : η.det⁻¹ * ϖ ∈ 𝓞v := mem_integers_of_valued_le_one v hu.le
  apply h00
  rw [mul_E00_mem_iff]
  constructor
  ·
    have e1 : ηi 0 0 = (η.det⁻¹ * ϖ) * (ϖ⁻¹ * η 1 1) := by
      rw [inv_apply_zero_zero v h1 h2]; field_simp
    rw [e1]; exact mul_mem hdp ((pr_inv_mul_mem_integers_iff v (hη 1 1)).2 hlt)
  ·
    have e1 : ηi 1 0 = -((η.det⁻¹ * ϖ) * (ϖ ^ (e - 1) * ((ϖ ^ e)⁻¹ * η 1 0))) := by
      rw [inv_apply_one_zero v h1 h2,
        show (ϖ ^ e : 𝕂) = ϖ ^ (e - 1) * ϖ by rw [← pow_succ, Nat.sub_add_cancel he]]
      have hpe : (ϖ ^ (e - 1) : 𝕂) ≠ 0 := pow_ne_zero _ hp0
      field_simp
    rw [e1]; exact neg_mem (mul_mem hdp (mul_mem (prpow_mem_integers v _) h10))

theorem dMi_mul_inv_mul_mem {e : ℕ} {η ηi Y : M₂} (h1 : η * ηi = 1)
    (h10 : (ϖ ^ e)⁻¹ * η 1 0 ∈ 𝓞v) (h11 : Valued.v (η 1 1) = 1)
    (hA : ηi * Y ∈ intMat v) (hdY : dMi v e * Y ∈ intMat v) :
    dMi v e * (ηi * Y) ∈ intMat v := by
  set A := ηi * Y with hAdef
  have hYA : Y = η * A := by rw [hAdef, ← mul_assoc, h1, one_mul]
  have hne : η 1 1 ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
  have hinv : (η 1 1)⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v h11
  rw [dMi_mul_mem_iff] at hdY ⊢
  obtain ⟨-, hr10, hr11⟩ := hdY
  have hYj : ∀ j, Y 1 j = η 1 0 * A 0 j + η 1 1 * A 1 j := by
    intro j; rw [hYA, Matrix.mul_apply, Fin.sum_univ_two]
  have key : ∀ j, (ϖ ^ e)⁻¹ * Y 1 j ∈ 𝓞v → (ϖ ^ e)⁻¹ * A 1 j ∈ 𝓞v := by
    intro j hj
    have eq : (ϖ ^ e)⁻¹ * A 1 j = (η 1 1)⁻¹ * ((ϖ ^ e)⁻¹ * Y 1 j - ((ϖ ^ e)⁻¹ * η 1 0) * A 0 j) := by
      rw [hYj]; field_simp; ring
    rw [eq]; exact mul_mem hinv (sub_mem hj (mul_mem h10 (hA 0 j)))
  exact ⟨⟨hA 0 0, hA 0 1⟩, ⟨key 0 hr10, key 1 hr11⟩⟩

end Eichler

section Global2

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

p2m_open "QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.CerednikDrinfeld"

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x y : 𝔹}
    (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff hΛ] at hx hy ⊢
  intro w
  rw [map_mul]
  exact mul_mem_localBox Λ w (fun x y hx hy => hΛ.mul_mem hx hy) (hx w) (hy w)

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) : (1 : 𝔹) ∈ Submodule.finiteAdeleBox Λ := by
  rw [Algebra.TensorProduct.one_def, ← mem_iff_tmul_one_mem_box hΛ]; exact hΛ.one_mem

theorem conj_mono {Λ Λ' : Submodule ℤ ℍ[ℚ, a, b]} (hle : Λ ≤ Λ') (g : (𝔹)ˣ) :
    Submodule.conjByFiniteIdele Λ g ≤ Submodule.conjByFiniteIdele Λ' g := by
  intro z hz
  rw [mem_conj_iff] at hz ⊢
  exact box_mono hle hz

theorem mem_ofFiniteIdele_iff_inv_mul_mem (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (𝔹)ˣ) (z : ℍ[ℚ, a, b]) :
    z ∈ Submodule.ofFiniteIdele Λ g ↔ ((g⁻¹ : (𝔹)ˣ) : 𝔹) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) ∈ Submodule.finiteAdeleBox Λ := by
  rw [Submodule.mem_ofFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨w, hw, hwz⟩
    rw [AddMonoidHom.coe_mulLeft] at hwz
    rw [← hwz, ← mul_assoc, Units.inv_mul, one_mul]
    exact hw
  · intro hz
    refine ⟨_, hz, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.mul_inv, one_mul]

theorem ofFiniteIdele_mul_le_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (x g g' : (𝔹)ˣ) :
    Submodule.ofFiniteIdele Λ (x * g) ≤ Submodule.ofFiniteIdele Λ (x * g') ↔
      ((g'⁻¹ * g : (𝔹)ˣ) : 𝔹) ∈ Submodule.finiteAdeleBox Λ := by
  constructor
  · intro hle
    have hb : Submodule.finiteAdeleBox (Submodule.ofFiniteIdele Λ (x * g)) ≤
        Submodule.finiteAdeleBox (Submodule.ofFiniteIdele Λ (x * g')) := box_mono hle
    rw [Submodule.finiteAdeleBox_ofFiniteIdele Λ hΛ.fg hΛ.spanTop (x * g),
      Submodule.finiteAdeleBox_ofFiniteIdele Λ hΛ.fg hΛ.spanTop (x * g')] at hb
    have h1 : ((x * g : (𝔹)ˣ) : 𝔹) ∈ (Submodule.finiteAdeleBox Λ).map (AddMonoidHom.mulLeft ((x * g : (𝔹)ˣ) : 𝔹)) :=
      ⟨1, one_mem_box hΛ, by rw [AddMonoidHom.coe_mulLeft, mul_one]⟩
    obtain ⟨w, hw, hwg⟩ := hb h1
    rw [AddMonoidHom.coe_mulLeft] at hwg
    have : ((g'⁻¹ * g : (𝔹)ˣ) : 𝔹) = w := by
      rw [show g'⁻¹ * g = (x * g')⁻¹ * (x * g) by group, Units.val_mul, ← hwg, ← mul_assoc, Units.inv_mul, one_mul]
    rw [this]; exact hw
  · intro hb z hz
    rw [mem_ofFiniteIdele_iff_inv_mul_mem] at hz ⊢
    have : (((x * g')⁻¹ : (𝔹)ˣ) : 𝔹) * (z ⊗ₜ[ℚ] (1 : 𝔸f)) =
        ((g'⁻¹ * g : (𝔹)ˣ) : 𝔹) * ((((x * g)⁻¹ : (𝔹)ˣ) : 𝔹) * (z ⊗ₜ[ℚ] (1 : 𝔸f))) := by
      rw [← mul_assoc, ← Units.val_mul]
      congr 2; group
    rw [this]; exact box_mul_mem hΛ hb hz

theorem conj_mem_box_of_mem_box_meetOrder {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (m : (𝔹)ˣ) {x : 𝔹}
    (hx : x ∈ Submodule.finiteAdeleBox (meetOrder Λ m)) :
    ((m⁻¹ : (𝔹)ˣ) : 𝔹) * x * (m : 𝔹) ∈ Submodule.finiteAdeleBox Λ := by
  have hx' : x ∈ Submodule.finiteAdeleBox (Submodule.conjByFiniteIdele Λ m) :=
    box_mono (inf_le_right : meetOrder Λ m ≤ Submodule.conjByFiniteIdele Λ m) hx
  rw [Submodule.finiteAdeleBox_conjByFiniteIdele Λ hΛ.fg hΛ.spanTop m, mem_map_conj_iff] at hx'
  exact hx'

theorem inter_core {A : Type*} [Ring A] (S : AddSubgroup A) (hS : ∀ {s t : A}, s ∈ S → t ∈ S → s * t ∈ S)
    {hv hiv mv miv : A} (h1 : hv * hiv = 1) (h3 : mv * miv = 1)
    (H : hiv ∈ S ∧ miv * hv * mv ∈ S ∧ miv * hiv * mv ∈ S ∧ mv ∈ S)
    (y : A) : (hiv * y ∈ S ∧ miv * y ∈ S) ↔ miv * hiv * y ∈ S := by
  have k3 : ∀ t, mv * (miv * t) = t := fun t => by rw [← mul_assoc, h3, one_mul]
  have k1 : ∀ t, hv * (hiv * t) = t := fun t => by rw [← mul_assoc, h1, one_mul]
  obtain ⟨hhi, hu, hui, hm⟩ := H
  constructor
  · rintro ⟨-, hy2⟩
    have : miv * hiv * y = (miv * hiv * mv) * (miv * y) := by
      rw [mul_assoc (miv * hiv) mv, k3]
    rw [this]; exact hS hui hy2
  · intro hy
    have hy2 : miv * y ∈ S := by
      have : miv * y = (miv * hv * mv) * (miv * hiv * y) := by
        simp only [mul_assoc]; rw [k3, k1]
      rw [this]; exact hS hu hy
    refine ⟨?_, hy2⟩
    have : hiv * y = hiv * (mv * (miv * y)) := by rw [k3]
    rw [this]; exact hS hhi (hS hm hy2)

end Global2

section Frame

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

p2m_open "QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.CerednikDrinfeld"

variable (Λ₁ : Submodule ℤ ℍ[ℚ, a, b]) (hΛo : IsOrder Λ₁) (v : HeightOneSpectrum (𝓞 ℚ))
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
  (hφ1 : ∀ r : v.adicCompletion ℚ,
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
  (hφΛ : ∀ x, x ∈ Submodule.localBox Λ₁ v ↔ φ x ∈ intMat v)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))
local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v

include hφ1 in
theorem map_one_tmul_mul (c : 𝕂) (x : ℍv) : φ (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x) = c • φ x := by
  rw [map_mul, hφ1, smul_mul_assoc, one_mul]

omit φ in
theorem one_tmul_natCast_inv_mul_cancel (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((pr v : ℕ) : w.adicCompletion ℚ)⁻¹) *
      (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((pr v : ℕ) : w.adicCompletion ℚ)) * x) = x := by
  rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    inv_mul_cancel₀ (natCast_ne_zero_of_notMem w (pr_notMem_asIdeal_of_ne v w hw))]
  change (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * x = x
  rw [one_mul]

omit φ in

theorem local_mem_of_mem_primeHeckeSet {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) {g : (𝔹)ˣ}
    (hg : g ∈ primeHeckeSet R (pr v)) :
    (∀ w, w ≠ v → ev w (g : 𝔹) ∈ Submodule.localBox R w ∧
      ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w) ∧
    ev v (g : 𝔹) ∈ Submodule.localBox R v ∧
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ϖ) * ev v ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R v := by
  obtain ⟨h1, h2, -, -⟩ := hg
  have hw1 : ∀ w, ev w (g : 𝔹) ∈ Submodule.localBox R w := (mem_box_iff hRo _).1 h1
  have hw2' : ∀ w, ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((pr v : ℕ) : w.adicCompletion ℚ)) *
      ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := by
    intro w
    have := (mem_box_iff hRo _).1 h2 w
    rwa [ev_ratCast_smul, map_natCast] at this
  have hw2 : ∀ w, w ≠ v → ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := fun w hw => by
    have := one_tmul_mul_mem_localBox R w (hw2' w)
      (natCast_inv_mem_integers w (pr_notMem_asIdeal_of_ne v w hw))
    rwa [one_tmul_natCast_inv_mul_cancel v w hw] at this
  exact ⟨fun w hw => ⟨hw1 w, hw2 w hw⟩, hw1 v, hw2' v⟩

include hφ1 hφΛ in

theorem local_of_mem_primeHeckeSet (hRo : IsOrder Λ₁) {g : (𝔹)ˣ} (hg : g ∈ primeHeckeSet Λ₁ (pr v)) :
    (∀ w, w ≠ v → ev w (g : 𝔹) ∈ Submodule.localBox Λ₁ w ∧
      ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox Λ₁ w) ∧
    φ (ev v (g : 𝔹)) ∈ intMat v ∧ ϖ • φ (ev v ((g⁻¹ : (𝔹)ˣ) : 𝔹)) ∈ intMat v ∧
    φ (ev v ((g⁻¹ : (𝔹)ˣ) : 𝔹)) ∉ intMat v ∧ ϖ⁻¹ • φ (ev v (g : 𝔹)) ∉ intMat v := by
  obtain ⟨hw, hv1, hv2⟩ := local_mem_of_mem_primeHeckeSet v hRo hg
  obtain ⟨h1, h2, h3, h4⟩ := hg
  refine ⟨hw, (hφΛ _).1 hv1, ?_, ?_, ?_⟩
  · rw [← map_one_tmul_mul v φ hφ1]; exact (hφΛ _).1 hv2
  · intro H
    apply h3
    rw [mem_box_iff hRo]
    intro w
    by_cases hw' : w = v
    · obtain rfl : v = w := (‹w = v›).symm; exact (hφΛ _).2 H
    · exact (hw w hw').2
  · intro H
    apply h4
    rw [mem_box_iff hRo]
    intro w
    rw [ev_ratCast_smul, map_inv₀, map_natCast]
    by_cases hw' : w = v
    · obtain rfl : v = w := (‹w = v›).symm; rw [hφΛ, map_one_tmul_mul _ φ hφ1]; exact H
    · exact one_tmul_mul_mem_localBox Λ₁ w (hw w hw').1 (natCast_inv_mem_integers w (pr_notMem_asIdeal_of_ne v w hw'))

variable (m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  (hm₁ : ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
    Submodule.finiteAdeleBox Λ₁)
  (e : ℕ) (he : 1 ≤ e) (K Ki : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
  (hK : K ∈ intMat v) (hKi : Ki ∈ intMat v) (hKK : K * Ki = 1) (hKK' : Ki * K = 1)
  (hmv : φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
    ((m : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) = dM v e * K)

include hKK hKK' hmv in

theorem map_ev_inv_eq : φ (ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹)) = Ki * dMi v e := by
  have h1 : φ (ev v (m : 𝔹)) * φ (ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹)) = 1 := by
    rw [← map_mul, ev_units_mul_inv, map_one]
  have h2 : (Ki * dMi v e) * (dM v e * K) = 1 := by
    calc (Ki * dMi v e) * (dM v e * K) = Ki * (dMi v e * dM v e) * K := by noncomm_ring
      _ = 1 := by rw [dMi_mul_dM, mul_one, hKK']
  rw [hmv] at h1
  exact (left_inv_eq_right_inv h2 h1).symm

include hΛo hφ1 hφΛ hK hKi hKK hKK' hmv in

theorem mem_localBox_meetOrder_iff (Y : ℍv) :
    Y ∈ Submodule.localBox (meetOrder Λ₁ m) v ↔ φ Y ∈ intMat v ∧ dMi v e * φ Y * dM v e ∈ intMat v := by
  have hc : IsOrder (Submodule.conjByFiniteIdele Λ₁ m) := QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ₁ hΛo m
  have hmi := map_ev_inv_eq v φ m e K Ki hKK hKK' hmv
  rw [show meetOrder Λ₁ m = Λ₁ ⊓ Submodule.conjByFiniteIdele Λ₁ m from rfl,
    Submodule.localBox_inf Λ₁ _ hΛo.fg hΛo.spanTop hc.fg hc.spanTop v, AddSubgroup.mem_inf, hφΛ,
    Submodule.mem_localBox_conjByFiniteIdele_iff Λ₁ hΛo.fg hΛo.spanTop m v Y]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [map_mul, map_mul, hmv, hmi]
    have e1 : dMi v e * (dM v e * K * φ y * (Ki * dMi v e)) * dM v e = K * φ y * Ki := by
      calc dMi v e * (dM v e * K * φ y * (Ki * dMi v e)) * dM v e
          = (dMi v e * dM v e) * K * φ y * Ki * (dMi v e * dM v e) := by noncomm_ring
        _ = K * φ y * Ki := by rw [dMi_mul_dM, one_mul, mul_one]
    rw [e1]
    exact (conj_mem_intMat_iff v hKi hK hKK' hKK).2 ((hφΛ y).1 hy)
  · intro h
    refine ⟨ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹) * Y * ev v (m : 𝔹), ?_, ?_⟩
    · rw [hφΛ, map_mul, map_mul, hmv, hmi]
      have e1 : Ki * dMi v e * φ Y * (dM v e * K) = Ki * (dMi v e * φ Y * dM v e) * K := by noncomm_ring
      rw [e1]; exact (conj_mem_intMat_iff v hK hKi hKK hKK').2 h
    · rw [← mul_assoc, ← mul_assoc, ev_units_mul_inv, one_mul, mul_assoc, ev_units_mul_inv, mul_one]

include hΛo hφ1 hφΛ hK hKi hKK hKK' hmv in

theorem conj_mem_of_le_conj {h : (𝔹)ˣ} (hle : meetOrder Λ₁ m ≤ Submodule.conjByFiniteIdele Λ₁ h)
    {X : M₂} (hX : X ∈ intMat v) (hXd : dMi v e * X * dM v e ∈ intMat v) :
    φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) * X * φ (ev v (h : 𝔹)) ∈ intMat v := by
  set Y := φ.symm X with hYdef
  have hY : Y ∈ Submodule.localBox (meetOrder Λ₁ m) v :=
    (mem_localBox_meetOrder_iff Λ₁ hΛo v φ hφ1 hφΛ m e K Ki hK hKi hKK hKK' hmv Y).2
      (by rw [hYdef, RingEquiv.apply_symm_apply]; exact ⟨hX, hXd⟩)
  have hY' : Y ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ₁ h) v := localBox_mono v hle hY
  obtain ⟨y, hy, hYeq⟩ := (Submodule.mem_localBox_conjByFiniteIdele_iff Λ₁ hΛo.fg hΛo.spanTop h v Y).1 hY'
  have hyeq : ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹) * Y * ev v (h : 𝔹) = y := by
    rw [hYeq, ← mul_assoc, ← mul_assoc, ev_units_inv_mul, one_mul, mul_assoc, ev_units_inv_mul, mul_one]
  have hint := (hφΛ y).1 hy
  rw [← hyeq, map_mul, map_mul, hYdef, RingEquiv.apply_symm_apply] at hint
  exact hint

include hΛo hφ1 hφΛ hK hKi hKK hKK' hmv in

theorem le_conj_of_forall_conj_mem {h : (𝔹)ˣ}
    (hw : ∀ w, w ≠ v → ev w (h : 𝔹) ∈ Submodule.localBox Λ₁ w ∧ ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox Λ₁ w)
    (H : ∀ X : M₂, X ∈ intMat v → dMi v e * X * dM v e ∈ intMat v →
      φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) * X * φ (ev v (h : 𝔹)) ∈ intMat v) :
    meetOrder Λ₁ m ≤ Submodule.conjByFiniteIdele Λ₁ h := by
  intro z hz
  rw [mem_conj_iff, mem_box_iff hΛo]
  intro w
  rw [map_mul, map_mul, ev_tmul_one]
  by_cases hw' : w = v
  · obtain rfl : v = w := (‹w = v›).symm
    rw [hφΛ, map_mul, map_mul]
    have hzv : z ⊗ₜ[ℚ] (1 : 𝕂) ∈ Submodule.localBox (meetOrder Λ₁ m) v := tmul_one_mem_localBox _ v hz
    obtain ⟨hX, hXd⟩ := (mem_localBox_meetOrder_iff Λ₁ hΛo v φ hφ1 hφΛ m e K Ki hK hKi hKK hKK' hmv _).1 hzv
    exact H _ hX hXd
  · have hzΛ : z ∈ Λ₁ := (inf_le_left : meetOrder Λ₁ m ≤ Λ₁) hz
    have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ₁ → y ∈ Λ₁ → x * y ∈ Λ₁ := fun x y hx hy => hΛo.mul_mem hx hy
    exact mul_mem_localBox Λ₁ w hmul
      (mul_mem_localBox Λ₁ w hmul (hw w hw').2 (tmul_one_mem_localBox Λ₁ w hzΛ)) (hw w hw').1

include hΛo hφΛ hm₁ hK hKi hKK hmv in

theorem inv_mul_mem_box_iff {h : (𝔹)ˣ}
    (hw : ∀ w, w ≠ v → ev w (h : 𝔹) ∈ Submodule.localBox Λ₁ w ∧ ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox Λ₁ w) :
    ((h⁻¹ * m : (𝔹)ˣ) : 𝔹) ∈ Submodule.finiteAdeleBox Λ₁ ↔ φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) * dM v e ∈ intMat v := by
  rw [mem_box_iff hΛo]
  constructor
  · intro H
    have := H v
    rw [hφΛ, Units.val_mul, map_mul, map_mul, hmv, ← mul_assoc] at this
    have e1 : φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) * dM v e = (φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) * dM v e * K) * Ki := by
      rw [mul_assoc _ K, hKK, mul_one]
    rw [e1]; exact (intMat v).mul_mem this hKi
  · intro H w
    rw [Units.val_mul, map_mul]
    by_cases hw' : w = v
    · obtain rfl : v = w := (‹w = v›).symm
      rw [hφΛ, map_mul, hmv, ← mul_assoc]; exact (intMat v).mul_mem H hK
    · have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ₁ → y ∈ Λ₁ → x * y ∈ Λ₁ := fun x y hx hy => hΛo.mul_mem hx hy
      exact mul_mem_localBox Λ₁ w hmul (hw w hw').2 ((mem_box_iff hΛo _).1 hm₁ w)

include hΛo hφ1 hφΛ hm₁ hK hKi hKK hKK' hmv in

theorem not_le_at {h : (𝔹)ˣ} (hh : h ∈ levelHeckeUSet Λ₁ (meetOrder Λ₁ m) (pr v))
    (hhT : h ∈ primeHeckeSet Λ₁ (pr v)) (x : (𝔹)ˣ) :
    ¬ Submodule.ofFiniteIdele Λ₁ (x * m) ≤ Submodule.ofFiniteIdele Λ₁ (x * h) := by
  intro hle
  obtain ⟨-, -, hU3⟩ := hh
  obtain ⟨hw, hη, -, -, -⟩ := local_of_mem_primeHeckeSet Λ₁ v φ hφ1 hφΛ hΛo hhT
  have h2 : φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) * φ (ev v (h : 𝔹)) = 1 := by rw [← map_mul, ev_units_inv_mul, map_one]
  have hbox : ((h⁻¹ * m : (𝔹)ˣ) : 𝔹) ∈ Submodule.finiteAdeleBox Λ₁ := (ofFiniteIdele_mul_le_iff hΛo x m h).1 hle
  have hηid := (inv_mul_mem_box_iff Λ₁ hΛo v φ hφΛ m hm₁ e K Ki hK hKi hKK hmv hw).1 hbox
  exact hU3 (le_conj_of_forall_conj_mem Λ₁ hΛo v φ hφ1 hφΛ m e K Ki hK hKi hKK hKK' hmv hw
    (fun X hX hXd => conj_mem_intMat_of_inv_mul_dM_mem v e h2 hη hηid hX hXd))

include hΛo hφ1 hφΛ hm₁ he hK hKi hKK hKK' hmv in

theorem mem_levelHeckeUSet_at {h : (𝔹)ˣ} (hhT : h ∈ primeHeckeSet Λ₁ (pr v))
    (hhR : h ∈ primeHeckeSet (meetOrder Λ₁ m) (pr v)) (x : (𝔹)ˣ)
    (hoff : ¬ Submodule.ofFiniteIdele Λ₁ (x * m) ≤ Submodule.ofFiniteIdele Λ₁ (x * h)) :
    h ∈ levelHeckeUSet Λ₁ (meetOrder Λ₁ m) (pr v) := by
  obtain ⟨hw, hη, hpηi, hηi_not, hpη_not⟩ := local_of_mem_primeHeckeSet Λ₁ v φ hφ1 hφΛ hΛo hhT
  set η := φ (ev v (h : 𝔹)) with hηdef
  set ηi := φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) with hηidef
  have h1 : η * ηi = 1 := by rw [hηdef, hηidef, ← map_mul, ev_units_mul_inv, map_one]
  have h2 : ηi * η = 1 := by rw [hηdef, hηidef, ← map_mul, ev_units_inv_mul, map_one]
  obtain ⟨K1, K1i, K2, K2i, hK1, hK1i, hK2, hK2i, hKK1, hKK1', hKK2, hKK2', hcart⟩ :=
    exists_eq_mul_tM_mul v h1 h2 hη hpηi hηi_not hpη_not
  have not3 : ¬ meetOrder Λ₁ m ≤ Submodule.conjByFiniteIdele Λ₁ h := by
    intro hle
    have hc00 := conj_mem_of_le_conj Λ₁ hΛo v φ hφ1 hφΛ m e K Ki hK hKi hKK hKK' hmv hle (E00_mem v)
      ((dMi_mul_mul_dM_mem_iff v e (E00_mem v)).2 (by simp [E00, zero_mem]))
    have hc01 := conj_mem_of_le_conj Λ₁ hΛo v φ hφ1 hφΛ m e K Ki hK hKi hKK hKK' hmv hle (E01_mem v)
      ((dMi_mul_mul_dM_mem_iff v e (E01_mem v)).2 (by simp [E01, zero_mem]))
    have h00 : ηi * E00 v ∈ intMat v := inv_mul_E00_mem_of_conj_mem v hK1 hK1i hK2i hKK1 hKK2 hcart hc00 hc01
    have hηid : ηi * dM v e ∈ intMat v := inv_mul_dM_mem_of_inv_mul_E00_mem v he hpηi h00
    exact hoff ((ofFiniteIdele_mul_le_iff hΛo x m h).2
      ((inv_mul_mem_box_iff Λ₁ hΛo v φ hφΛ m hm₁ e K Ki hK hKi hKK hmv hw).2 hηid))
  refine ⟨hhR, fun heq => not3 ?_, not3⟩
  calc meetOrder Λ₁ m = Submodule.conjByFiniteIdele (meetOrder Λ₁ m) h := heq.symm
    _ ≤ Submodule.conjByFiniteIdele Λ₁ h := conj_mono inf_le_left h

include hΛo hφ1 hφΛ hm₁ he hK hKi hKK hKK' hmv in

theorem inf_eq_at {h : (𝔹)ˣ} (hh : h ∈ levelHeckeUSet Λ₁ (meetOrder Λ₁ m) (pr v))
    (hhT : h ∈ primeHeckeSet Λ₁ (pr v)) (x : (𝔹)ˣ) :
    Submodule.ofFiniteIdele Λ₁ (x * h) ⊓ Submodule.ofFiniteIdele Λ₁ (x * m) =
      Submodule.ofFiniteIdele Λ₁ (x * h * m) := by
  have hR : IsOrder (meetOrder Λ₁ m) := hΛo.inf (QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ₁ hΛo m)
  obtain ⟨hhR, -, hU3⟩ := hh
  obtain ⟨hw, hη, hpηi, hηi_not, hpη_not⟩ := local_of_mem_primeHeckeSet Λ₁ v φ hφ1 hφΛ hΛo hhT
  obtain ⟨-, hvR1, -⟩ := local_mem_of_mem_primeHeckeSet v hR hhR
  set η := φ (ev v (h : 𝔹)) with hηdef
  set ηi := φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) with hηidef
  have h1 : η * ηi = 1 := by rw [hηdef, hηidef, ← map_mul, ev_units_mul_inv, map_one]
  have h2 : ηi * η = 1 := by rw [hηdef, hηidef, ← map_mul, ev_units_inv_mul, map_one]
  have hηΓ : dMi v e * η * dM v e ∈ intMat v :=
    ((mem_localBox_meetOrder_iff Λ₁ hΛo v φ hφ1 hφΛ m e K Ki hK hKi hKK hKK' hmv _).1 hvR1).2
  have h10 : (ϖ ^ e)⁻¹ * η 1 0 ∈ 𝓞v := (dMi_mul_mul_dM_mem_iff v e hη).1 hηΓ
  obtain ⟨K1, K1i, K2, K2i, hK1, hK1i, hK2, hK2i, hKK1, hKK1', hKK2, hKK2', hcart⟩ :=
    exists_eq_mul_tM_mul v h1 h2 hη hpηi hηi_not hpη_not
  have hdet : Valued.v η.det = Valued.v ϖ := by
    rw [hcart, Matrix.det_mul, Matrix.det_mul, det_tM, map_mul, map_mul, valued_det_eq_one v hK1 hK1i hKK1,
      valued_det_eq_one v hK2 hK2i hKK2, one_mul, mul_one]
  have h00 : ηi * E00 v ∉ intMat v := fun h00 =>
    hU3 (le_conj_of_forall_conj_mem Λ₁ hΛo v φ hφ1 hφΛ m e K Ki hK hKi hKK hKK' hmv hw
      (fun X hX hXd => conj_mem_intMat_of_inv_mul_dM_mem v e h2 hη
        (inv_mul_dM_mem_of_inv_mul_E00_mem v he hpηi h00) hX hXd))
  have h11 : Valued.v (η 1 1) = 1 := valued_apply_one_one_eq_one v he h1 h2 hη hdet h10 h00
  have hmi := map_ev_inv_eq v φ m e K Ki hKK hKK' hmv

  ext z
  simp only [Submodule.mem_inf]
  rw [mem_ofFiniteIdele_iff_inv_mul_mem, mem_ofFiniteIdele_iff_inv_mul_mem, mem_ofFiniteIdele_iff_inv_mul_mem,
    mem_box_iff hΛo, mem_box_iff hΛo, mem_box_iff hΛo, ← forall_and]
  refine forall_congr' fun w => ?_
  set y := ev w (((x⁻¹ : (𝔹)ˣ) : 𝔹) * (z ⊗ₜ[ℚ] (1 : 𝔸f))) with hy
  have e1 : ev w ((((x * h)⁻¹ : (𝔹)ˣ) : 𝔹) * (z ⊗ₜ[ℚ] (1 : 𝔸f))) = ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) * y := by
    rw [_root_.mul_inv_rev, Units.val_mul, mul_assoc, map_mul]
  have e2 : ev w ((((x * m)⁻¹ : (𝔹)ˣ) : 𝔹) * (z ⊗ₜ[ℚ] (1 : 𝔸f))) = ev w ((m⁻¹ : (𝔹)ˣ) : 𝔹) * y := by
    rw [_root_.mul_inv_rev, Units.val_mul, mul_assoc, map_mul]
  have e3 : ev w ((((x * h * m)⁻¹ : (𝔹)ˣ) : 𝔹) * (z ⊗ₜ[ℚ] (1 : 𝔸f))) =
      ev w ((m⁻¹ : (𝔹)ˣ) : 𝔹) * ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) * y := by
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, mul_assoc, mul_assoc, map_mul, map_mul, ← mul_assoc]
  rw [e1, e2, e3]
  by_cases hw' : w = v
  · obtain rfl : v = w := (‹w = v›).symm
    rw [hφΛ, hφΛ, hφΛ, map_mul, map_mul, map_mul, map_mul, hmi, ← hηidef]
    set Y := φ y with hYdef
    have hKiff : ∀ Z : M₂, Ki * dMi v e * Z ∈ intMat v ↔ dMi v e * Z ∈ intMat v := by
      intro Z
      constructor
      · intro H
        have := (intMat v).mul_mem hK H
        rwa [← mul_assoc, ← mul_assoc, hKK, one_mul] at this
      · intro H
        rw [mul_assoc]
        exact (intMat v).mul_mem hKi H
    rw [hKiff, show Ki * dMi v e * ηi * Y = Ki * dMi v e * (ηi * Y) by noncomm_ring, hKiff]
    constructor
    · rintro ⟨hA, hdY⟩
      exact dMi_mul_inv_mul_mem v h1 h10 h11 hA hdY
    · intro H
      refine ⟨?_, ?_⟩
      · have := (intMat v).mul_mem (dM_mem v e) H
        rwa [← mul_assoc, dM_mul_dMi, one_mul] at this
      · have eq : dMi v e * Y = (dMi v e * η * dM v e) * (dMi v e * (ηi * Y)) := by
          calc dMi v e * Y = dMi v e * (η * (dM v e * dMi v e) * ηi) * Y := by
                rw [dM_mul_dMi, mul_one, h1, mul_one]
            _ = (dMi v e * η * dM v e) * (dMi v e * (ηi * Y)) := by simp only [mul_assoc]
        rw [eq]
        exact (intMat v).mul_mem hηΓ H
  · have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ₁ → y ∈ Λ₁ → x * y ∈ Λ₁ := fun x y hx hy => hΛo.mul_mem hx hy
    have Hm : ev w (m : 𝔹) ∈ Submodule.localBox Λ₁ w := (mem_box_iff hΛo _).1 hm₁ w
    have Hu : ev w ((m⁻¹ : (𝔹)ˣ) : 𝔹) * ev w (h : 𝔹) * ev w (m : 𝔹) ∈ Submodule.localBox Λ₁ w := by
      have := (mem_box_iff hΛo _).1 (conj_mem_box_of_mem_box_meetOrder hΛo m hhR.1) w
      rwa [map_mul, map_mul] at this
    have Hui : ev w ((m⁻¹ : (𝔹)ˣ) : 𝔹) * ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) * ev w (m : 𝔹) ∈ Submodule.localBox Λ₁ w := by
      have hc := conj_mem_box_of_mem_box_meetOrder hΛo m hhR.2.1
      rw [mul_smul_comm, smul_mul_assoc] at hc
      have h3 := (mem_box_iff hΛo _).1 hc w
      rw [ev_ratCast_smul, map_natCast, map_mul, map_mul] at h3
      have h4 := one_tmul_mul_mem_localBox Λ₁ w h3
        (natCast_inv_mem_integers w (pr_notMem_asIdeal_of_ne v w hw'))
      rwa [one_tmul_natCast_inv_mul_cancel v w hw'] at h4
    exact inter_core (Submodule.localBox Λ₁ w) (fun hs ht => mul_mem_localBox Λ₁ w hmul hs ht)
      (ev_units_mul_inv w h) (ev_units_mul_inv w m) ⟨(hw w hw').2, Hu, Hui, Hm⟩ y

end Frame

section Wrapper

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

p2m_open "QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.CerednikDrinfeld"

def pl (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

theorem pr_pl (q : ℕ) (hq : q.Prime) : pr (pl q hq) = q :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨q, hq⟩)

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ℍv" => ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v

def conjRingEquiv (P Pi : M₂) (h1 : P * Pi = 1) (h2 : Pi * P = 1) : M₂ ≃+* M₂ where
  toFun Y := Pi * Y * P
  invFun Y := P * Y * Pi
  left_inv Y := by
    show P * (Pi * Y * P) * Pi = Y
    calc P * (Pi * Y * P) * Pi = (P * Pi) * Y * (P * Pi) := by noncomm_ring
      _ = Y := by rw [h1, one_mul, mul_one]
  right_inv Y := by
    show Pi * (P * Y * Pi) * P = Y
    calc Pi * (P * Y * Pi) * P = (Pi * P) * Y * (Pi * P) := by noncomm_ring
      _ = Y := by rw [h2, one_mul, mul_one]
  map_mul' Y Z := by
    show Pi * (Y * Z) * P = (Pi * Y * P) * (Pi * Z * P)
    rw [show (Pi * Y * P) * (Pi * Z * P) = Pi * Y * (P * Pi) * Z * P by noncomm_ring, h1]
    noncomm_ring
  map_add' Y Z := by
    show Pi * (Y + Z) * P = Pi * Y * P + Pi * Z * P
    rw [mul_add, add_mul]

theorem conjRingEquiv_apply (P Pi : M₂) (h1 : P * Pi = 1) (h2 : Pi * P = 1) (Y : M₂) :
    conjRingEquiv v P Pi h1 h2 Y = Pi * Y * P := rfl

theorem exists_frame (hab : a ≠ 0 ∧ b ≠ 0) {Λ₁ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ₁ : IsMaximalOrder Λ₁)
    (N : ℕ) [NeZero N] (m : (𝔹)ˣ)
    (hm₁ : ((m : (𝔹)ˣ) : 𝔹) ∈ Submodule.finiteAdeleBox Λ₁)
    (hmN : ((N : ℕ) : ℚ) • ((m⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.finiteAdeleBox Λ₁)
    (hRN : (meetOrder Λ₁ m).toAddSubgroup.relIndex Λ₁.toAddSubgroup = N)
    (hv : pr v ∣ N) :
    ∃ φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ r : v.adicCompletion ℚ,
        φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))) ∧
      (∀ x, x ∈ Submodule.localBox Λ₁ v ↔ φ x ∈ intMat v) ∧
      ∃ K Ki : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ), K ∈ intMat v ∧ Ki ∈ intMat v ∧
        K * Ki = 1 ∧ Ki * K = 1 ∧
        φ (ev v (m : 𝔹)) = dM v (padicValNat (pr v) N) * K := by
  obtain ⟨-, hsplit⟩ :=
    QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
      hab hΛ₁ N m hm₁ hmN hRN
  obtain ⟨-, φ₀, hφ₀1, hφ₀Λ, k₁, k₂, hk₁, hk₁i, hk₂, hk₂i, hm0⟩ :=
    hsplit v (pr v) (pr_prime v) (pr_mem_asIdeal v) hv
  set P : M₂ := (k₁ : M₂) with hP
  set Pi : M₂ := ((k₁⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : M₂) with hPi
  have hPPi : P * Pi = 1 := k₁.mul_inv
  have hPiP : Pi * P = 1 := k₁.inv_mul
  set Q : M₂ := (k₂ : M₂) with hQ
  set Qi : M₂ := ((k₂⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) : M₂) with hQi
  have hQQi : Q * Qi = 1 := k₂.mul_inv
  have hQiQ : Qi * Q = 1 := k₂.inv_mul
  refine ⟨φ₀.trans (conjRingEquiv v P Pi hPPi hPiP), fun r => ?_, fun x => ?_, Q * P, Pi * Qi,
    (intMat v).mul_mem hk₂ hk₁, (intMat v).mul_mem hk₁i hk₂i, ?_, ?_, ?_⟩
  · rw [RingEquiv.trans_apply, conjRingEquiv_apply, hφ₀1, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hPiP]
  · rw [RingEquiv.trans_apply, conjRingEquiv_apply, conj_mem_intMat_iff v hk₁ hk₁i hPPi hPiP]
    exact hφ₀Λ x
  · calc Q * P * (Pi * Qi) = Q * (P * Pi) * Qi := by noncomm_ring
      _ = 1 := by rw [hPPi, mul_one, hQQi]
  · calc Pi * Qi * (Q * P) = Pi * (Qi * Q) * P := by noncomm_ring
      _ = 1 := by rw [hQiQ, mul_one, hPiP]
  · rw [RingEquiv.trans_apply, conjRingEquiv_apply, hm0]
    have hd : Matrix.diagonal ![(1 : v.adicCompletion ℚ), ((pr v : ℕ) : v.adicCompletion ℚ) ^ padicValNat (pr v) N] =
        dM v (padicValNat (pr v) N) := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [dM, Matrix.diagonal]
    rw [hd]
    calc Pi * (P * dM v (padicValNat (pr v) N) * Q) * P
        = (Pi * P) * dM v (padicValNat (pr v) N) * (Q * P) := by noncomm_ring
      _ = dM v (padicValNat (pr v) N) * (Q * P) := by rw [hPiP, one_mul]

end Wrapper

end LevelULocal
p2m_reactivate "P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.LevelULocal"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.LevelULocal"

end LevelULocalBlock
p2m_reactivate "P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet.LevelULocal"

open scoped Quaternion TensorProduct NumberField Pointwise in
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
    Submodule.ofFiniteIdele Λ₁ (x * h) ⊓ Submodule.ofFiniteIdele Λ₁ (x * m) =
      Submodule.ofFiniteIdele Λ₁ (x * h * m) := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have he : 1 ≤ padicValNat ℓ N := one_le_padicValNat_of_dvd (NeZero.ne N) hℓN
  have hhT := CerednikDrinfeld.LevelU.levelHeckeUSet_meetOrder_subset hΛ₁.isOrder m ℓ hh
  set v := LevelULocal.pl ℓ hℓ with hvdef
  have hpr : LevelULocal.pr v = ℓ := LevelULocal.pr_pl ℓ hℓ
  rw [← hpr] at hh hhT hℓN he
  obtain ⟨φ, hφ1, hφΛ, K, Ki, hK, hKi, hKK, hKK', hmv⟩ :=
    LevelULocal.exists_frame v hab hΛ₁ N m hm₁ hmN hRN hℓN
  exact LevelULocal.inf_eq_at Λ₁ hΛ₁.isOrder v φ hφ1 hφΛ m hm₁ _ he K Ki hK hKi hKK hKK' hmv hh hhT x

end S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet
end P2MW
export P2MW.S_CerednikDrinfeld_LevelU_ofFiniteIdele_mul_inf_ofFiniteIdele_mul_eq_of_mem_levelHeckeUSet (solution)
