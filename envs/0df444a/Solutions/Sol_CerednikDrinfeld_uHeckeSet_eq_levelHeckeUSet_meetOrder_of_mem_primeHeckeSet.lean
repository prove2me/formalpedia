-- Prove2me | solution 1 for CerednikDrinfeld.uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/052902bf-9a54-5ce8-ae13-b3dd6a100d1b

import Mathlib
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet
import Theorems.Thm_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
import Theorems.Thm_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
import Theorems.Thm_Submodule_exists_mem_add_one_tmul_pow_mul_of_mem_localBox
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_exists_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_eq_of_forall_finiteAdeleEvalAt_eq
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Theorems.Thm_Submodule_ofFiniteIdele_one
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_localBox_eq_localBox_of_isMaximalOrder_of_le_of_not_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_CerednikDrinfeld_uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

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

namespace CosetDict

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

theorem exists_scalar_of_conj_intMat {X Xi : M₂} (h1 : X * Xi = 1)
    (hX : ∀ W ∈ intMat v, X * W * Xi ∈ intMat v) :
    ∃ c : 𝕂, c ≠ 0 ∧ c⁻¹ • X ∈ intMat v ∧ c • Xi ∈ intMat v := by
  have h2 : Xi * X = 1 := mul_eq_one_comm.mp h1
  obtain ⟨c, hc1, hc2⟩ :=
    Matrix.GeneralLinearGroup.exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
      (HeightOneSpectrum.adicCompletionIntegers ℚ v) (⟨X, Xi, h1, h2⟩ : GL (Fin 2) 𝕂)
      (fun M hM => (mem_intMat_iff v _).1 (hX M ((mem_intMat_iff v M).2 hM)))
  refine ⟨(c : 𝕂), c.ne_zero, ?_, ?_⟩
  · intro i j
    rw [Matrix.smul_apply, smul_eq_mul, ← Units.val_inv_eq_inv_val]
    exact hc1 i j
  · intro i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hc2 i j

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

open QuaternionAlgebra CerednikDrinfeld

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

section Frame

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

open QuaternionAlgebra CerednikDrinfeld

variable (R : Submodule ℤ ℍ[ℚ, a, b]) (hRo : IsOrder R) (v : HeightOneSpectrum (𝓞 ℚ))
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
  (hφ1 : ∀ r : v.adicCompletion ℚ,
    φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
  (hφR : ∀ x, x ∈ Submodule.localBox R v ↔ φ x ∈ intMat v)

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

include hRo hφ1 hφR in

theorem local_of_mem_primeHeckeSet {g : (𝔹)ˣ} (hg : g ∈ primeHeckeSet R (pr v)) :
    (∀ w, w ≠ v → ev w (g : 𝔹) ∈ Submodule.localBox R w ∧
      ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w) ∧
    φ (ev v (g : 𝔹)) ∈ intMat v ∧ ϖ • φ (ev v ((g⁻¹ : (𝔹)ˣ) : 𝔹)) ∈ intMat v ∧
    φ (ev v ((g⁻¹ : (𝔹)ˣ) : 𝔹)) ∉ intMat v ∧ ϖ⁻¹ • φ (ev v (g : 𝔹)) ∉ intMat v := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
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
  refine ⟨fun w hw => ⟨hw1 w, hw2 w hw⟩, (hφR _).1 (hw1 v), ?_, ?_, ?_⟩
  · rw [← map_one_tmul_mul v φ hφ1]; exact (hφR _).1 (hw2' v)
  · intro H
    apply h3
    rw [mem_box_iff hRo]
    intro w
    by_cases hw : w = v
    · obtain rfl : v = w := (‹w = v›).symm; exact (hφR _).2 H
    · exact hw2 w hw
  · intro H
    apply h4
    rw [mem_box_iff hRo]
    intro w
    rw [ev_ratCast_smul, map_inv₀, map_natCast]
    by_cases hw : w = v
    · obtain rfl : v = w := (‹w = v›).symm; rw [hφR, map_one_tmul_mul _ φ hφ1]; exact H
    · exact one_tmul_mul_mem_localBox R w (hw1 w) (natCast_inv_mem_integers w (pr_notMem_asIdeal_of_ne v w hw))

variable (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (k₀ k₀i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
  (hk₀ : k₀ ∈ intMat v) (hk₀i : k₀i ∈ intMat v) (hkk : k₀ * k₀i = 1) (hkk' : k₀i * k₀ = 1)
  (hn : φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
    ((n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) = tM v * k₀)
  (hni : φ (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v
    ((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)) =
      k₀i * tMi v)
  (hnw : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
      ((n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        Submodule.localBox R w ∧
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
      ((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
        Submodule.localBox R w)

include hRo in
omit φ in
theorem isOrder_meetOrder : IsOrder (meetOrder R n) :=
  hRo.inf (QuaternionAlgebra.IsOrder.conjByFiniteIdele R hRo n)

omit φ n in
theorem zsmul_tmul_one (m : ℤ) (z : ℍ[ℚ, a, b]) (w : HeightOneSpectrum (𝓞 ℚ)) :
    (m • z) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (m : w.adicCompletion ℚ)) * (z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, ← Int.cast_smul_eq_zsmul ℚ,
    TensorProduct.smul_tmul]
  congr 1
  simp [Algebra.smul_def]

include hRo hφ1 hφR hk₀ hk₀i hkk hkk' hn hni hnw in

theorem pr_smul_mem_meetOrder {z : ℍ[ℚ, a, b]} (hz : z ∈ R) : ((pr v : ℕ) : ℤ) • z ∈ meetOrder R n := by
  show _ ∈ R ⊓ Submodule.conjByFiniteIdele R n
  rw [Submodule.mem_inf]
  refine ⟨Submodule.smul_mem _ _ hz, ?_⟩
  rw [mem_conj_iff, mem_box_iff hRo]
  intro w
  rw [map_mul, map_mul, ev_tmul_one, zsmul_tmul_one, Int.cast_natCast]
  by_cases hw : w = v
  · obtain rfl : v = w := (‹w = v›).symm
    rw [hφR, map_mul, map_mul, map_one_tmul_mul _ φ hφ1, hn, hni]
    have hZ : φ (z ⊗ₜ[ℚ] (1 : 𝕂)) ∈ intMat v := (hφR _).1 (tmul_one_mem_localBox R _ hz)
    have e : k₀i * tMi v * (ϖ • φ (z ⊗ₜ[ℚ] (1 : 𝕂))) * (tM v * k₀) =
        k₀i * ((ϖ • tMi v) * φ (z ⊗ₜ[ℚ] (1 : 𝕂)) * tM v) * k₀ := by
      simp only [Matrix.smul_mul, Matrix.mul_smul]
      congr 1
      noncomm_ring
    rw [e, smul_tMi]
    exact conj_mem_intMat v hk₀ hk₀i ((intMat v).mul_mem ((intMat v).mul_mem (tbM_mem v) hZ) (tM_mem v))
  · have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ R → y ∈ R → x * y ∈ R := fun x y hx hy => hRo.mul_mem hx hy
    refine mul_mem_localBox R w hmul (mul_mem_localBox R w hmul (hnw w hw).2 ?_) (hnw w hw).1
    exact one_tmul_mul_mem_localBox R w (tmul_one_mem_localBox R w hz) (natCast_mem_integers w _)

include hRo hφ1 hφR hk₀ hk₀i hkk hkk' hn hni hnw in

theorem localBox_le_meetOrder_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) :
    Submodule.localBox R w ≤ Submodule.localBox (meetOrder R n) w :=
  localBox_le_of_nsmul_mem w (pr_notMem_asIdeal_of_ne v w hw)
    fun z hz => pr_smul_mem_meetOrder R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw hz

include hRo hφ1 hφR hk₀ hk₀i hkk hkk' hn hni hnw in

theorem mem_localBox_meetOrder_of {Y : ℍv} (hY1 : φ Y ∈ intMat v) (hY2 : tMi v * φ Y * tM v ∈ intMat v) :
    Y ∈ Submodule.localBox (meetOrder R n) v := by
  have hYR : Y ∈ Submodule.localBox R v := (hφR _).2 hY1
  obtain ⟨z, hz, E, hE, hYeq⟩ := exists_approx hRo v hYR
  have hEint : φ E ∈ intMat v := (hφR _).1 hE

  have hzS : z ∈ meetOrder R n := by
    show _ ∈ R ⊓ Submodule.conjByFiniteIdele R n
    rw [Submodule.mem_inf]
    refine ⟨hz, ?_⟩
    rw [mem_conj_iff, mem_box_iff hRo]
    intro w
    rw [map_mul, map_mul, ev_tmul_one]
    by_cases hw : w = v
    · obtain rfl : v = w := (‹w = v›).symm
      have hz1 : z ⊗ₜ[ℚ] (1 : 𝕂) = Y - ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ϖ) * E := by rw [hYeq]; abel
      rw [hφR, map_mul, map_mul, hn, hni, hz1, map_sub, map_one_tmul_mul _ φ hφ1]
      have e : k₀i * tMi v * (φ Y - ϖ • φ E) * (tM v * k₀) =
          k₀i * (tMi v * φ Y * tM v - (ϖ • tMi v) * φ E * tM v) * k₀ := by
        rw [Matrix.smul_mul, Matrix.smul_mul, ← Matrix.mul_smul]; noncomm_ring
      rw [e, smul_tMi]
      exact conj_mem_intMat v hk₀ hk₀i (sub_mem hY2
        ((intMat v).mul_mem ((intMat v).mul_mem (tbM_mem v) hEint) (tM_mem v)))
    · have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ R → y ∈ R → x * y ∈ R := fun x y hx hy => hRo.mul_mem hx hy
      exact mul_mem_localBox R w hmul (mul_mem_localBox R w hmul (hnw w hw).2
        (tmul_one_mem_localBox R w hz)) (hnw w hw).1

  have hpE : ∀ E' : ℍv, E' ∈ Submodule.localBox R v →
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ϖ) * E' ∈ Submodule.localBox (meetOrder R n) v := by
    intro E' hE'
    induction hE' using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨z', hz', c, hc, rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      have : z' ⊗ₜ[ℚ] (ϖ * c) = (((pr v : ℕ) : ℤ) • z') ⊗ₜ[ℚ] c := by
        rw [← Int.cast_smul_eq_zsmul ℚ, TensorProduct.smul_tmul, Int.cast_natCast]
        congr 1
        simp [Algebra.smul_def]
      rw [this]
      exact tmul_mem_localBox _ v (pr_smul_mem_meetOrder R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw hz') hc
    | zero => rw [mul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
    | neg x _ hx => exact (mul_neg _ x).symm ▸ neg_mem hx
  rw [hYeq]
  exact add_mem (tmul_one_mem_localBox _ v hzS) (hpE E hE)

include hRo hφ1 hφR hk₀ hk₀i hkk hkk' hn hni hnw in

theorem shape_of_mem_uHeckeSet {h : (𝔹)ˣ} (hh : h ∈ uHeckeSet R n (pr v)) :
    (∀ w, w ≠ v → ev w (h : 𝔹) ∈ Submodule.localBox R w ∧
      ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w) ∧
    ∃ k' k'i : M₂, k' ∈ intMat v ∧ k'i ∈ intMat v ∧ k' * k'i = 1 ∧ k'i * k' = 1 ∧
      φ (ev v (h : 𝔹)) = k' * tbM v ∧ φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) = tbMi v * k'i ∧
      Valued.v (k' 1 1) = 1 := by
  obtain ⟨⟨hh1, hh2, hh3, hh4⟩, hconj, hne⟩ := hh
  have hp0 := pr_ne_zero' v
  have hSR : Submodule.finiteAdeleBox (meetOrder R n) ≤ Submodule.finiteAdeleBox R := box_mono inf_le_left
  set H := φ (ev v (h : 𝔹)) with hH
  set Hi := φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) with hHi
  have hHHi : H * Hi = 1 := by rw [hH, hHi, ← map_mul, ev_units_mul_inv, map_one]
  have hHiH : Hi * H = 1 := by rw [hH, hHi, ← map_mul, ev_units_inv_mul, map_one]

  have hw1 : ∀ w, ev w (h : 𝔹) ∈ Submodule.localBox R w := (mem_box_iff hRo _).1 (hSR hh1)
  have hw2' : ∀ w, ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((pr v : ℕ) : w.adicCompletion ℚ)) *
      ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := by
    intro w
    have := (mem_box_iff hRo _).1 (hSR hh2) w
    rwa [ev_ratCast_smul, map_natCast] at this
  have hw2 : ∀ w, w ≠ v → ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := fun w hw => by
    have := one_tmul_mul_mem_localBox R w (hw2' w)
      (natCast_inv_mem_integers w (pr_notMem_asIdeal_of_ne v w hw))
    rwa [one_tmul_natCast_inv_mul_cancel v w hw] at this
  have hHint : H ∈ intMat v := (hφR _).1 (hw1 v)
  have hpHi : ϖ • Hi ∈ intMat v := by
    rw [hHi, ← map_one_tmul_mul v φ hφ1]; exact (hφR _).1 (hw2' v)

  have hconj' : Submodule.conjByFiniteIdele R (h * n) = Submodule.conjByFiniteIdele R 1 := by
    rw [← conj_conj_eq hRo n h, hconj, conj_one_eq hRo]
  set X := H * (tM v * k₀) with hX
  set Xi := k₀i * tMi v * Hi with hXi
  have hXXi : X * Xi = 1 := by
    calc X * Xi = H * (tM v * (k₀ * k₀i) * tMi v) * Hi := by simp only [hX, hXi]; noncomm_ring
      _ = 1 := by rw [hkk, mul_one, tM_mul_tMi, mul_one, hHHi]
  have hXiX : Xi * X = 1 := by
    calc Xi * X = k₀i * (tMi v * (Hi * H) * tM v) * k₀ := by simp only [hX, hXi]; noncomm_ring
      _ = 1 := by rw [hHiH, mul_one, tMi_mul_tM, mul_one, hkk']
  have hloc : ∀ W : M₂, Xi * W * X ∈ intMat v ↔ W ∈ intMat v := by
    intro W
    obtain ⟨x, hxv, hxw⟩ := exists_adele_at hRo v (φ.symm W)
    have key := conj_mem_box_iff_of_conj_eq hRo hconj' x
    rw [inv_one, Units.val_one, one_mul, mul_one, mem_box_iff hRo, mem_box_iff hRo] at key
    have e1 : (∀ w, ev w ((((h * n)⁻¹ : (𝔹)ˣ) : 𝔹) * x * ((h * n : (𝔹)ˣ) : 𝔹)) ∈ Submodule.localBox R w) ↔
        ev v ((((h * n)⁻¹ : (𝔹)ˣ) : 𝔹) * x * ((h * n : (𝔹)ˣ) : 𝔹)) ∈ Submodule.localBox R v :=
      ⟨fun H' => H' v, fun H' w => by
        by_cases hw : w = v
        · obtain rfl : v = w := (‹w = v›).symm; exact H'
        · rw [map_mul, map_mul, hxw w hw, mul_zero, zero_mul]; exact zero_mem _⟩
    have e2 : (∀ w, ev w x ∈ Submodule.localBox R w) ↔ ev v x ∈ Submodule.localBox R v :=
      ⟨fun H' => H' v, fun H' w => by
        by_cases hw : w = v
        · obtain rfl : v = w := (‹w = v›).symm; exact H'
        · rw [hxw w hw]; exact zero_mem _⟩
    have eφ : φ (ev v ((((h * n)⁻¹ : (𝔹)ˣ) : 𝔹) * x * ((h * n : (𝔹)ˣ) : 𝔹))) = Xi * W * X := by
      simp only [_root_.mul_inv_rev, Units.val_mul, map_mul]
      rw [hxv, RingEquiv.apply_symm_apply, hn, hni, ← hH, ← hHi]
    rw [e1, e2, hφR, hφR, eφ, hxv, RingEquiv.apply_symm_apply] at key
    exact key
  have hX' : ∀ W ∈ intMat v, X * W * Xi ∈ intMat v := fun W hW => by
    refine (hloc _).1 ?_
    have e : Xi * (X * W * Xi) * X = (Xi * X) * W * (Xi * X) := by noncomm_ring
    rwa [e, hXiX, one_mul, mul_one]
  obtain ⟨c, hc0, hcX, hcXi⟩ := exists_scalar_of_conj_intMat v hXXi hX'

  have hdetX : Valued.v X.det = Valued.v c ^ 2 := valued_det_eq_sq v hc0 hXXi hcX hcXi
  have hk₀det : Valued.v k₀.det = 1 := valued_det_eq_one v hk₀ hk₀i hkk
  obtain ⟨m, hm2, hm0, hm⟩ := valued_det_bounds v hHHi hHint hpHi
  obtain ⟨e, he⟩ : ∃ e : ℤ, Valued.v c = WithZero.exp e :=
    ⟨WithZero.log _, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hc0)).symm⟩
  have hme : m = -1 ∧ e = -1 := by
    rw [hX, Matrix.det_mul, Matrix.det_mul, det_tM, map_mul, map_mul, hm, hk₀det, valued_pr, he, mul_one,
      ← WithZero.exp_add, ← WithZero.exp_nsmul, WithZero.exp_inj] at hdetX
    simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at hdetX
    omega
  obtain ⟨rfl, rfl⟩ := hme
  have hvc : Valued.v c = Valued.v ϖ := by rw [he, valued_pr]
  have hu : ϖ⁻¹ * c ∈ 𝓞v := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hvc, inv_mul_cancel₀]
    rw [valued_pr]; exact WithZero.coe_ne_zero
  have hui : ϖ * c⁻¹ ∈ 𝓞v := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, hvc, mul_inv_cancel₀]
    rw [valued_pr]; exact WithZero.coe_ne_zero

  set k' : M₂ := ϖ⁻¹ • (H * tM v) with hk'
  set k'i : M₂ := ϖ • (tMi v * Hi) with hk'i
  have hk'int : k' ∈ intMat v := by
    have e1 : k' = (ϖ⁻¹ * c) • ((c⁻¹ • X) * k₀i) := by
      rw [hk', hX]
      simp only [Matrix.smul_mul, smul_smul, Matrix.mul_assoc, hkk, Matrix.mul_one]
      rw [mul_assoc, mul_inv_cancel₀ hc0, mul_one]
    rw [e1]; exact smul_mem_intMat v hu ((intMat v).mul_mem hcX hk₀i)
  have hk'iint : k'i ∈ intMat v := by
    have e1 : k'i = (ϖ * c⁻¹) • (k₀ * (c • Xi)) := by
      rw [hk'i, hXi]
      simp only [Matrix.mul_smul, smul_smul, ← Matrix.mul_assoc, hkk, Matrix.one_mul]
      rw [mul_assoc, inv_mul_cancel₀ hc0, mul_one]
    rw [e1]; exact smul_mem_intMat v hui ((intMat v).mul_mem hk₀ hcXi)
  have hk'k'i : k' * k'i = 1 := by
    rw [hk', hk'i, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    calc H * tM v * (tMi v * Hi) = H * (tM v * tMi v) * Hi := by noncomm_ring
      _ = 1 := by rw [tM_mul_tMi, mul_one, hHHi]
  have hk'ik' : k'i * k' = 1 := by
    rw [hk', hk'i, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hp0, one_smul]
    calc tMi v * Hi * (H * tM v) = tMi v * (Hi * H) * tM v := by noncomm_ring
      _ = 1 := by rw [hHiH, mul_one, tMi_mul_tM]
  have hHeq : H = k' * tbM v := by
    rw [hk', Matrix.smul_mul, Matrix.mul_assoc, tM_mul_tbM, Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hp0, one_smul]
  have hHieq : Hi = tbMi v * k'i := by
    rw [hk'i, Matrix.mul_smul, ← Matrix.mul_assoc, tbMi_mul_tMi, Matrix.smul_mul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ hp0, one_smul]
  refine ⟨fun w hw => ⟨hw1 w, hw2 w hw⟩, k', k'i, hk'int, hk'iint, hk'k'i, hk'ik', hHeq, hHieq, ?_⟩

  by_contra hne1
  have hlt : Valued.v (k' 1 1) < 1 := lt_of_le_of_ne (valued_le_one_of_mem v (hk'int 1 1)) hne1
  set Y := tMi v * H with hY
  set Yi := Hi * tM v with hYi
  have hYint : Y ∈ intMat v := by
    rw [hY, hHeq, ← Matrix.mul_assoc]; exact (tMi_mul_mul_tbM_mem_iff v hk'int).2 hlt
  have hYYi : Y * Yi = 1 := by
    calc Y * Yi = tMi v * (H * Hi) * tM v := by simp only [hY, hYi]; noncomm_ring
      _ = 1 := by rw [hHHi, mul_one, tMi_mul_tM]
  have hYiY : Yi * Y = 1 := by
    calc Yi * Y = Hi * (tM v * tMi v) * H := by simp only [hY, hYi]; noncomm_ring
      _ = 1 := by rw [tM_mul_tMi, mul_one, hHiH]
  have hYiint : Yi ∈ intMat v := by
    refine inv_mem_intMat_of_valued_det v hYint hYYi hYiY ?_
    rw [hY, Matrix.det_mul, det_tMi, map_mul, map_inv₀, hm, valued_pr, ← WithZero.exp_neg,
      ← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1
  apply hne
  ext z
  rw [mem_conj_iff, mem_conj_iff, mem_box_iff hRo, mem_box_iff hRo]
  refine forall_congr' fun w => ?_
  rw [map_mul, map_mul, map_mul, map_mul, ev_tmul_one]
  by_cases hw : w = v
  · obtain rfl : v = w := (‹w = v›).symm
    rw [hφR, hφR, map_mul, map_mul, map_mul, map_mul, ← hH, ← hHi, hn, hni]
    have e1 : Hi * φ (z ⊗ₜ[ℚ] (1 : 𝕂)) * H = Yi * (tMi v * φ (z ⊗ₜ[ℚ] (1 : 𝕂)) * tM v) * Y := by
      calc Hi * φ (z ⊗ₜ[ℚ] (1 : 𝕂)) * H
          = Hi * (tM v * tMi v) * φ (z ⊗ₜ[ℚ] (1 : 𝕂)) * (tM v * tMi v) * H := by
            rw [tM_mul_tMi, mul_one, mul_one]
        _ = _ := by simp only [hY, hYi]; noncomm_ring
    have e2 : k₀i * tMi v * φ (z ⊗ₜ[ℚ] (1 : 𝕂)) * (tM v * k₀) =
        k₀i * (tMi v * φ (z ⊗ₜ[ℚ] (1 : 𝕂)) * tM v) * k₀ := by noncomm_ring
    rw [e1, e2, conj_mem_intMat_iff v hYint hYiint hYYi hYiY, conj_mem_intMat_iff v hk₀ hk₀i hkk hkk']
  · rw [units_conj_mem_localBox_iff hRo w (hw1 w) (hw2 w hw) (ev_units_mul_inv w h) (ev_units_inv_mul w h),
      units_conj_mem_localBox_iff hRo w (hnw w hw).1 (hnw w hw).2 (ev_units_mul_inv w n)
        (ev_units_inv_mul w n)]

include hRo hφ1 hφR hk₀ hk₀i hkk hkk' hn hni hnw in

theorem mem_uHeckeSet_of_shape {h : (𝔹)ˣ}
    (hw : ∀ w, w ≠ v → ev w (h : 𝔹) ∈ Submodule.localBox R w ∧
      ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w)
    {k' k'i : M₂} (hk'int : k' ∈ intMat v) (hk'iint : k'i ∈ intMat v) (hk'k'i : k' * k'i = 1)
    (hk'ik' : k'i * k' = 1) (hHeq : φ (ev v (h : 𝔹)) = k' * tbM v)
    (hHieq : φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) = tbMi v * k'i) (hunit : Valued.v (k' 1 1) = 1) :
    h ∈ uHeckeSet R n (pr v) := by
  have hp0 := pr_ne_zero' v
  have hS := isOrder_meetOrder R hRo n
  have hSR : ∀ w, Submodule.localBox (meetOrder R n) w ≤ Submodule.localBox R w :=
    fun w => localBox_mono w inf_le_left
  have hle := localBox_le_meetOrder_of_ne R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw
  have hmemv := fun {Y : ℍv} (h1 : φ Y ∈ intMat v) (h2 : tMi v * φ Y * tM v ∈ intMat v) =>
    mem_localBox_meetOrder_of R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw h1 h2
  have hdetk' : Valued.v k'.det = 1 := valued_det_eq_one v hk'int hk'iint hk'k'i
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    rw [mem_box_iff hS]
    intro w
    by_cases hw' : w = v
    · obtain rfl : v = w := (‹w = v›).symm
      refine hmemv (by rw [hHeq]; exact (intMat v).mul_mem hk'int (tbM_mem v)) ?_
      rw [hHeq, Matrix.mul_assoc, Matrix.mul_assoc, tbM_mul_tM, Matrix.mul_smul, Matrix.mul_one,
        Matrix.mul_smul, ← Matrix.smul_mul, smul_tMi]
      exact (intMat v).mul_mem (tbM_mem v) hk'int
    · exact hle w hw' (hw w hw').1
  ·
    rw [mem_box_iff hS]
    intro w
    rw [ev_ratCast_smul, map_natCast]
    by_cases hw' : w = v
    · obtain rfl : v = w := (‹w = v›).symm
      have e : φ (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ϖ) * ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) = tM v * k'i := by
        rw [map_one_tmul_mul v φ hφ1, hHieq, ← Matrix.smul_mul, smul_tbMi]
      refine hmemv (by rw [e]; exact (intMat v).mul_mem (tM_mem v) hk'iint) ?_
      rw [e, ← Matrix.mul_assoc, tMi_mul_tM, Matrix.one_mul]
      exact (intMat v).mul_mem hk'iint (tM_mem v)
    · exact hle w hw' (one_tmul_mul_mem_localBox R w (hw w hw').2 (natCast_mem_integers w _))
  ·
    intro H
    have h1 : tbMi v * k'i ∈ intMat v := by rw [← hHieq]; exact (hφR _).1 (hSR v ((mem_box_iff hS _).1 H v))
    have h2 := valued_le_one_of_mem v (det_mem_integers v h1)
    rw [Matrix.det_mul, det_tbMi, map_mul, map_inv₀, valued_pr,
      valued_det_eq_one v hk'iint hk'int hk'ik', mul_one, ← WithZero.exp_neg, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h2
    norm_num at h2
  ·
    intro H
    have h1 := (hφR _).1 (hSR v ((mem_box_iff hS _).1 H v))
    rw [ev_ratCast_smul, map_inv₀, map_natCast, map_one_tmul_mul v φ hφ1, hHeq] at h1
    have h2 := valued_le_one_of_mem v (det_mem_integers v h1)
    rw [Matrix.det_smul, Fintype.card_fin, Matrix.det_mul, det_tbM, map_mul, map_mul, map_pow, map_inv₀,
      valued_pr, hdetk', one_mul, ← WithZero.exp_neg, ← WithZero.exp_nsmul, ← WithZero.exp_add,
      ← WithZero.exp_zero, WithZero.exp_le_exp] at h2
    norm_num at h2
  ·
    rw [conj_conj_eq hRo n h]
    ext z
    rw [mem_conj_iff, mem_box_iff hRo, mem_iff_tmul_one_mem_box hRo z, mem_box_iff hRo]
    refine forall_congr' fun w => ?_
    rw [map_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, map_mul, map_mul]
    by_cases hw' : w = v
    · obtain rfl : v = w := (‹w = v›).symm
      rw [hφR, hφR, map_mul, map_mul, map_mul, map_mul, hn, hni, hHeq, hHieq]
      have e : k₀i * tMi v * (tbMi v * k'i) * φ (ev v (z ⊗ₜ[ℚ] (1 : 𝔸f))) * (k' * tbM v * (tM v * k₀)) =
          (k₀i * k'i) * φ (ev v (z ⊗ₜ[ℚ] (1 : 𝔸f))) * (k' * k₀) := by
        calc _ = k₀i * (tMi v * tbMi v) * k'i * φ (ev v (z ⊗ₜ[ℚ] (1 : 𝔸f))) * k' * (tbM v * tM v) * k₀ := by
              noncomm_ring
          _ = (ϖ⁻¹ * ϖ) • ((k₀i * k'i) * φ (ev v (z ⊗ₜ[ℚ] (1 : 𝔸f))) * (k' * k₀)) := by
            rw [tMi_mul_tbMi, tbM_mul_tM]
            simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_smul]
            rw [mul_comm (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))
              (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))⁻¹]
            congr 1
            noncomm_ring
          _ = _ := by rw [inv_mul_cancel₀ hp0, one_smul]
      rw [e]
      have hA : k' * k₀ * (k₀i * k'i) = 1 := by
        calc k' * k₀ * (k₀i * k'i) = k' * (k₀ * k₀i) * k'i := by noncomm_ring
          _ = 1 := by rw [hkk, mul_one, hk'k'i]
      have hB : k₀i * k'i * (k' * k₀) = 1 := by
        calc k₀i * k'i * (k' * k₀) = k₀i * (k'i * k') * k₀ := by noncomm_ring
          _ = 1 := by rw [hk'ik', mul_one, hkk']
      exact conj_mem_intMat_iff v ((intMat v).mul_mem hk'int hk₀) ((intMat v).mul_mem hk₀i hk'iint) hA hB
    · have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ R → y ∈ R → x * y ∈ R := fun x y hx hy => hRo.mul_mem hx hy
      have hu : ev w (h : 𝔹) * ev w (n : 𝔹) ∈ Submodule.localBox R w :=
        mul_mem_localBox R w hmul (hw w hw').1 (hnw w hw').1
      have hui : ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) * ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w :=
        mul_mem_localBox R w hmul (hnw w hw').2 (hw w hw').2
      have hA : ev w (h : 𝔹) * ev w (n : 𝔹) * (ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) * ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹)) = 1 := by
        calc ev w (h : 𝔹) * ev w (n : 𝔹) * (ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) * ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹))
            = ev w (h : 𝔹) * (ev w (n : 𝔹) * ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹)) * ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) := by
              noncomm_ring
          _ = 1 := by rw [ev_units_mul_inv, mul_one, ev_units_mul_inv]
      have hB : ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) * ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) * (ev w (h : 𝔹) * ev w (n : 𝔹)) = 1 := by
        calc ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) * ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) * (ev w (h : 𝔹) * ev w (n : 𝔹))
            = ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) * (ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) * ev w (h : 𝔹)) * ev w (n : 𝔹) := by
              noncomm_ring
          _ = 1 := by rw [ev_units_inv_mul, mul_one, ev_units_inv_mul]
      have := units_conj_mem_localBox_iff hRo w hu hui (y := ev w (z ⊗ₜ[ℚ] (1 : 𝔸f))) hA hB
      rw [show ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) * ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) * ev w (z ⊗ₜ[ℚ] (1 : 𝔸f)) *
          (ev w (h : 𝔹) * ev w (n : 𝔹)) = ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) * ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) *
          ev w (z ⊗ₜ[ℚ] (1 : 𝔸f)) * (ev w (h : 𝔹) * ev w (n : 𝔹)) from rfl]
      exact this
  ·
    intro heq
    set H := φ (ev v (h : 𝔹)) with hH
    set Hi := φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) with hHi
    have hHHi : H * Hi = 1 := by rw [hH, hHi, ← map_mul, ev_units_mul_inv, map_one]
    have hHiH : Hi * H = 1 := by rw [hH, hHi, ← map_mul, ev_units_inv_mul, map_one]
    have hloc : ∀ W : M₂, Hi * W * H ∈ intMat v ↔ tMi v * W * tM v ∈ intMat v := by
      intro W
      obtain ⟨x, hxv, hxw⟩ := exists_adele_at hRo v (φ.symm W)
      have key := conj_mem_box_iff_of_conj_eq hRo heq x
      rw [mem_box_iff hRo, mem_box_iff hRo] at key
      have e1 : ∀ g : (𝔹)ˣ, (∀ w, ev w (((g⁻¹ : (𝔹)ˣ) : 𝔹) * x * (g : 𝔹)) ∈ Submodule.localBox R w) ↔
          ev v (((g⁻¹ : (𝔹)ˣ) : 𝔹) * x * (g : 𝔹)) ∈ Submodule.localBox R v := fun g =>
        ⟨fun H' => H' v, fun H' w => by
          by_cases hw' : w = v
          · obtain rfl : v = w := (‹w = v›).symm; exact H'
          · rw [map_mul, map_mul, hxw w hw', mul_zero, zero_mul]; exact zero_mem _⟩
      rw [e1, e1, hφR, hφR] at key
      simp only [map_mul] at key
      rw [hxv, RingEquiv.apply_symm_apply, ← hH, ← hHi, hn, hni] at key
      rw [key]
      have e2 : k₀i * tMi v * W * (tM v * k₀) = k₀i * (tMi v * W * tM v) * k₀ := by noncomm_ring
      rw [e2, conj_mem_intMat_iff v hk₀ hk₀i hkk hkk']
    set X := tMi v * H with hX
    set Xi := Hi * tM v with hXi
    have hXXi : X * Xi = 1 := by
      calc X * Xi = tMi v * (H * Hi) * tM v := by simp only [hX, hXi]; noncomm_ring
        _ = 1 := by rw [hHHi, mul_one, tMi_mul_tM]
    have hX' : ∀ W ∈ intMat v, X * W * Xi ∈ intMat v := fun W hW => by
      have := (hloc (H * W * Hi)).1 (by
        have e : Hi * (H * W * Hi) * H = (Hi * H) * W * (Hi * H) := by noncomm_ring
        rwa [e, hHiH, one_mul, mul_one])
      have e : tMi v * (H * W * Hi) * tM v = X * W * Xi := by simp only [hX, hXi]; noncomm_ring
      rwa [e] at this
    obtain ⟨c, hc0, hcX, hcXi⟩ := exists_scalar_of_conj_intMat v hXXi hX'
    have hdetX : Valued.v X.det = Valued.v c ^ 2 := valued_det_eq_sq v hc0 hXXi hcX hcXi
    rw [hX, hHeq, Matrix.det_mul, Matrix.det_mul, det_tMi, det_tbM, map_mul, map_mul, map_inv₀, hdetk',
      one_mul, inv_mul_cancel₀ (by rw [valued_pr]; exact WithZero.coe_ne_zero)] at hdetX
    have hc1 : Valued.v c = 1 := by
      obtain ⟨e, he⟩ : ∃ e : ℤ, Valued.v c = WithZero.exp e :=
        ⟨WithZero.log _, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hc0)).symm⟩
      rw [he, ← WithZero.exp_nsmul, ← WithZero.exp_zero, WithZero.exp_inj] at hdetX
      rw [he, ← WithZero.exp_zero]
      congr 1
      simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat] at hdetX
      omega
    have hXint : X ∈ intMat v := by
      have : X = c • (c⁻¹ • X) := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      rw [this]
      exact smul_mem_intMat v (mem_integers_of_valued_le_one v hc1.le) hcX
    rw [hX, hHeq, ← Matrix.mul_assoc, tMi_mul_mul_tbM_mem_iff v hk'int, hunit] at hXint
    exact lt_irrefl _ hXint

omit φ n in
theorem tbMi_mul_tbM : tbMi v * tbM v = 1 := by
  have hp0 := pr_ne_zero' v
  ext i j; fin_cases i <;> fin_cases j <;> simp [tbMi, tbM, Matrix.mul_apply, Fin.sum_univ_two, hp0]

omit φ n in

theorem tbMi_mul_mul_tbM (Z : M₂) : tbMi v * Z * tbM v = !![Z 0 0, ϖ⁻¹ * Z 0 1; ϖ * Z 1 0, Z 1 1] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  have hp := pr_ne_zero' v
  fin_cases i <;> fin_cases j <;> simp [tbM, tbMi] <;> field_simp

omit φ n in

theorem det_tMi_mul_mul_tM (X : M₂) : (tMi v * X * tM v).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, det_tMi, det_tM, mul_assoc, mul_comm X.det, ← mul_assoc,
    inv_mul_cancel₀ (pr_ne_zero' v), one_mul]

omit φ n in

theorem mul_tbMi (H : M₂) : H * tbMi v = !![ϖ⁻¹ * H 0 0, H 0 1; ϖ⁻¹ * H 1 0, H 1 1] := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [tbMi] <;> ring

omit φ n in

theorem exists_isIw_conj_notMem {k' k'i : M₂} (hk' : k' ∈ intMat v) (hk'i : k'i ∈ intMat v)
    (h1 : k' * k'i = 1) (h2 : k'i * k' = 1) (hunit : Valued.v (k' 1 1) = 1) :
    ∃ Y : M₂, Y ∈ intMat v ∧ tMi v * Y * tM v ∈ intMat v ∧ tbMi v * (k'i * Y * k') * tbM v ∉ intMat v := by
  have hp0 := pr_ne_zero' v
  have hne : k' 1 1 ≠ 0 := by intro h; rw [h, map_zero] at hunit; exact zero_ne_one hunit
  have hk11i : (k' 1 1)⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v hunit

  have hrow : ¬ (ϖ⁻¹ * k'i 0 0 ∈ 𝓞v ∧ ϖ⁻¹ * k'i 0 1 ∈ 𝓞v) := by
    rintro ⟨ha, hb⟩
    have hdet : Valued.v k'i.det = 1 := valued_det_eq_one v hk'i hk' h2
    have hmem : ϖ⁻¹ * k'i.det ∈ 𝓞v := by
      rw [Matrix.det_fin_two, mul_sub, ← mul_assoc, ← mul_assoc]
      exact sub_mem (mul_mem ha (hk'i 1 1)) (mul_mem hb (hk'i 1 0))
    rw [pr_inv_mul_mem_integers_iff v (det_mem_integers v hk'i), hdet] at hmem
    exact lt_irrefl _ hmem
  by_cases h00 : ϖ⁻¹ * k'i 0 0 ∈ 𝓞v
  ·
    refine ⟨!![0, 0; 0, 1], ?_, ?_, ?_⟩
    · intro i j; fin_cases i <;> fin_cases j <;> simp
    · rw [tMi_mul_mul_tM]; intro i j; fin_cases i <;> fin_cases j <;> simp
    · intro hmem
      have h01 := hmem 0 1
      have e : (tbMi v * (k'i * !![(0 : 𝕂), 0; 0, 1] * k') * tbM v) 0 1 = ϖ⁻¹ * (k'i 0 1 * k' 1 1) := by
        rw [tbMi_mul_mul_tbM]; simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [e] at h01
      apply hrow
      refine ⟨h00, ?_⟩
      have e2 : ϖ⁻¹ * k'i 0 1 = ϖ⁻¹ * (k'i 0 1 * k' 1 1) * (k' 1 1)⁻¹ := by field_simp
      rw [e2]
      exact mul_mem h01 hk11i
  ·
    refine ⟨!![0, 1; 0, 0], ?_, ?_, ?_⟩
    · intro i j; fin_cases i <;> fin_cases j <;> simp
    · rw [tMi_mul_mul_tM]; intro i j; fin_cases i <;> fin_cases j <;> simp [pr_mem_integers]
    · intro hmem
      have h01 := hmem 0 1
      have e : (tbMi v * (k'i * !![(0 : 𝕂), 1; 0, 0] * k') * tbM v) 0 1 = ϖ⁻¹ * (k'i 0 0 * k' 1 1) := by
        rw [tbMi_mul_mul_tbM]; simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [e] at h01
      apply h00
      have e2 : ϖ⁻¹ * k'i 0 0 = ϖ⁻¹ * (k'i 0 0 * k' 1 1) * (k' 1 1)⁻¹ := by field_simp
      rw [e2]
      exact mul_mem h01 hk11i

include hRo in
omit φ in

theorem mem_localBox_conj_iff_ev (x : ℍv) :
    x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v ↔
      ev v ((n⁻¹ : (𝔹)ˣ) : 𝔹) * x * ev v (n : 𝔹) ∈ Submodule.localBox R v := by
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff (D := ℍ[ℚ, a, b]) R hRo.fg hRo.spanTop n v x]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [← mul_assoc, ← mul_assoc, ev_units_inv_mul, one_mul, mul_assoc, ev_units_inv_mul, mul_one]; exact hy
  · intro h
    exact ⟨_, h, by rw [← mul_assoc, ← mul_assoc, ev_units_mul_inv, one_mul, mul_assoc, ev_units_mul_inv, mul_one]⟩

include hRo hφ1 hφR hk₀ hk₀i hkk hkk' hn hni hnw in

theorem isIw_of_mem_localBox_meetOrder {x : ℍv} (hx : x ∈ Submodule.localBox (meetOrder R n) v) :
    φ x ∈ intMat v ∧ tMi v * φ x * tM v ∈ intMat v := by
  have hxR : x ∈ Submodule.localBox R v := localBox_mono v inf_le_left hx
  have hxC : x ∈ Submodule.localBox (Submodule.conjByFiniteIdele R n) v :=
    localBox_mono v (inf_le_right : meetOrder R n ≤ _) hx
  refine ⟨(hφR _).1 hxR, ?_⟩
  rw [mem_localBox_conj_iff_ev R hRo v n, hφR, map_mul, map_mul, hn, hni] at hxC
  have e : k₀i * tMi v * φ x * (tM v * k₀) = k₀i * (tMi v * φ x * tM v) * k₀ := by noncomm_ring
  rw [e, conj_mem_intMat_iff v hk₀ hk₀i hkk hkk'] at hxC
  exact hxC

omit φ n in
theorem one_tmul_mul_comm (c : 𝕂) (x : ℍv) : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x = x * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | tmul y d => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm]
  | add y z hy hz => rw [mul_add, add_mul, hy, hz]

include hRo hφ1 in

theorem forall_localBox_meetOrder_of_forall {Hl Hr : ℍv}
    (hgen : ∀ z ∈ meetOrder R n, φ (Hl * (z ⊗ₜ[ℚ] (1 : 𝕂)) * Hr) ∈ intMat v) :
    ∀ x ∈ Submodule.localBox (meetOrder R n) v, φ (Hl * x * Hr) ∈ intMat v := by
  intro x hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c, hc, rfl⟩ := hy
    have e : z ⊗ₜ[ℚ] c = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * (z ⊗ₜ[ℚ] (1 : 𝕂)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    have e2 : Hl * (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * (z ⊗ₜ[ℚ] (1 : 𝕂))) * Hr =
        ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * (Hl * (z ⊗ₜ[ℚ] (1 : 𝕂)) * Hr) := by
      rw [← mul_assoc Hl, ← one_tmul_mul_comm v c Hl]; noncomm_ring
    rw [e, e2, map_one_tmul_mul v φ hφ1]
    exact smul_mem_intMat v hc (hgen z hz)
  | zero => rw [mul_zero, zero_mul, map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add, add_mul, map_add]; exact add_mem hx hy
  | neg x _ hx =>
    have h1 := neg_mem hx
    rw [← map_neg] at h1
    have hA : Hl * -x = -(Hl * x) := mul_neg Hl x
    have hB : -(Hl * x) * Hr = -(Hl * x * Hr) := neg_mul (Hl * x) Hr
    have h2 : φ (Hl * -x * Hr) = φ (-(Hl * x * Hr)) := by rw [hA, hB]
    exact h2 ▸ h1

include hRo hφ1 hφR hk₀ hk₀i hkk hkk' hn hni hnw in

theorem mem_levelHeckeUSet_of_shape (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛo : IsOrder Λ) (hRΛ : R ≤ Λ)
    (hΛv : ∀ x, x ∈ Submodule.localBox Λ v ↔ φ x ∈ intMat v) {h : (𝔹)ˣ}
    (hw : ∀ w, w ≠ v → ev w (h : 𝔹) ∈ Submodule.localBox R w ∧
      ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w)
    {k' k'i : M₂} (hk'int : k' ∈ intMat v) (hk'iint : k'i ∈ intMat v) (hk'k'i : k' * k'i = 1)
    (hk'ik' : k'i * k' = 1) (hHeq : φ (ev v (h : 𝔹)) = k' * tbM v)
    (hHieq : φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) = tbMi v * k'i) (hunit : Valued.v (k' 1 1) = 1) :
    h ∈ levelHeckeUSet Λ (meetOrder R n) (pr v) := by
  have hU := mem_uHeckeSet_of_shape R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw hw hk'int hk'iint hk'k'i
    hk'ik' hHeq hHieq hunit
  obtain ⟨Y, hYint, hYiw, hbad⟩ := exists_isIw_conj_notMem v hk'int hk'iint hk'k'i hk'ik' hunit
  have hyS : φ.symm Y ∈ Submodule.localBox (meetOrder R n) v :=
    mem_localBox_meetOrder_of R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw
      (by rw [RingEquiv.apply_symm_apply]; exact hYint) (by rw [RingEquiv.apply_symm_apply]; exact hYiw)
  have key : φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹) * φ.symm Y * ev v (h : 𝔹)) = tbMi v * (k'i * Y * k') * tbM v := by
    rw [map_mul, map_mul, hHieq, hHeq, RingEquiv.apply_symm_apply]; noncomm_ring
  refine ⟨hU.1, ?_, ?_⟩
  ·
    intro hEq
    apply hbad
    rw [← key]
    refine forall_localBox_meetOrder_of_forall R hRo v φ hφ1 n (fun z hz => ?_) _ hyS
    have hzc : z ∈ Submodule.conjByFiniteIdele (meetOrder R n) h := by rw [hEq]; exact hz
    rw [mem_conj_iff, mem_box_iff (isOrder_meetOrder R hRo n)] at hzc
    have := hzc v
    rw [map_mul, map_mul, ev_tmul_one] at this
    exact (isIw_of_mem_localBox_meetOrder R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw this).1
  ·
    intro hle
    apply hbad
    rw [← key]
    refine forall_localBox_meetOrder_of_forall R hRo v φ hφ1 n (fun z hz => ?_) _ hyS
    have hzc : z ∈ Submodule.conjByFiniteIdele Λ h := hle hz
    rw [mem_conj_iff, mem_box_iff hΛo] at hzc
    have := hzc v
    rw [map_mul, map_mul, ev_tmul_one] at this
    exact (hΛv _).1 this

include hRo hφ1 hφR hk₀ hk₀i hkk hkk' hn hni hnw in

theorem shape_of_mem_levelHeckeUSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛo : IsOrder Λ) (hRΛ : R ≤ Λ)
    (hΛv : ∀ x, x ∈ Submodule.localBox Λ v ↔ φ x ∈ intMat v) {h : (𝔹)ˣ}
    (hh : h ∈ levelHeckeUSet Λ (meetOrder R n) (pr v)) :
    (∀ w, w ≠ v → ev w (h : 𝔹) ∈ Submodule.localBox R w ∧
      ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w) ∧
    ∃ k' k'i : M₂, k' ∈ intMat v ∧ k'i ∈ intMat v ∧ k' * k'i = 1 ∧ k'i * k' = 1 ∧
      φ (ev v (h : 𝔹)) = k' * tbM v ∧ φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) = tbMi v * k'i ∧
      Valued.v (k' 1 1) = 1 := by
  obtain ⟨⟨hh1, hh2, hh3, hh4⟩, hneS, hnle⟩ := hh
  have hp0 := pr_ne_zero' v
  have hS := isOrder_meetOrder R hRo n
  have hSR : Submodule.finiteAdeleBox (meetOrder R n) ≤ Submodule.finiteAdeleBox R := box_mono inf_le_left
  set H := φ (ev v (h : 𝔹)) with hH
  set Hi := φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) with hHi
  have hHHi : H * Hi = 1 := by rw [hH, hHi, ← map_mul, ev_units_mul_inv, map_one]
  have hHiH : Hi * H = 1 := by rw [hH, hHi, ← map_mul, ev_units_inv_mul, map_one]

  have hv1 : ev v (h : 𝔹) ∈ Submodule.localBox (meetOrder R n) v := (mem_box_iff hS _).1 hh1 v
  have hw1 : ∀ w, ev w (h : 𝔹) ∈ Submodule.localBox R w := (mem_box_iff hRo _).1 (hSR hh1)
  have hv2' : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((pr v : ℕ) : 𝕂)) * ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈
      Submodule.localBox (meetOrder R n) v := by
    have := (mem_box_iff hS _).1 hh2 v
    rwa [ev_ratCast_smul, map_natCast] at this
  have hw2' : ∀ w, ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((pr v : ℕ) : w.adicCompletion ℚ)) *
      ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := by
    intro w
    have := (mem_box_iff hRo _).1 (hSR hh2) w
    rwa [ev_ratCast_smul, map_natCast] at this
  have hw2 : ∀ w, w ≠ v → ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := fun w hw => by
    have := one_tmul_mul_mem_localBox R w (hw2' w) (natCast_inv_mem_integers w (pr_notMem_asIdeal_of_ne v w hw))
    rwa [one_tmul_natCast_inv_mul_cancel v w hw] at this
  obtain ⟨hHint, hHiw⟩ := isIw_of_mem_localBox_meetOrder R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw hv1
  have hpHi' := isIw_of_mem_localBox_meetOrder R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw hv2'
  rw [map_one_tmul_mul v φ hφ1, ← hHi] at hpHi'
  obtain ⟨hpHi, hpHiiw⟩ := hpHi'
  have htt : tM v * tMi v = 1 := tM_mul_tMi v
  have htt' : tMi v * tM v = 1 := tMi_mul_tM v

  obtain ⟨m, hm2, hm0, hm⟩ := valued_det_bounds v hHHi hHint hpHi
  have hm_ne0 : m ≠ 0 := by
    rintro rfl
    have hdet1 : Valued.v H.det = 1 := by rw [hm, WithZero.exp_zero]
    have hHiint : Hi ∈ intMat v := inv_mem_intMat_of_valued_det v hHint hHHi hHiH hdet1
    have hHiiw : tMi v * Hi * tM v ∈ intMat v := by
      refine inv_mem_intMat_of_valued_det v hHiw (Mi := tMi v * Hi * tM v) ?_ ?_ ?_
      · calc tMi v * H * tM v * (tMi v * Hi * tM v) = tMi v * H * (tM v * tMi v) * Hi * tM v := by noncomm_ring
          _ = 1 := by rw [htt, mul_one, mul_assoc (tMi v), hHHi, mul_one, htt']
      · calc tMi v * Hi * tM v * (tMi v * H * tM v) = tMi v * Hi * (tM v * tMi v) * H * tM v := by noncomm_ring
          _ = 1 := by rw [htt, mul_one, mul_assoc (tMi v), hHiH, mul_one, htt']
      · rw [det_tMi_mul_mul_tM]; exact hdet1
    apply hh3
    rw [mem_box_iff hS]
    intro w
    by_cases hw : w = v
    · obtain rfl : v = w := (‹w = v›).symm
      exact mem_localBox_meetOrder_of R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw hHiint hHiiw
    · exact localBox_le_meetOrder_of_ne R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw w hw (hw2 w hw)
  have hm_ne2 : m ≠ -2 := by
    rintro rfl
    have hinv1 : (ϖ • Hi) * (ϖ⁻¹ • H) = 1 := by
      rw [smul_mul_smul_comm, mul_inv_cancel₀ hp0, one_smul, hHiH]
    have hinv2 : (ϖ⁻¹ • H) * (ϖ • Hi) = 1 := by
      rw [smul_mul_smul_comm, inv_mul_cancel₀ hp0, one_smul, hHHi]
    have hdetp : Valued.v (ϖ • Hi).det = 1 := by
      have hdd := det_mul_det_eq_one v hHHi
      have h1 : Valued.v H.det * Valued.v Hi.det = 1 := by rw [← map_mul, hdd, map_one]
      rw [hm] at h1
      have hHidet : Valued.v Hi.det = WithZero.exp 2 := by
        have e : Valued.v Hi.det = (WithZero.exp (-2 : ℤ))⁻¹ * (WithZero.exp (-2 : ℤ) * Valued.v Hi.det) := by
          rw [← mul_assoc, inv_mul_cancel₀ WithZero.coe_ne_zero, one_mul]
        rw [e, h1, mul_one, ← WithZero.exp_neg]; norm_num
      rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, valued_pr, hHidet, ← WithZero.exp_nsmul,
        ← WithZero.exp_add]; norm_num
    have hpHint : ϖ⁻¹ • H ∈ intMat v := inv_mem_intMat_of_valued_det v hpHi hinv1 hinv2 hdetp
    have hpHiw : tMi v * (ϖ⁻¹ • H) * tM v ∈ intMat v := by
      refine inv_mem_intMat_of_valued_det v hpHiiw (Mi := tMi v * (ϖ⁻¹ • H) * tM v) ?_ ?_ ?_
      · calc tMi v * (ϖ • Hi) * tM v * (tMi v * (ϖ⁻¹ • H) * tM v)
            = tMi v * (ϖ • Hi) * (tM v * tMi v) * (ϖ⁻¹ • H) * tM v := by noncomm_ring
          _ = 1 := by rw [htt, mul_one, mul_assoc (tMi v), hinv1, mul_one, htt']
      · calc tMi v * (ϖ⁻¹ • H) * tM v * (tMi v * (ϖ • Hi) * tM v)
            = tMi v * (ϖ⁻¹ • H) * (tM v * tMi v) * (ϖ • Hi) * tM v := by noncomm_ring
          _ = 1 := by rw [htt, mul_one, mul_assoc (tMi v), hinv2, mul_one, htt']
      · rw [det_tMi_mul_mul_tM]; exact hdetp
    apply hh4
    rw [mem_box_iff hS]
    intro w
    rw [ev_ratCast_smul, map_inv₀, map_natCast]
    by_cases hw : w = v
    · obtain rfl : v = w := (‹w = v›).symm
      refine mem_localBox_meetOrder_of R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw ?_ ?_
      · rw [map_one_tmul_mul v φ hφ1]; exact hpHint
      · rw [map_one_tmul_mul v φ hφ1]; exact hpHiw
    · exact localBox_le_meetOrder_of_ne R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw w hw
        (one_tmul_mul_mem_localBox R w (hw1 w) (natCast_inv_mem_integers w (pr_notMem_asIdeal_of_ne v w hw)))
  have hm1 : m = -1 := by omega
  subst hm1

  have h10 : Valued.v (H 1 0) < 1 := (tMi_mul_mul_tM_mem_iff v hHint).1 hHiw
  have h11 : Valued.v (H 1 1) = 1 := by
    by_contra hne1
    have hlt : Valued.v (H 1 1) < 1 := lt_of_le_of_ne (valued_le_one_of_mem v (hHint 1 1)) hne1
    set g := tMi v * H with hg
    set gi := Hi * tM v with hgi
    have eg : g = !![H 0 0, H 0 1; ϖ⁻¹ * H 1 0, ϖ⁻¹ * H 1 1] := by
      rw [hg]; ext i j; fin_cases i <;> fin_cases j <;> simp [tMi, Matrix.mul_apply, Fin.sum_univ_two]
    have hgint : g ∈ intMat v := by
      rw [eg]
      intro i j
      fin_cases i <;> fin_cases j
      · exact hHint 0 0
      · exact hHint 0 1
      · exact (pr_inv_mul_mem_integers_iff v (hHint 1 0)).2 h10
      · exact (pr_inv_mul_mem_integers_iff v (hHint 1 1)).2 hlt
    have hggi : g * gi = 1 := by
      calc g * gi = tMi v * (H * Hi) * tM v := by simp only [hg, hgi]; noncomm_ring
        _ = 1 := by rw [hHHi, mul_one, htt']
    have hgig : gi * g = 1 := by
      calc gi * g = Hi * (tM v * tMi v) * H := by simp only [hg, hgi]; noncomm_ring
        _ = 1 := by rw [htt, mul_one, hHiH]
    have hgdet : Valued.v g.det = 1 := by
      rw [hg, Matrix.det_mul, det_tMi, map_mul, hm, map_inv₀, valued_pr, ← WithZero.exp_neg, ← WithZero.exp_add]
      norm_num
    have hgiint : gi ∈ intMat v := inv_mem_intMat_of_valued_det v hgint hggi hgig hgdet
    apply hnle
    intro z hz
    rw [mem_conj_iff, mem_box_iff hΛo]
    intro w
    rw [map_mul, map_mul, ev_tmul_one]
    by_cases hw : w = v
    · obtain rfl : v = w := (‹w = v›).symm
      rw [hΛv, map_mul, map_mul, ← hH, ← hHi]
      have hzS : z ⊗ₜ[ℚ] (1 : 𝕂) ∈ Submodule.localBox (meetOrder R n) v := tmul_one_mem_localBox _ v hz
      obtain ⟨-, hZiw⟩ := isIw_of_mem_localBox_meetOrder R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw hzS
      have e : Hi * φ (z ⊗ₜ[ℚ] (1 : 𝕂)) * H = gi * (tMi v * φ (z ⊗ₜ[ℚ] (1 : 𝕂)) * tM v) * g := by
        calc Hi * φ (z ⊗ₜ[ℚ] (1 : 𝕂)) * H = Hi * (tM v * tMi v) * φ (z ⊗ₜ[ℚ] (1 : 𝕂)) * (tM v * tMi v) * H := by
              rw [htt, mul_one, mul_one]
          _ = _ := by simp only [hg, hgi]; noncomm_ring
      rw [e]
      exact conj_mem_intMat v hgint hgiint hZiw
    · have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ → y ∈ Λ → x * y ∈ Λ := fun x y hx hy => hΛo.mul_mem hx hy
      have hzΛ : z ∈ Λ := hRΛ ((inf_le_left : meetOrder R n ≤ R) hz)
      exact mul_mem_localBox Λ w hmul
        (mul_mem_localBox Λ w hmul (localBox_mono w hRΛ (hw2 w hw)) (tmul_one_mem_localBox Λ w hzΛ))
        (localBox_mono w hRΛ (hw1 w))

  have h00 : Valued.v (H 0 0) < 1 := by
    have hdet : H 0 0 * H 1 1 = H.det + H 0 1 * H 1 0 := by rw [Matrix.det_fin_two]; ring
    have hv : Valued.v (H 0 0 * H 1 1) < 1 := by
      rw [hdet]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
      · rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
      · rw [map_mul]
        calc Valued.v (H 0 1) * Valued.v (H 1 0) ≤ 1 * Valued.v (H 1 0) :=
              mul_le_mul_left (valued_le_one_of_mem v (hHint 0 1)) _
          _ = Valued.v (H 1 0) := one_mul _
          _ < 1 := h10
    rwa [map_mul, h11, mul_one] at hv

  set k' : M₂ := ϖ⁻¹ • (H * tM v) with hk'
  set k'i : M₂ := ϖ • (tMi v * Hi) with hk'i
  have hk'eq : k' = H * tbMi v := by
    rw [hk', ← Matrix.mul_smul, ← smul_tbMi, smul_smul, inv_mul_cancel₀ hp0, one_smul]
  have hk'int : k' ∈ intMat v := by
    rw [hk'eq, mul_tbMi]
    intro i j
    fin_cases i <;> fin_cases j
    · exact (pr_inv_mul_mem_integers_iff v (hHint 0 0)).2 h00
    · exact hHint 0 1
    · exact (pr_inv_mul_mem_integers_iff v (hHint 1 0)).2 h10
    · exact hHint 1 1
  have hk'k'i : k' * k'i = 1 := by
    rw [hk', hk'i, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul]
    calc H * tM v * (tMi v * Hi) = H * (tM v * tMi v) * Hi := by noncomm_ring
      _ = 1 := by rw [htt, mul_one, hHHi]
  have hk'ik' : k'i * k' = 1 := by
    rw [hk', hk'i, Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hp0, one_smul]
    calc tMi v * Hi * (H * tM v) = tMi v * (Hi * H) * tM v := by noncomm_ring
      _ = 1 := by rw [hHiH, mul_one, htt']
  have hk'det : Valued.v k'.det = 1 := by
    rw [hk'eq, Matrix.det_mul, det_tbMi, map_mul, hm, map_inv₀, valued_pr, ← WithZero.exp_neg, ← WithZero.exp_add]
    norm_num
  have hk'iint : k'i ∈ intMat v := inv_mem_intMat_of_valued_det v hk'int hk'k'i hk'ik' hk'det
  have hHeq : H = k' * tbM v := by
    rw [hk', Matrix.smul_mul, Matrix.mul_assoc, tM_mul_tbM, Matrix.mul_smul, Matrix.mul_one, smul_smul,
      inv_mul_cancel₀ hp0, one_smul]
  have hHieq : Hi = tbMi v * k'i := by
    rw [hk'i, Matrix.mul_smul, ← Matrix.mul_assoc, tbMi_mul_tMi, Matrix.smul_mul, Matrix.one_mul, smul_smul,
      mul_inv_cancel₀ hp0, one_smul]
  have h11' : k' 1 1 = H 1 1 := by rw [hk'eq, mul_tbMi]; simp
  exact ⟨fun w hw => ⟨hw1 w, hw2 w hw⟩, k', k'i, hk'int, hk'iint, hk'k'i, hk'ik', hHeq, hHieq, by rw [h11']; exact h11⟩

include hRo hφ1 hφR hk₀ hk₀i hkk hkk' hn hni hnw in

theorem uHeckeSet_eq_levelHeckeUSet (Λ : Submodule ℤ ℍ[ℚ, a, b]) (hΛo : IsOrder Λ) (hRΛ : R ≤ Λ)
    (hΛv : ∀ x, x ∈ Submodule.localBox Λ v ↔ φ x ∈ intMat v) :
    uHeckeSet R n (pr v) = levelHeckeUSet Λ (meetOrder R n) (pr v) := by
  ext h
  constructor
  · intro hh
    obtain ⟨hw, k', k'i, h1, h2, h3, h4, h5, h6, h7⟩ :=
      shape_of_mem_uHeckeSet R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw hh
    exact mem_levelHeckeUSet_of_shape R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw Λ hΛo hRΛ hΛv hw
      h1 h2 h3 h4 h5 h6 h7
  · intro hh
    obtain ⟨hw, k', k'i, h1, h2, h3, h4, h5, h6, h7⟩ :=
      shape_of_mem_levelHeckeUSet R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw Λ hΛo hRΛ hΛv hh
    exact mem_uHeckeSet_of_shape R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw hw h1 h2 h3 h4 h5 h6 h7

end Frame

section Assembly

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ

open QuaternionAlgebra CerednikDrinfeld

def pl (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

theorem pr_pl (q : ℕ) (hq : q.Prime) : pr (pl q hq) = q :=
  congrArg Subtype.val ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply ⟨q, hq⟩)

theorem bridge_at (v : HeightOneSpectrum (𝓞 ℚ)) {q' : ℕ} (hq' : q'.Prime) (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal) (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (hR : IsEichlerOrder R N)
    (hRΛ : R ≤ Λ) (hNv : (N : 𝓞 ℚ) ∉ v.asIdeal) (n : (𝔹)ˣ) (hnH : n ∈ primeHeckeSet R (pr v)) :
    uHeckeSet R n (pr v) = levelHeckeUSet Λ (meetOrder R n) (pr v) := by
  have hRo : IsOrder R := hR.isOrder
  obtain ⟨hnw, φ, hφ1, hφR', k₀, k₀i, hk₀, hk₀i, hkk, hkk', hn, hni⟩ :=
    QuaternionAlgebra.exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet hdef hR (pr v)
      (pr_prime v) v (pr_mem_asIdeal v) hq'v hNv n hnH
  have hφR : ∀ x, x ∈ Submodule.localBox R v ↔ φ x ∈ intMat v := hφR'
  have hqq' : pr v ≠ q' := by
    intro h; apply hq'v; rw [← h]; exact pr_mem_asIdeal v
  have hqN : ¬ pr v ∣ N := by rw [← natCast_mem_asIdeal_iff_pr_dvd]; exact hNv
  have hΛR : Submodule.localBox Λ v = Submodule.localBox R v :=
    QuaternionAlgebra.IsEichlerOrder.localBox_eq_localBox_of_isMaximalOrder_of_le_of_not_dvd hq' hdef hR (pr v) (pr_prime v) hqq' hqN v
      (pr_mem_asIdeal v) hΛ hRΛ
  have hΛv : ∀ x, x ∈ Submodule.localBox Λ v ↔ φ x ∈ intMat v := fun x => by rw [hΛR]; exact hφR x
  exact uHeckeSet_eq_levelHeckeUSet R hRo v φ hφ1 hφR n k₀ k₀i hk₀ hk₀i hkk hkk' hn hni hnw Λ hΛ.isOrder hRΛ hΛv

theorem bridge (q q' : ℕ) (hq : q.Prime) (hq' : q'.Prime) (hqq' : q ≠ q') (hdef : IsDefiniteRamifiedExactlyAt a b q')
    (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) {N : ℕ} (hR : IsEichlerOrder R N) (hRΛ : R ≤ Λ) (hqN : ¬ q ∣ N)
    (n : (𝔹)ˣ) (hnH : n ∈ primeHeckeSet R q) :
    uHeckeSet R n q = levelHeckeUSet Λ (meetOrder R n) q := by
  set v := pl q hq with hv
  have hpr : pr v = q := pr_pl q hq
  have hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [natCast_mem_asIdeal_iff_pr_dvd, hpr]
    intro h
    exact hqq' ((Nat.prime_dvd_prime_iff_eq hq hq').1 h)
  have hNv : (N : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [natCast_mem_asIdeal_iff_pr_dvd, hpr]; exact hqN
  have hnH' : n ∈ primeHeckeSet R (pr v) := by rw [hpr]; exact hnH
  have := bridge_at v hq' hdef hq'v Λ R hΛ hR hRΛ hNv n hnH'
  rw [hpr] at this
  exact this

end Assembly

end CosetDict
p2m_reactivate "P2MW.S_CerednikDrinfeld_uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet.CosetDict"

open QuaternionAlgebra CerednikDrinfeld in

theorem solution
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {M : ℕ} [NeZero M] (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (hΛ : IsMaximalOrder Λ) (hR : IsEichlerOrder R M) (hRΛ : R ≤ Λ)
    {s : ℕ} [Fact s.Prime] (hsq' : s ≠ q') (hsM : ¬ s ∣ M)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hn : n ∈ primeHeckeSet R s) :
    uHeckeSet R n s = levelHeckeUSet Λ (meetOrder R n) s :=
  CosetDict.bridge s q' Fact.out Fact.out hsq' hdef Λ R hΛ hR hRΛ hsM n hn

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet.CosetDict"

end S_CerednikDrinfeld_uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet
end P2MW
export P2MW.S_CerednikDrinfeld_uHeckeSet_eq_levelHeckeUSet_meetOrder_of_mem_primeHeckeSet (solution)
