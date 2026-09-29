-- Prove2me | solution 1 for CerednikDrinfeld.levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ad962bad-f577-5eda-b33d-40617763f853

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
import Theorems.Thm_QuaternionAlgebra_IsEichlerOrder_exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree
import Theorems.Thm_QuaternionAlgebra_exists_conjByFiniteIdele_eq_mem_finiteAdeleBox_smul_inv_mem_of_relIndex_eq
import Theorems.Thm_CerednikDrinfeld_mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree
p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "simp" "QuaternionAlgebra.baseChangeRight_tmul QuaternionAlgebra.mapOfAlgebraMapEq_apply QuaternionAlgebra.baseChange_tmul LocalGL2.swapUnit_val"

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

section Peirce

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def E10 : M₂ := !![0, 0; 1, 0]

def E11 : M₂ := !![0, 0; 0, 1]

theorem E10_mem : E10 v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E10, one_mem, zero_mem]
theorem E11_mem : E11 v ∈ intMat v := by
  intro i j; fin_cases i <;> fin_cases j <;> simp [E11, one_mem, zero_mem]

theorem eq_sum_smul_E (X : M₂) :
    X = (X 0 0) • E00 v + (X 0 1) • E01 v + (X 1 0) • E10 v + (X 1 1) • E11 v := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E00, E01, E10, E11]

theorem E00_mul_mul_E00 (X : M₂) : E00 v * X * E00 v = (X 0 0) • E00 v := by
  ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E00]
theorem E00_mul_mul_E11 (X : M₂) : E00 v * X * E11 v = (X 0 1) • E01 v := by
  ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E00, E01, E11]
theorem E11_mul_mul_E00 (X : M₂) : E11 v * X * E00 v = (X 1 0) • E10 v := by
  ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E00, E10, E11]
theorem E11_mul_mul_E11 (X : M₂) : E11 v * X * E11 v = (X 1 1) • E11 v := by
  ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [E11]
theorem E10_mul_E01 : E10 v * E01 v = E11 v := by
  ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [E01, E10, E11]
theorem E01_mul_E10 : E01 v * E10 v = E00 v := by
  ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [E00, E01, E10]
theorem smul_E_mul_smul_E {x y : 𝕂} (A B C : M₂) (h : A * B = C) : (x • A) * (y • B) = (x * y) • C := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h]

theorem iwahori_generators :
    (E00 v ∈ intMat v ∧ ϖ⁻¹ * (E00 v) 1 0 ∈ 𝓞v) ∧ (E01 v ∈ intMat v ∧ ϖ⁻¹ * (E01 v) 1 0 ∈ 𝓞v) ∧
    (E11 v ∈ intMat v ∧ ϖ⁻¹ * (E11 v) 1 0 ∈ 𝓞v) ∧ (ϖ • E10 v ∈ intMat v ∧ ϖ⁻¹ * (ϖ • E10 v) 1 0 ∈ 𝓞v) := by
  have hp0 := pr_ne_zero' v
  refine ⟨⟨E00_mem v, ?_⟩, ⟨E01_mem v, ?_⟩, ⟨E11_mem v, ?_⟩, ⟨smul_mem_intMat v (pr_mem_integers v) (E10_mem v), ?_⟩⟩ <;>
    simp [E00, E01, E10, E11, Matrix.smul_apply, zero_mem, inv_mul_cancel₀ hp0, one_mem]

theorem mem_integers_of_forall_pow {x : 𝕂} (k : ℕ) (h : ∀ n : ℕ, ϖ ^ k * x ^ n ∈ 𝓞v) : x ∈ 𝓞v := by
  by_contra hx
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hx
  have hx0 : x ≠ 0 := fun h0 => by rw [h0, map_zero] at hx; exact not_lt_zero hx
  obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
    ⟨WithZero.log (Valued.v x), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx0)).symm⟩
  have hm1 : 1 ≤ m := by
    rw [hm, ← WithZero.exp_zero, WithZero.exp_lt_exp] at hx; omega
  have := valued_le_one_of_mem v (h (k + 1))
  rw [map_mul, map_pow, map_pow, valued_pr, hm, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp] at this
  simp only [smul_eq_mul, nsmul_eq_mul] at this
  push_cast at this
  nlinarith

theorem exists_iwahori_mul_tbM_mul {Y : M₂} (hY : Y ∈ intMat v) (h00 : ϖ⁻¹ * Y 0 0 ∈ 𝓞v) (h10 : ϖ⁻¹ * Y 1 0 ∈ 𝓞v)
    (h11 : Valued.v (Y 1 1) = 1) (hdet : Valued.v Y.det = Valued.v ϖ) :
    ∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tbM v * ι' := by
  have hp0 := pr_ne_zero' v
  set α := ϖ⁻¹ * Y 0 0 with hα
  set γ := ϖ⁻¹ * Y 1 0 with hγ
  set β := Y 0 1 with hβ
  set δ := Y 1 1 with hδ
  have hδ0 : δ ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
  have hδi : δ⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v h11
  have hY00 : Y 0 0 = ϖ * α := by rw [hα, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  have hY10 : Y 1 0 = ϖ * γ := by rw [hγ, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  set α' := α - β * γ * δ⁻¹ with hα'
  have hα'O : α' ∈ 𝓞v := sub_mem h00 (mul_mem (mul_mem (hY 0 1) h10) hδi)
  have hdet' : Y.det = ϖ * (α' * δ) := by
    rw [Matrix.det_fin_two, hY00, hY10, hα']; field_simp; ring
  have hαδ : Valued.v (α' * δ) = 1 := by
    have := hdet; rw [hdet', map_mul] at this
    have hv0 : Valued.v ϖ ≠ 0 := by rw [valued_pr]; exact WithZero.coe_ne_zero
    calc Valued.v (α' * δ) = (Valued.v ϖ)⁻¹ * (Valued.v ϖ * Valued.v (α' * δ)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hv0, one_mul]
      _ = 1 := by rw [this, inv_mul_cancel₀ hv0]
  have hα'v : Valued.v α' = 1 := by
    rw [map_mul, h11, mul_one] at hαδ; exact hαδ
  have hα'0 : α' ≠ 0 := fun h0 => by rw [h0, map_zero] at hα'v; exact zero_ne_one hα'v
  have hα'i : α'⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v hα'v
  have hβO : β ∈ 𝓞v := hY 0 1
  have hδO : δ ∈ 𝓞v := hY 1 1
  have hx : ϖ * γ * δ⁻¹ ∈ 𝓞v := mul_mem (mul_mem (pr_mem_integers v) h10) hδi
  have hnx : -(ϖ * γ * δ⁻¹) ∈ 𝓞v := neg_mem hx
  have hy : -(β * α'⁻¹ * δ⁻¹) ∈ 𝓞v := neg_mem (mul_mem (mul_mem hβO hα'i) hδi)
  refine ⟨!![α', β; 0, δ], !![α'⁻¹, -(β * α'⁻¹ * δ⁻¹); 0, δ⁻¹], !![1, 0; ϖ * γ * δ⁻¹, 1], !![1, 0; -(ϖ * γ * δ⁻¹), 1],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hα'O, hβO, zero_mem, hδO]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hα'i, hδi, zero_mem, hy]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hx]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hnx]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · simp [zero_mem]
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ϖ⁻¹ * (ϖ * γ * δ⁻¹) = γ * δ⁻¹ by field_simp]
    exact mul_mem h10 hδi
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [tbM, hY00, hY10, hα'] <;> (try field_simp) <;> ring

theorem exists_iwahori_mul_tM_mul {Y : M₂} (hY : Y ∈ intMat v) (h10 : ϖ⁻¹ * Y 1 0 ∈ 𝓞v) (h11 : ϖ⁻¹ * Y 1 1 ∈ 𝓞v)
    (h00 : Valued.v (Y 0 0) = 1) (hdet : Valued.v Y.det = Valued.v ϖ) :
    ∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tM v * ι' := by
  have hp0 := pr_ne_zero' v
  set a := Y 0 0 with ha
  set b := Y 0 1 with hb
  set c := ϖ⁻¹ * Y 1 0 with hc
  set d := ϖ⁻¹ * Y 1 1 with hd
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, map_zero] at h00; exact zero_ne_one h00
  have hai : a⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v h00
  have hY10 : Y 1 0 = ϖ * c := by rw [hc, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  have hY11 : Y 1 1 = ϖ * d := by rw [hd, ← mul_assoc, mul_inv_cancel₀ hp0, one_mul]
  set d' := d - c * b * a⁻¹ with hd'
  have hd'O : d' ∈ 𝓞v := sub_mem h11 (mul_mem (mul_mem h10 (hY 0 1)) hai)
  have hdet' : Y.det = ϖ * (a * d') := by
    rw [Matrix.det_fin_two, hY10, hY11, hd']; field_simp; ring
  have had : Valued.v (a * d') = 1 := by
    have := hdet; rw [hdet', map_mul] at this
    have hv0 : Valued.v ϖ ≠ 0 := by rw [valued_pr]; exact WithZero.coe_ne_zero
    calc Valued.v (a * d') = (Valued.v ϖ)⁻¹ * (Valued.v ϖ * Valued.v (a * d')) := by
          rw [← mul_assoc, inv_mul_cancel₀ hv0, one_mul]
      _ = 1 := by rw [this, inv_mul_cancel₀ hv0]
  have hd'v : Valued.v d' = 1 := by rw [map_mul, h00, one_mul] at had; exact had
  have hd'0 : d' ≠ 0 := fun h0 => by rw [h0, map_zero] at hd'v; exact zero_ne_one hd'v
  have hd'i : d'⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v hd'v
  have haO : a ∈ 𝓞v := hY 0 0
  have hbO : b ∈ 𝓞v := hY 0 1
  have hx : ϖ * c * a⁻¹ ∈ 𝓞v := mul_mem (mul_mem (pr_mem_integers v) h10) hai
  have hnx : -(ϖ * c * a⁻¹) ∈ 𝓞v := neg_mem hx
  have hy : -(b * a⁻¹ * d'⁻¹) ∈ 𝓞v := neg_mem (mul_mem (mul_mem hbO hai) hd'i)
  refine ⟨!![1, 0; ϖ * c * a⁻¹, 1], !![1, 0; -(ϖ * c * a⁻¹), 1], !![a, b; 0, d'], !![a⁻¹, -(b * a⁻¹ * d'⁻¹); 0, d'⁻¹],
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hx]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [one_mem, zero_mem, hnx]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hd'O, hbO, zero_mem, haO]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hai, hd'i, zero_mem, hy]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> (try field_simp) <;> ring
  · simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [show ϖ⁻¹ * (ϖ * c * a⁻¹) = c * a⁻¹ by field_simp]
    exact mul_mem h10 hai
  · simp [zero_mem]
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [tM, hY10, hY11, hd'] <;> (try field_simp) <;> ring

end Peirce

section IwahoriHecke

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

def alM : M₂ := !![0, 1; ϖ, 0]
def alMi : M₂ := !![0, ϖ⁻¹; 1, 0]

theorem alM_mul_alMi : alM v * alMi v = 1 := by
  have hp0 := pr_ne_zero' v
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, alM, alMi, mul_inv_cancel₀ hp0]
theorem alMi_mul_alM : alMi v * alM v = 1 := by
  have hp0 := pr_ne_zero' v
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, alM, alMi, inv_mul_cancel₀ hp0]

theorem iwahori_iff {X : M₂} (hX : X ∈ intMat v) : tMi v * X * tM v ∈ intMat v ↔ ϖ⁻¹ * X 1 0 ∈ 𝓞v :=
  (tMi_mul_mul_tM_mem_iff v hX).trans (pr_inv_mul_mem_integers_iff v (hX 1 0)).symm

theorem valued_eq_one_or_pr_inv_mul_mem {x : 𝕂} (hx : x ∈ 𝓞v) : Valued.v x = 1 ∨ ϖ⁻¹ * x ∈ 𝓞v := by
  rcases (valued_le_one_of_mem v hx).lt_or_eq with h | h
  · exact Or.inr ((pr_inv_mul_mem_integers_iff v hx).2 h)
  · exact Or.inl h

theorem valued_diag_mul_lt_one {η : M₂} (hη : η ∈ intMat v) (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v)
    (hdet : Valued.v η.det = Valued.v ϖ) : Valued.v (η 0 0 * η 1 1) < 1 := by
  have hp0 := pr_ne_zero' v
  have e1 : η 0 0 * η 1 1 = η.det + η 0 1 * (ϖ * (ϖ⁻¹ * η 1 0)) := by
    rw [mul_inv_cancel_left₀ hp0, Matrix.det_fin_two]; ring
  rw [e1]
  refine lt_of_le_of_lt (Valued.v.map_add _ _) (max_lt ?_ ?_)
  · rw [hdet, valued_pr, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)
  · rw [map_mul, map_mul, valued_pr]
    calc Valued.v (η 0 1) * (WithZero.exp (-1) * Valued.v (ϖ⁻¹ * η 1 0))
        ≤ 1 * (WithZero.exp (-1) * 1) :=
          mul_le_mul' (valued_le_one_of_mem v (hη 0 1)) (mul_le_mul_right (valued_le_one_of_mem v h10) _)
      _ < 1 := by rw [one_mul, mul_one, ← WithZero.exp_zero]; exact WithZero.exp_lt_exp.2 (by norm_num)

theorem pr_inv_mul_apply_zero_zero_mem {η : M₂} (hη : η ∈ intMat v) (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v)
    (hdet : Valued.v η.det = Valued.v ϖ) (h11 : Valued.v (η 1 1) = 1) : ϖ⁻¹ * η 0 0 ∈ 𝓞v := by
  have h := valued_diag_mul_lt_one v hη h10 hdet
  rw [map_mul, h11, mul_one] at h
  exact (pr_inv_mul_mem_integers_iff v (hη 0 0)).2 h

theorem pr_inv_mul_apply_one_one_mem {η : M₂} (hη : η ∈ intMat v) (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v)
    (hdet : Valued.v η.det = Valued.v ϖ) (h00 : Valued.v (η 0 0) = 1) : ϖ⁻¹ * η 1 1 ∈ 𝓞v := by
  have h := valued_diag_mul_lt_one v hη h10 hdet
  rw [map_mul, h00, one_mul] at h
  exact (pr_inv_mul_mem_integers_iff v (hη 1 1)).2 h

theorem iwahori_mul_mul_mem {X Y Z : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v)
    (hY : Y ∈ intMat v) (hY' : tMi v * Y * tM v ∈ intMat v) (hZ : Z ∈ intMat v) (hZ' : tMi v * Z * tM v ∈ intMat v) :
    X * Y * Z ∈ intMat v ∧ tMi v * (X * Y * Z) * tM v ∈ intMat v := by
  refine ⟨(intMat v).mul_mem ((intMat v).mul_mem hX hY) hZ, ?_⟩
  have e : tMi v * (X * Y * Z) * tM v = (tMi v * X * tM v) * (tMi v * Y * tM v) * (tMi v * Z * tM v) := by
    calc tMi v * (X * Y * Z) * tM v = tMi v * X * (tM v * tMi v) * Y * (tM v * tMi v) * Z * tM v := by
          rw [tM_mul_tMi]; simp only [mul_one, Matrix.mul_assoc]
      _ = _ := by noncomm_ring
  rw [e]; exact (intMat v).mul_mem ((intMat v).mul_mem hX' hY') hZ'

theorem iwahori_inv_mem {κ κi : M₂} (h1 : κ * κi = 1) (h2 : κi * κ = 1) (hκ : κ ∈ intMat v)
    (hκ' : tMi v * κ * tM v ∈ intMat v) (hdet : Valued.v κ.det = 1) :
    κi ∈ intMat v ∧ tMi v * κi * tM v ∈ intMat v := by
  have hκiO : κi ∈ intMat v := inv_mem_intMat_of_valued_det v hκ h1 h2 hdet
  refine ⟨hκiO, (iwahori_iff v hκiO).2 ?_⟩
  rw [inv_apply_one_zero v h1 h2, mul_neg, ← mul_assoc, mul_comm ϖ⁻¹, mul_assoc]
  exact neg_mem (mul_mem (inv_mem_integers_of_valued_eq_one v hdet) ((iwahori_iff v hκ).1 hκ'))

theorem alMi_mul_mul_alM (X : M₂) : alMi v * X * alM v = !![X 1 1, ϖ⁻¹ * X 1 0; ϖ * X 0 1, X 0 0] := by
  have hp0 := pr_ne_zero' v
  ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [alM, alMi] <;> field_simp
theorem alM_mul_mul_alMi (X : M₂) : alM v * X * alMi v = !![X 1 1, ϖ⁻¹ * X 1 0; ϖ * X 0 1, X 0 0] := by
  have hp0 := pr_ne_zero' v
  ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;> simp [alM, alMi] <;> field_simp

theorem swap_mem_iwahori {X : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v) :
    (!![X 1 1, ϖ⁻¹ * X 1 0; ϖ * X 0 1, X 0 0] : M₂) ∈ intMat v ∧
      tMi v * (!![X 1 1, ϖ⁻¹ * X 1 0; ϖ * X 0 1, X 0 0] : M₂) * tM v ∈ intMat v := by
  have hp0 := pr_ne_zero' v
  have hX10 := (iwahori_iff v hX).1 hX'
  have hmem : (!![X 1 1, ϖ⁻¹ * X 1 0; ϖ * X 0 1, X 0 0] : M₂) ∈ intMat v := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [hX 1 1, hX10, hX 0 0, mul_mem (pr_mem_integers v) (hX 0 1)]
  refine ⟨hmem, (iwahori_iff v hmem).2 ?_⟩
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [inv_mul_cancel_left₀ hp0]; exact hX 0 1

theorem conj_mem_iwahori_of_normaliser_type {η ηi : M₂} (h1 : η * ηi = 1) (h2 : ηi * η = 1) (hη : η ∈ intMat v)
    (h10 : ϖ⁻¹ * η 1 0 ∈ 𝓞v) (hdet : Valued.v η.det = Valued.v ϖ)
    (h00 : ϖ⁻¹ * η 0 0 ∈ 𝓞v) (h11 : ϖ⁻¹ * η 1 1 ∈ 𝓞v) {X : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v) :
    (ηi * X * η ∈ intMat v ∧ tMi v * (ηi * X * η) * tM v ∈ intMat v) ∧
      (η * X * ηi ∈ intMat v ∧ tMi v * (η * X * ηi) * tM v ∈ intMat v) := by
  have hp0 := pr_ne_zero' v
  set κ : M₂ := alMi v * η with hκ
  set κi : M₂ := ηi * alM v with hκi
  have hηκ : η = alM v * κ := by rw [hκ, ← mul_assoc, alM_mul_alMi, one_mul]
  have hηiκ : ηi = κi * alMi v := by rw [hκi, mul_assoc, alM_mul_alMi, mul_one]
  have hκκi : κ * κi = 1 := by
    rw [hκ, hκi, show alMi v * η * (ηi * alM v) = alMi v * (η * ηi) * alM v by noncomm_ring, h1, mul_one, alMi_mul_alM]
  have hκiκ : κi * κ = 1 := by
    rw [hκ, hκi, show ηi * alM v * (alMi v * η) = ηi * (alM v * alMi v) * η by noncomm_ring, alM_mul_alMi, mul_one, h2]
  have eκ : κ = !![ϖ⁻¹ * η 1 0, ϖ⁻¹ * η 1 1; η 0 0, η 0 1] := by
    rw [hκ]; ext i j; simp only [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> simp [alMi]
  have hκO : κ ∈ intMat v := by
    rw [eκ]; intro i j; fin_cases i <;> fin_cases j <;> simp [h10, h11, hη 0 0, hη 0 1]
  have hκ10 : κ 1 0 = η 0 0 := by rw [eκ]; simp
  have hκ' : tMi v * κ * tM v ∈ intMat v := by rw [iwahori_iff v hκO, hκ10]; exact h00
  have hκdet : Valued.v κ.det = 1 := by
    have : κ.det = -(ϖ⁻¹ * η.det) := by
      rw [eκ, Matrix.det_fin_two, Matrix.det_fin_two]; simp; ring
    rw [this, Valuation.map_neg, map_mul, map_inv₀, hdet, inv_mul_cancel₀]
    rw [valued_pr]; exact WithZero.coe_ne_zero
  obtain ⟨hκiO, hκi'⟩ := iwahori_inv_mem v hκκi hκiκ hκO hκ' hκdet
  constructor
  · rw [hηκ, hηiκ]
    have e : κi * alMi v * X * (alM v * κ) = κi * (alMi v * X * alM v) * κ := by noncomm_ring
    rw [e, alMi_mul_mul_alM]
    obtain ⟨hw, hw'⟩ := swap_mem_iwahori v hX hX'
    exact iwahori_mul_mul_mem v hκiO hκi' hw hw' hκO hκ'
  · rw [hηκ, hηiκ]
    have e : alM v * κ * X * (κi * alMi v) = alM v * (κ * X * κi) * alMi v := by noncomm_ring
    rw [e, alM_mul_mul_alMi]
    obtain ⟨hw, hw'⟩ := iwahori_mul_mul_mem v hκO hκ' hX hX' hκiO hκi'
    exact swap_mem_iwahori v hw hw'

theorem conj_mem_intMat_of_tM_type {ι ιi ι' ι'i : M₂} (hι : ι ∈ intMat v) (hιi : ιi ∈ intMat v)
    (hι' : ι' ∈ intMat v) (hι'i : ι'i ∈ intMat v) (h1 : ι * ιi = 1) (h2 : ιi * ι = 1)
    (hιΓ : tMi v * ι * tM v ∈ intMat v) (hιdet : Valued.v ι.det = 1)
    {X : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v) :
    (ι'i * tMi v * ιi) * X * (ι * tM v * ι') ∈ intMat v := by
  obtain ⟨-, hιiΓ⟩ := iwahori_inv_mem v h1 h2 hι hιΓ hιdet
  have hin : ιi * X * ι ∈ intMat v ∧ tMi v * (ιi * X * ι) * tM v ∈ intMat v :=
    iwahori_mul_mul_mem v hιi hιiΓ hX hX' hι hιΓ
  have e : (ι'i * tMi v * ιi) * X * (ι * tM v * ι') = ι'i * (tMi v * (ιi * X * ι) * tM v) * ι' := by noncomm_ring
  rw [e]; exact (intMat v).mul_mem ((intMat v).mul_mem hι'i hin.2) hι'

theorem conj_mem_intMat_of_tbM_type {ι ιi ι' ι'i : M₂} (hι : ι ∈ intMat v) (hιi : ιi ∈ intMat v)
    (hι' : ι' ∈ intMat v) (hι'i : ι'i ∈ intMat v) (h1 : ι * ιi = 1) (h2 : ιi * ι = 1) (h1' : ι' * ι'i = 1)
    (h2' : ι'i * ι' = 1)
    (hιΓ : tMi v * ι * tM v ∈ intMat v) (hιdet : Valued.v ι.det = 1)
    (hι'Γ : tMi v * ι' * tM v ∈ intMat v) (hι'det : Valued.v ι'.det = 1)
    {X : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v) :
    tMi v * ((ι'i * tbMi v * ιi) * X * (ι * tbM v * ι')) * tM v ∈ intMat v := by
  have hp0 := pr_ne_zero' v
  obtain ⟨-, hιiΓ⟩ := iwahori_inv_mem v h1 h2 hι hιΓ hιdet
  obtain ⟨hι'iO, hι'iΓ⟩ := iwahori_inv_mem v h1' h2' hι' hι'Γ hι'det
  have hin := iwahori_mul_mul_mem v hιi hιiΓ hX hX' hι hιΓ
  have key : tbMi v * (ιi * X * ι) * tbM v = tM v * (ιi * X * ι) * tMi v := by
    rw [show tbM v = ϖ • tMi v from (smul_tMi v).symm]
    have : tbMi v = ϖ⁻¹ • tM v := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [tbMi, tM, inv_mul_cancel₀ hp0]
    rw [this, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul]
  have e : tMi v * ((ι'i * tbMi v * ιi) * X * (ι * tbM v * ι')) * tM v =
      (tMi v * ι'i * tM v) * (tMi v * (tbMi v * (ιi * X * ι) * tbM v) * tM v) * (tMi v * ι' * tM v) := by
    calc tMi v * ((ι'i * tbMi v * ιi) * X * (ι * tbM v * ι')) * tM v
        = tMi v * ι'i * (tM v * tMi v) * (tbMi v * (ιi * X * ι) * tbM v) * (tM v * tMi v) * ι' * tM v := by
          rw [tM_mul_tMi]; simp only [mul_one, Matrix.mul_assoc]
      _ = _ := by noncomm_ring
  rw [e, key, show tMi v * (tM v * (ιi * X * ι) * tMi v) * tM v = (tMi v * tM v) * (ιi * X * ι) * (tMi v * tM v) by
    noncomm_ring, tMi_mul_tM, one_mul, mul_one]
  exact (intMat v).mul_mem ((intMat v).mul_mem hι'iΓ hin.1) hι'Γ

end IwahoriHecke

end LevelULocal
p2m_reactivate "P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.LevelULocal"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.LevelULocal"

end LevelULocalBlock
p2m_reactivate "P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.LevelULocal"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Quaternion Pointwise
open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LevelULocal

section ULocal

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)
local notation "ϖ" => (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v))

theorem tbM_mul_tbMi : tbM v * tbMi v = 1 := by
  have hp0 := pr_ne_zero' v
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, tbM, tbMi, mul_inv_cancel₀ hp0]
theorem tbMi_mul_tbM : tbMi v * tbM v = 1 := by
  have hp0 := pr_ne_zero' v
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, tbM, tbMi, inv_mul_cancel₀ hp0]

theorem diagonal_eq_tM : Matrix.diagonal ![(1 : 𝕂), ϖ ^ 1] = tM v := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tM, Matrix.diagonal]

theorem one_mem_iwahori : (1 : M₂) ∈ intMat v ∧ tMi v * 1 * tM v ∈ intMat v := by
  refine ⟨(intMat v).one_mem, ?_⟩
  rw [mul_one, tMi_mul_tM]; exact (intMat v).one_mem

theorem iwahori_mul_mem {X Y : M₂} (hX : X ∈ intMat v) (hX' : tMi v * X * tM v ∈ intMat v)
    (hY : Y ∈ intMat v) (hY' : tMi v * Y * tM v ∈ intMat v) :
    X * Y ∈ intMat v ∧ tMi v * (X * Y) * tM v ∈ intMat v := by
  have h := iwahori_mul_mul_mem v hX hX' hY hY' (one_mem_iwahori v).1 (one_mem_iwahori v).2
  simpa only [mul_one] using h

theorem valued_det_eq_valued_pr {Y Yi : M₂} (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : Y ∈ intMat v) (hY' : tMi v * Y * tM v ∈ intMat v)
    (hpYi : ϖ • Yi ∈ intMat v) (hpYi' : tMi v * (ϖ • Yi) * tM v ∈ intMat v)
    (hYi : ¬ (Yi ∈ intMat v ∧ tMi v * Yi * tM v ∈ intMat v))
    (hpY : ¬ (ϖ⁻¹ • Y ∈ intMat v ∧ tMi v * (ϖ⁻¹ • Y) * tM v ∈ intMat v)) :
    Valued.v Y.det = Valued.v ϖ := by
  have hp0 := pr_ne_zero' v
  obtain ⟨m, hm2, hm0, hm⟩ := valued_det_bounds v h1 hY hpYi
  have hvp : Valued.v ϖ = WithZero.exp (-1) := valued_pr v
  have hYidet : Valued.v Yi.det = (Valued.v Y.det)⁻¹ := by
    have h' : Valued.v Y.det * Valued.v Yi.det = 1 := by rw [← map_mul, det_mul_det_eq_one v h1, map_one]
    exact eq_inv_of_mul_eq_one_right h'
  obtain rfl | rfl | rfl : m = -2 ∨ m = -1 ∨ m = 0 := by omega
  · exfalso
    apply hpY
    have hZ1 : (ϖ • Yi) * (ϖ⁻¹ • Y) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hp0, one_smul, h2]
    have hZ2 : (ϖ⁻¹ • Y) * (ϖ • Yi) = 1 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hp0, one_smul, h1]
    have hdetZ : Valued.v (ϖ • Yi).det = 1 := by
      rw [Matrix.det_smul, Fintype.card_fin, map_mul, map_pow, hvp, hYidet, hm, ← WithZero.exp_nsmul,
        ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero]
      congr 1
    exact iwahori_inv_mem v hZ1 hZ2 hpYi hpYi' hdetZ
  · rw [hm, hvp]
  · exfalso
    apply hYi
    have hdet1 : Valued.v Y.det = 1 := by rw [hm, WithZero.exp_zero]
    exact iwahori_inv_mem v h1 h2 hY hY' hdet1

theorem exists_tbM_type {Y Yi : M₂} (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : Y ∈ intMat v) (hY' : tMi v * Y * tM v ∈ intMat v)
    (hpYi : ϖ • Yi ∈ intMat v) (hpYi' : tMi v * (ϖ • Yi) * tM v ∈ intMat v)
    (hYi : ¬ (Yi ∈ intMat v ∧ tMi v * Yi * tM v ∈ intMat v))
    (hpY : ¬ (ϖ⁻¹ • Y ∈ intMat v ∧ tMi v * (ϖ⁻¹ • Y) * tM v ∈ intMat v))
    (hnn : ¬ ∀ X : M₂, X ∈ intMat v → tMi v * X * tM v ∈ intMat v →
        (Yi * X * Y ∈ intMat v ∧ tMi v * (Yi * X * Y) * tM v ∈ intMat v) ∧
        (Y * X * Yi ∈ intMat v ∧ tMi v * (Y * X * Yi) * tM v ∈ intMat v))
    (hnt : ¬ ∀ X : M₂, X ∈ intMat v → tMi v * X * tM v ∈ intMat v → Yi * X * Y ∈ intMat v) :
    ∃ ι ιi ι' ι'i : M₂, ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      ϖ⁻¹ * ι 1 0 ∈ 𝓞v ∧ ϖ⁻¹ * ι' 1 0 ∈ 𝓞v ∧ Y = ι * tbM v * ι' := by
  have hdet := valued_det_eq_valued_pr v h1 h2 hY hY' hpYi hpYi' hYi hpY
  have h10 : ϖ⁻¹ * Y 1 0 ∈ 𝓞v := (iwahori_iff v hY).1 hY'
  rcases valued_eq_one_or_pr_inv_mul_mem v (hY 1 1) with h11 | h11
  · exact exists_iwahori_mul_tbM_mul v hY (pr_inv_mul_apply_zero_zero_mem v hY h10 hdet h11) h10 h11 hdet
  · exfalso
    rcases valued_eq_one_or_pr_inv_mul_mem v (hY 0 0) with h00 | h00
    · obtain ⟨ι, ιi, ι', ι'i, hι, hιi, hι', hι'i, e1, e2, e1', e2', hι10, hι'10, hYeq⟩ :=
        exists_iwahori_mul_tM_mul v hY h10 h11 h00 hdet
      apply hnt
      intro X hX hX'
      have hW : Y * (ι'i * tMi v * ιi) = 1 := by
        rw [hYeq]
        calc ι * tM v * ι' * (ι'i * tMi v * ιi) = ι * (tM v * (ι' * ι'i) * tMi v) * ιi := by noncomm_ring
          _ = 1 := by rw [e1', mul_one, tM_mul_tMi, mul_one, e1]
      have hYi_eq : Yi = ι'i * tMi v * ιi := by
        calc Yi = Yi * (Y * (ι'i * tMi v * ιi)) := by rw [hW, mul_one]
          _ = (Yi * Y) * (ι'i * tMi v * ιi) := (mul_assoc _ _ _).symm
          _ = ι'i * tMi v * ιi := by rw [h2, one_mul]
      rw [hYi_eq, hYeq]
      exact conj_mem_intMat_of_tM_type v hι hιi hι' hι'i e1 e2 ((iwahori_iff v hι).2 hι10)
        (valued_det_eq_one v hι hιi e1) hX hX'
    · apply hnn
      intro X hX hX'
      exact conj_mem_iwahori_of_normaliser_type v h1 h2 hY h10 hdet h00 h11 hX hX'

end ULocal
p2m_reactivate "P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.LevelULocal"

end LevelULocal
p2m_reactivate "P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.LevelULocal"

namespace LevelULocal

section UFrame

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

open QuaternionAlgebra CerednikDrinfeld

theorem conjφ_mul (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (k ki : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) (hkki : k * ki = 1)
    (x y : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) :
    (ki * φ x * k) * (ki * φ y * k) = ki * φ (x * y) * k := by
  rw [map_mul]
  calc (ki * φ x * k) * (ki * φ y * k) = ki * (φ x * (k * ki) * φ y) * k := by noncomm_ring
    _ = ki * (φ x * φ y) * k := by rw [hkki, mul_one]

theorem conjφ_mul3 (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (k ki : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) (hkki : k * ki = 1)
    (x y z : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) :
    ki * φ (x * y * z) * k = (ki * φ x * k) * (ki * φ y * k) * (ki * φ z * k) := by
  rw [conjφ_mul v φ k ki hkki, conjφ_mul v φ k ki hkki]

theorem conjφ_sandwich (v : HeightOneSpectrum (𝓞 ℚ))
    (k ki A : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) (hkik : ki * k = 1) :
    ki * (k * A * ki) * k = A := by
  calc ki * (k * A * ki) * k = (ki * k) * A * (ki * k) := by noncomm_ring
    _ = A := by rw [hkik, one_mul, mul_one]

theorem φ_one_tmul_mul (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (hφ : ∀ r : HeightOneSpectrum.adicCompletion ℚ v,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] r) = r • (1 : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)))
    (c : HeightOneSpectrum.adicCompletion ℚ v) (y : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) :
    φ (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * y) = c • φ y := by
  rw [map_mul, hφ, smul_mul_assoc, one_mul]

theorem one_tmul_inv_mul_cancel (w : HeightOneSpectrum (𝓞 ℚ)) {c : HeightOneSpectrum.adicCompletion ℚ w} (hc : c ≠ 0)
    (y : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ w) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c⁻¹) * (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * y) = y := by
  rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hc, ← Algebra.TensorProduct.one_def,
    one_mul]

theorem ev_one_mem_localBox {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) (w : HeightOneSpectrum (𝓞 ℚ)) :
    ev w (1 : 𝔹) ∈ Submodule.localBox R w := by
  rw [map_one, Algebra.TensorProduct.one_def]; exact tmul_one_mem_localBox R w hRo.one_mem

theorem localBox_inf_conj_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛo : IsOrder Λ) (m : (𝔹)ˣ) (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (hΛφ : ∀ x, x ∈ Submodule.localBox Λ v ↔ φ x ∈ intMat v)
    (k ki k₂ k₂i : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (hk : k ∈ intMat v) (hki : ki ∈ intMat v) (hk₂ : k₂ ∈ intMat v) (hk₂i : k₂i ∈ intMat v)
    (hkki : k * ki = 1) (hkik : ki * k = 1) (hk₂ki : k₂ * k₂i = 1) (hk₂ik : k₂i * k₂ = 1)
    (hm : φ (ev v (m : 𝔹)) = k * tM v * k₂) (x : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v) :
    x ∈ Submodule.localBox (Λ ⊓ Submodule.conjByFiniteIdele Λ m) v ↔
      ki * φ x * k ∈ intMat v ∧ tMi v * (ki * φ x * k) * tM v ∈ intMat v := by
  have hc : IsOrder (Submodule.conjByFiniteIdele Λ m) := QuaternionAlgebra.IsOrder.conjByFiniteIdele Λ hΛo m

  have hP1 : (k * tM v * k₂) * (k₂i * tMi v * ki) = 1 := by
    calc (k * tM v * k₂) * (k₂i * tMi v * ki) = k * (tM v * (k₂ * k₂i) * tMi v) * ki := by noncomm_ring
      _ = 1 := by rw [hk₂ki, mul_one, tM_mul_tMi, mul_one, hkki]
  have hmi : φ (ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹)) = k₂i * tMi v * ki := by
    have hQ : φ (ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹)) * φ (ev v (m : 𝔹)) = 1 := by
      rw [← map_mul, ev_units_inv_mul, map_one]
    rw [hm] at hQ
    calc φ (ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹)) = φ (ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹)) * ((k * tM v * k₂) * (k₂i * tMi v * ki)) := by
          rw [hP1, mul_one]
      _ = (φ (ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹)) * (k * tM v * k₂)) * (k₂i * tMi v * ki) := (mul_assoc _ _ _).symm
      _ = k₂i * tMi v * ki := by rw [hQ, one_mul]
  rw [Submodule.localBox_inf Λ (Submodule.conjByFiniteIdele Λ m) hΛo.fg hΛo.spanTop hc.fg hc.spanTop v,
    AddSubgroup.mem_inf, hΛφ, Submodule.mem_localBox_conjByFiniteIdele_iff Λ hΛo.fg hΛo.spanTop m v x]
  constructor
  · rintro ⟨hxΛ, y, hy, hxy⟩
    refine ⟨conj_mem_intMat v hk hki hxΛ, ?_⟩
    rw [hΛφ] at hy
    have e : tMi v * (ki * φ x * k) * tM v = k₂ * φ y * k₂i := by
      rw [hxy, map_mul, map_mul, hm, hmi]
      calc tMi v * (ki * (k * tM v * k₂ * φ y * (k₂i * tMi v * ki)) * k) * tM v
          = (tMi v * ((ki * k) * tM v)) * k₂ * φ y * k₂i * (tMi v * ((ki * k) * tM v)) := by noncomm_ring
        _ = k₂ * φ y * k₂i := by rw [hkik, one_mul, tMi_mul_tM, one_mul, mul_one]
    rw [e]; exact conj_mem_intMat v hk₂i hk₂ hy
  · rintro ⟨H1, H2⟩
    refine ⟨(conj_mem_intMat_iff v hk hki hkki hkik).1 H1, ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹) * x * ev v (m : 𝔹), ?_, ?_⟩
    · rw [hΛφ, map_mul, map_mul, hm, hmi]
      have e : k₂i * tMi v * ki * φ x * (k * tM v * k₂) = k₂i * (tMi v * (ki * φ x * k) * tM v) * k₂ := by noncomm_ring
      rw [e]; exact conj_mem_intMat v hk₂ hk₂i H2
    · calc x = (ev v (m : 𝔹) * ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹)) * x * (ev v (m : 𝔹) * ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹)) := by
            rw [ev_units_mul_inv, one_mul, mul_one]
        _ = ev v (m : 𝔹) * (ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹) * x * ev v (m : 𝔹)) * ev v ((m⁻¹ : (𝔹)ˣ) : 𝔹) := by noncomm_ring

theorem conj_eq_of_local {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (k ki : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) (hkki : k * ki = 1)
    (hRΨ : ∀ x, x ∈ Submodule.localBox R v ↔ ki * φ x * k ∈ intMat v ∧ tMi v * (ki * φ x * k) * tM v ∈ intMat v)
    (h : (𝔹)ˣ)
    (hoff : ∀ w, w ≠ v → ev w (h : 𝔹) ∈ Submodule.localBox R w ∧ ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w)
    (Y Yi : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (hY : ki * φ (ev v (h : 𝔹)) * k = Y) (hYi : ki * φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) * k = Yi)
    (h1 : Y * Yi = 1)
    (hloc : ∀ X, X ∈ intMat v → tMi v * X * tM v ∈ intMat v →
      (Yi * X * Y ∈ intMat v ∧ tMi v * (Yi * X * Y) * tM v ∈ intMat v) ∧
      (Y * X * Yi ∈ intMat v ∧ tMi v * (Y * X * Yi) * tM v ∈ intMat v)) :
    Submodule.conjByFiniteIdele R h = R := by
  have hu1 : ∀ w, ev w (h : 𝔹) * ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) = 1 := fun w => ev_units_mul_inv w h
  have hu2 : ∀ w, ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) * ev w (h : 𝔹) = 1 := fun w => ev_units_inv_mul w h
  ext z
  rw [mem_conj_iff, mem_iff_tmul_one_mem_box hRo z, mem_box_iff hRo, mem_box_iff hRo]
  constructor
  · intro H w
    by_cases hw : w = v
    · rw [hw]
      have Hw := H v
      rw [map_mul, map_mul, hRΨ, conjφ_mul3 v φ k ki hkki, hY, hYi] at Hw
      rw [hRΨ]
      have key := (hloc _ Hw.1 Hw.2).2
      have e : Y * (Yi * (ki * φ (ev v (z ⊗ₜ[ℚ] (1 : 𝔸f))) * k) * Y) * Yi = ki * φ (ev v (z ⊗ₜ[ℚ] (1 : 𝔸f))) * k := by
        calc _ = (Y * Yi) * (ki * φ (ev v (z ⊗ₜ[ℚ] (1 : 𝔸f))) * k) * (Y * Yi) := by noncomm_ring
          _ = _ := by rw [h1, one_mul, mul_one]
      rw [e] at key
      exact key
    · have Hw := H w
      rw [map_mul, map_mul] at Hw
      exact (units_conj_mem_localBox_iff hRo w (hoff w hw).1 (hoff w hw).2 (hu1 w) (hu2 w)).1 Hw
  · intro H w
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · rw [hw]
      have Hw := H v
      rw [hRΨ] at Hw
      rw [hRΨ, conjφ_mul3 v φ k ki hkki, hY, hYi]
      exact (hloc _ Hw.1 Hw.2).1
    · exact (units_conj_mem_localBox_iff hRo w (hoff w hw).1 (hoff w hw).2 (hu1 w) (hu2 w)).2 (H w)

theorem le_conj_of_local {R Λ : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R) (hΛo : IsOrder Λ) (hRΛ : R ≤ Λ)
    (v : HeightOneSpectrum (𝓞 ℚ))
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v ≃+* Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (k ki : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) (hkki : k * ki = 1)
    (hΛΨ : ∀ x, x ∈ Submodule.localBox Λ v ↔ ki * φ x * k ∈ intMat v)
    (hRΨ : ∀ x, x ∈ Submodule.localBox R v ↔ ki * φ x * k ∈ intMat v ∧ tMi v * (ki * φ x * k) * tM v ∈ intMat v)
    (h : (𝔹)ˣ)
    (hoff : ∀ w, w ≠ v → ev w (h : 𝔹) ∈ Submodule.localBox R w ∧ ev w ((h⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w)
    (Y Yi : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v))
    (hY : ki * φ (ev v (h : 𝔹)) * k = Y) (hYi : ki * φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) * k = Yi)
    (hloc : ∀ X, X ∈ intMat v → tMi v * X * tM v ∈ intMat v → Yi * X * Y ∈ intMat v) :
    R ≤ Submodule.conjByFiniteIdele Λ h := by
  intro z hz
  rw [mem_conj_iff, mem_box_iff hΛo]
  intro w
  rw [map_mul, map_mul]
  have hzw : ∀ w', ev w' (z ⊗ₜ[ℚ] (1 : 𝔸f)) ∈ Submodule.localBox R w' := fun w' => by
    rw [ev_tmul_one]; exact tmul_one_mem_localBox R w' hz
  by_cases hw : w = v
  · rw [hw, hΛΨ, conjφ_mul3 v φ k ki hkki, hY, hYi]
    exact hloc _ ((hRΨ _).1 (hzw v)).1 ((hRΨ _).1 (hzw v)).2
  · have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ → y ∈ Λ → x * y ∈ Λ := fun x y hx hy => hΛo.mul_mem hx hy
    exact mul_mem_localBox Λ w hmul (mul_mem_localBox Λ w hmul (localBox_mono w hRΛ (hoff w hw).2)
      (localBox_mono w hRΛ (hzw w))) (localBox_mono w hRΛ (hoff w hw).1)

end UFrame
p2m_reactivate "P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.LevelULocal"

section UInv

variable (v : HeightOneSpectrum (𝓞 ℚ))
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)

theorem inv_eq_of_eq_mul_tbM_mul {Y Yi ι ιi ι' ι'i : M₂} (h2 : Yi * Y = 1) (e1 : ι * ιi = 1) (e1' : ι' * ι'i = 1)
    (hY : Y = ι * tbM v * ι') : Yi = ι'i * tbMi v * ιi := by
  have hW : Y * (ι'i * tbMi v * ιi) = 1 := by
    rw [hY]
    calc ι * tbM v * ι' * (ι'i * tbMi v * ιi) = ι * (tbM v * (ι' * ι'i) * tbMi v) * ιi := by noncomm_ring
      _ = 1 := by rw [e1', mul_one, tbM_mul_tbMi, mul_one, e1]
  calc Yi = Yi * (Y * (ι'i * tbMi v * ιi)) := by rw [hW, mul_one]
    _ = (Yi * Y) * (ι'i * tbMi v * ιi) := (mul_assoc _ _ _).symm
    _ = ι'i * tbMi v * ιi := by rw [h2, one_mul]

end UInv
p2m_reactivate "P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.LevelULocal"

end LevelULocal
p2m_reactivate "P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.LevelULocal"

namespace LevelULocal

section UMain

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

open QuaternionAlgebra CerednikDrinfeld

theorem exists_mem_finiteIdeleStabilizer_eq_mul_mul_of_mem_levelHeckeUSet
    {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {R Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} [NeZero N] (hN : Squarefree N)
    (hR : IsEichlerOrder R N) (hΛ : IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    (hq'N : ¬ q' ∣ N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N)
    {h g : (𝔹)ˣ} (hh : h ∈ levelHeckeUSet Λ R ℓ) (hg : g ∈ levelHeckeUSet Λ R ℓ) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer R, ∃ u' ∈ Submodule.finiteIdeleStabilizer R, h = u * g * u' := by
  have hRo : IsOrder R := hR.isOrder
  have hΛo : IsOrder Λ := hΛ.isOrder
  have hℓ : ℓ.Prime := Fact.out
  have hmulR : ∀ x y : ℍ[ℚ, a, b], x ∈ R → y ∈ R → x * y ∈ R := fun x y hx hy => hRo.mul_mem hx hy

  obtain ⟨v, hv⟩ : ∃ v : HeightOneSpectrum (𝓞 ℚ), ((ℓ : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
    refine ⟨(Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, hℓ⟩, ?_⟩
    have e : pr ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, hℓ⟩) = ℓ := by
      simp [pr]
    have := pr_mem_asIdeal ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨ℓ, hℓ⟩)
    rwa [e] at this
  have hpr : pr v = ℓ :=
    (Nat.prime_dvd_prime_iff_eq (pr_prime v) hℓ).1 ((natCast_mem_asIdeal_iff_pr_dvd v ℓ).1 hv)
  subst hpr
  have hp0 := pr_ne_zero' v

  obtain ⟨Λ₂, hΛ₂, hRinf, hidx⟩ :=
    QuaternionAlgebra.IsEichlerOrder.exists_isMaximalOrder_eq_inf_relIndex_eq_of_squarefree hdef hN Λ R hΛ hR hRΛ
  have hidx' : (Λ ⊓ Λ₂).toAddSubgroup.relIndex Λ.toAddSubgroup = N := by rw [← hRinf]; exact hidx
  obtain ⟨m, hmΛ₂, hm1, hmN⟩ :=
    QuaternionAlgebra.exists_conjByFiniteIdele_eq_mem_finiteAdeleBox_smul_inv_mem_of_relIndex_eq q' hdef Λ Λ₂ hΛ hΛ₂ N hq'N hidx'
  have hRm : R = Λ ⊓ Submodule.conjByFiniteIdele Λ m := by rw [hmΛ₂]; exact hRinf
  have hidx'' : (Λ ⊓ Submodule.conjByFiniteIdele Λ m).toAddSubgroup.relIndex Λ.toAddSubgroup = N := by
    rw [hmΛ₂]; exact hidx'
  have hab : a ≠ 0 ∧ b ≠ 0 := ⟨hdef.neg_left.ne, hdef.neg_right.ne⟩
  obtain ⟨-, hfr⟩ := QuaternionAlgebra.IsMaximalOrder.localBoxUnits_and_exists_eq_mul_diagonal_mul_of_relIndex_inf_conjByFiniteIdele_eq
    hab hΛ N m hm1 hmN hidx''
  obtain ⟨-, φ, hφ, hΛφ, k₁, k₂, hk₁, hk₁i, hk₂, hk₂i, hφm⟩ := hfr v (pr v) (pr_prime v) hv hℓN
  have hval : padicValNat (pr v) N = 1 := by
    apply le_antisymm
    · by_contra hlt
      push_neg at hlt
      have h2 : (pr v) ^ 2 ∣ N := (pow_dvd_pow (pr v) (Nat.succ_le_of_lt hlt)).trans pow_padicValNat_dvd
      rw [pow_two] at h2
      exact (pr_prime v).ne_one (Nat.isUnit_iff.mp (hN (pr v) h2))
    · exact Nat.one_le_iff_ne_zero.mpr ((dvd_iff_padicValNat_ne_zero (NeZero.ne N)).mp hℓN)
  rw [hval, diagonal_eq_tM] at hφm
  have hΛφ' : ∀ z, z ∈ Submodule.localBox Λ v ↔ φ z ∈ intMat v := fun z => hΛφ z

  set k : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v) := (k₁ : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) with hkdef
  set ki : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v) := ((k₁⁻¹ : GL (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)) with hkidef
  have hkki : k * ki = 1 := k₁.mul_inv
  have hkik : ki * k = 1 := k₁.inv_mul
  have hRΨ : ∀ x, x ∈ Submodule.localBox R v ↔ ki * φ x * k ∈ intMat v ∧ tMi v * (ki * φ x * k) * tM v ∈ intMat v := by
    intro x; rw [hRm]
    exact localBox_inf_conj_iff hΛo m v φ hΛφ' k ki k₂ (↑k₂⁻¹) hk₁ hk₁i hk₂ hk₂i hkki hkik k₂.mul_inv k₂.inv_mul hφm x
  have hΛΨ : ∀ x, x ∈ Submodule.localBox Λ v ↔ ki * φ x * k ∈ intMat v := fun x => by
    rw [hΛφ', conj_mem_intMat_iff v hk₁ hk₁i hkki hkik]

  have key : ∀ x : (𝔹)ˣ, x ∈ levelHeckeUSet Λ R (pr v) →
      (∀ w, w ≠ v → ev w (x : 𝔹) ∈ Submodule.localBox R w ∧ ev w ((x⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w) ∧
      ∃ ι ιi ι' ι'i : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v),
        ι ∈ intMat v ∧ ιi ∈ intMat v ∧ ι' ∈ intMat v ∧ ι'i ∈ intMat v ∧
        ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
        ((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)⁻¹ * ι 1 0 ∈ HeightOneSpectrum.adicCompletionIntegers ℚ v ∧
        ((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)⁻¹ * ι' 1 0 ∈ HeightOneSpectrum.adicCompletionIntegers ℚ v ∧
        ki * φ (ev v (x : 𝔹)) * k = ι * tbM v * ι' := by
    intro x hx
    simp only [CerednikDrinfeld.levelHeckeUSet, Set.mem_setOf_eq, QuaternionAlgebra.mem_primeHeckeSet_iff] at hx
    obtain ⟨⟨hx1, hx2, hx3, hx4⟩, hx5, hx6⟩ := hx
    have hoff : ∀ w, w ≠ v → ev w (x : 𝔹) ∈ Submodule.localBox R w ∧ ev w ((x⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := by
      intro w hw
      have hnot : ((pr v : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := pr_notMem_asIdeal_of_ne v w hw
      refine ⟨(mem_box_iff hRo _).1 hx1 w, ?_⟩
      have h2w := (mem_box_iff hRo _).1 hx2 w
      rw [ev_ratCast_smul, algebraMap_natCast] at h2w
      have := one_tmul_mul_mem_localBox R w h2w (natCast_inv_mem_integers w hnot)
      rwa [one_tmul_inv_mul_cancel w (natCast_ne_zero_of_notMem w hnot)] at this
    refine ⟨hoff, ?_⟩
    set Y : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v) := ki * φ (ev v (x : 𝔹)) * k with hYdef
    set Yi : Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v) := ki * φ (ev v ((x⁻¹ : (𝔹)ˣ) : 𝔹)) * k with hYidef
    have h1 : Y * Yi = 1 := by
      rw [hYdef, hYidef, conjφ_mul v φ k ki hkki, ev_units_mul_inv, map_one, mul_one, hkik]
    have h2 : Yi * Y = 1 := by
      rw [hYdef, hYidef, conjφ_mul v φ k ki hkki, ev_units_inv_mul, map_one, mul_one, hkik]
    have hc1 : Y ∈ intMat v ∧ tMi v * Y * tM v ∈ intMat v := (hRΨ _).1 ((mem_box_iff hRo _).1 hx1 v)
    have hc2 : ((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) • Yi ∈ intMat v ∧
        tMi v * (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v) • Yi) * tM v ∈ intMat v := by
      have h := (mem_box_iff hRo _).1 hx2 v
      rw [ev_ratCast_smul, algebraMap_natCast, hRΨ, φ_one_tmul_mul v φ hφ, Matrix.mul_smul, Matrix.smul_mul] at h
      exact h
    have hc3 : ¬ (Yi ∈ intMat v ∧ tMi v * Yi * tM v ∈ intMat v) := by
      intro H; apply hx3
      rw [mem_box_iff hRo]
      intro w
      by_cases hw : w = v
      · rw [hw]; exact (hRΨ _).2 H
      · exact (hoff w hw).2
    have hc4 : ¬ (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)⁻¹ • Y ∈ intMat v ∧
        tMi v * (((pr v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)⁻¹ • Y) * tM v ∈ intMat v) := by
      intro H; apply hx4
      rw [mem_box_iff hRo]
      intro w
      rw [ev_ratCast_smul, map_inv₀, algebraMap_natCast]
      by_cases hw : w = v
      · rw [hw, hRΨ, φ_one_tmul_mul v φ hφ, Matrix.mul_smul, Matrix.smul_mul]; exact H
      · exact one_tmul_mul_mem_localBox R w (hoff w hw).1 (natCast_inv_mem_integers w (pr_notMem_asIdeal_of_ne v w hw))
    refine exists_tbM_type v h1 h2 hc1.1 hc1.2 hc2.1 hc2.2 hc3 hc4 ?_ ?_
    · intro H
      exact hx5 (conj_eq_of_local hRo v φ k ki hkki hRΨ x hoff Y Yi hYdef.symm hYidef.symm h1 H)
    · intro H
      exact hx6 (le_conj_of_local hRo hΛo hRΛ v φ k ki hkki hΛΨ hRΨ x hoff Y Yi hYdef.symm hYidef.symm H)

  obtain ⟨hoffh, ι, ιi, ι', ι'i, hι, hιi, hι', hι'i, e1, e2, e1', e2', hι10, hι'10, hY⟩ := key h hh
  obtain ⟨hoffg, μ, μi, μ', μ'i, hμ, hμi, hμ', hμ'i, f1, f2, f1', f2', hμ10, hμ'10, hG⟩ := key g hg

  have hYi : ki * φ (ev v ((h⁻¹ : (𝔹)ˣ) : 𝔹)) * k = ι'i * tbMi v * ιi :=
    inv_eq_of_eq_mul_tbM_mul v (by rw [conjφ_mul v φ k ki hkki, ev_units_inv_mul, map_one, mul_one, hkik]) e1 e1' hY
  have hGi : ki * φ (ev v ((g⁻¹ : (𝔹)ˣ) : 𝔹)) * k = μ'i * tbMi v * μi :=
    inv_eq_of_eq_mul_tbM_mul v (by rw [conjφ_mul v φ k ki hkki, ev_units_inv_mul, map_one, mul_one, hkik]) f1 f1' hG

  have hιΓ : tMi v * ι * tM v ∈ intMat v := (iwahori_iff v hι).2 hι10
  have hι'Γ : tMi v * ι' * tM v ∈ intMat v := (iwahori_iff v hι').2 hι'10
  have hμΓ : tMi v * μ * tM v ∈ intMat v := (iwahori_iff v hμ).2 hμ10
  have hμ'Γ : tMi v * μ' * tM v ∈ intMat v := (iwahori_iff v hμ').2 hμ'10
  have hιiΓ := (iwahori_inv_mem v e1 e2 hι hιΓ (valued_det_eq_one v hι hιi e1)).2
  have hι'iΓ := (iwahori_inv_mem v e1' e2' hι' hι'Γ (valued_det_eq_one v hι' hι'i e1')).2
  have hμiΓ := (iwahori_inv_mem v f1 f2 hμ hμΓ (valued_det_eq_one v hμ hμi f1)).2
  have hμ'iΓ := (iwahori_inv_mem v f1' f2' hμ' hμ'Γ (valued_det_eq_one v hμ' hμ'i f1')).2

  set yv : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v := φ.symm (k * (ι * μi) * ki) with hyv
  set yvi : ℍ[ℚ, a, b] ⊗[ℚ] HeightOneSpectrum.adicCompletion ℚ v := φ.symm (k * (μ * ιi) * ki) with hyvi
  have hyy : yv * yvi = 1 := by
    rw [hyv, hyvi, ← map_mul]
    have e : k * (ι * μi) * ki * (k * (μ * ιi) * ki) = 1 := by
      calc _ = k * (ι * (μi * ((ki * k) * μ)) * ιi) * ki := by noncomm_ring
        _ = 1 := by rw [hkik, one_mul, f2, mul_one, e1, mul_one, hkki]
    rw [e, map_one]
  have hyy' : yvi * yv = 1 := by
    rw [hyv, hyvi, ← map_mul]
    have e : k * (μ * ιi) * ki * (k * (ι * μi) * ki) = 1 := by
      calc _ = k * (μ * (ιi * ((ki * k) * ι)) * μi) * ki := by noncomm_ring
        _ = 1 := by rw [hkik, one_mul, e2, mul_one, f1, mul_one, hkki]
    rw [e, map_one]
  have hφyv : ki * φ yv * k = ι * μi := by rw [hyv, RingEquiv.apply_symm_apply, conjφ_sandwich v k ki _ hkik]
  have hφyvi : ki * φ yvi * k = μ * ιi := by rw [hyvi, RingEquiv.apply_symm_apply, conjφ_sandwich v k ki _ hkik]
  obtain ⟨u, huv, huiv, huw⟩ := exists_unit_patch hRo v yv yvi hyy hyy' 1
    (fun w _ => ⟨by exact ev_one_mem_localBox hRo w, by rw [inv_one]; exact ev_one_mem_localBox hRo w⟩)

  have hu : u ∈ Submodule.finiteIdeleStabilizer R := by
    rw [mem_stab_iff hRo]
    intro w
    by_cases hw : w = v
    · rw [hw, huv, huiv, hRΨ, hRΨ, hφyv, hφyvi]
      exact ⟨iwahori_mul_mem v hι hιΓ hμi hμiΓ, iwahori_mul_mem v hμ hμΓ hιi hιiΓ⟩
    · rw [(huw w hw).1, (huw w hw).2, inv_one]
      exact ⟨ev_one_mem_localBox hRo w, ev_one_mem_localBox hRo w⟩

  have hu' : g⁻¹ * u⁻¹ * h ∈ Submodule.finiteIdeleStabilizer R := by
    rw [mem_stab_iff hRo]
    intro w
    have einv : ((g⁻¹ * u⁻¹ * h)⁻¹ : (𝔹)ˣ) = h⁻¹ * u * g := by group
    rw [einv, Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, map_mul, map_mul, map_mul, map_mul]
    by_cases hw : w = v
    · rw [hw, hRΨ, hRΨ, conjφ_mul3 v φ k ki hkki, conjφ_mul3 v φ k ki hkki, hGi, huiv, hφyvi, hY, hYi, huv, hφyv, hG]
      have P1 : μ'i * tbMi v * μi * (μ * ιi) * (ι * tbM v * ι') = μ'i * ι' := by
        calc _ = μ'i * (tbMi v * ((μi * μ) * (ιi * ι)) * tbM v) * ι' := by noncomm_ring
          _ = μ'i * ι' := by simp only [f2, e2, mul_one, one_mul, tbMi_mul_tbM]
      have P2 : ι'i * tbMi v * ιi * (ι * μi) * (μ * tbM v * μ') = ι'i * μ' := by
        calc _ = ι'i * (tbMi v * ((ιi * ι) * (μi * μ)) * tbM v) * μ' := by noncomm_ring
          _ = ι'i * μ' := by simp only [f2, e2, mul_one, one_mul, tbMi_mul_tbM]
      rw [P1, P2]
      exact ⟨iwahori_mul_mem v hμ'i hμ'iΓ hι' hι'Γ, iwahori_mul_mem v hι'i hι'iΓ hμ' hμ'Γ⟩
    · rw [(huw w hw).1, (huw w hw).2]
      refine ⟨mul_mem_localBox R w hmulR (mul_mem_localBox R w hmulR (hoffg w hw).2 ?_) (hoffh w hw).1,
        mul_mem_localBox R w hmulR (mul_mem_localBox R w hmulR (hoffh w hw).2 (ev_one_mem_localBox hRo w)) (hoffg w hw).1⟩
      rw [inv_one]; exact ev_one_mem_localBox hRo w
  exact ⟨u, hu, g⁻¹ * u⁻¹ * h, hu', by group⟩

theorem levelHeckeUSet_eq_doubleCoset
    {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {R Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} [NeZero N] (hN : Squarefree N)
    (hR : IsEichlerOrder R N) (hΛ : IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    (hq'N : ¬ q' ∣ N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N)
    {g : (𝔹)ˣ} (hg : g ∈ levelHeckeUSet Λ R ℓ) :
    levelHeckeUSet Λ R ℓ =
      DoubleCoset.doubleCoset g (Submodule.finiteIdeleStabilizer R : Set (𝔹)ˣ) (Submodule.finiteIdeleStabilizer R : Set (𝔹)ˣ) := by
  ext h
  rw [DoubleCoset.mem_doubleCoset]
  constructor
  · intro hh
    obtain ⟨u, hu, u', hu', e⟩ :=
      exists_mem_finiteIdeleStabilizer_eq_mul_mul_of_mem_levelHeckeUSet hdef hN hR hΛ hRΛ hq'N ℓ hℓN hh hg
    exact ⟨u, hu, u', hu', e⟩
  · rintro ⟨u, hu, u', hu', rfl⟩
    have h1 := (CerednikDrinfeld.mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer Λ R
      hΛ.isOrder hR.isOrder hRΛ ℓ hu hg).1
    exact (CerednikDrinfeld.mul_mem_levelHeckeUSet_and_mul_mem_levelHeckeUSet_of_mem_finiteIdeleStabilizer Λ R
      hΛ.isOrder hR.isOrder hRΛ ℓ hu' h1).2

end UMain
p2m_reactivate "P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.LevelULocal"

end LevelULocal
p2m_reactivate "P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.LevelULocal"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree.LevelULocal"

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

theorem solution
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    {R Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} [NeZero N] (hN : Squarefree N)
    (hR : QuaternionAlgebra.IsEichlerOrder R N) (hΛ : QuaternionAlgebra.IsMaximalOrder Λ) (hRΛ : R ≤ Λ)
    (hq'N : ¬ q' ∣ N) (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ℓ ∣ N)
    {g : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hg : g ∈ CerednikDrinfeld.levelHeckeUSet Λ R ℓ) :
    CerednikDrinfeld.levelHeckeUSet Λ R ℓ =
      DoubleCoset.doubleCoset g (Submodule.finiteIdeleStabilizer R : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
        (Submodule.finiteIdeleStabilizer R : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :=
  LevelULocal.levelHeckeUSet_eq_doubleCoset hdef hN hR hΛ hRΛ hq'N ℓ hℓN hg

end S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree
end P2MW
export P2MW.S_CerednikDrinfeld_levelHeckeUSet_eq_doubleCoset_finiteIdeleStabilizer_of_dvd_of_squarefree (solution)
