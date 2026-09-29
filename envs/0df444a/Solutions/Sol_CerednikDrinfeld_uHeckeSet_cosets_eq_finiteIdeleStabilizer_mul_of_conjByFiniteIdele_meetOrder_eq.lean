-- Prove2me | solution 1 for CerednikDrinfeld.uHeckeSet_cosets_eq_finiteIdeleStabilizer_mul_of_conjByFiniteIdele_meetOrder_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/dc35e700-8f30-5ce7-84c0-f7adbad8e17e

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_CerednikDrinfeld_CosetGraph_mul_self_mem_level_and_not_mem_level_and_mem_inf_conj_iff_of_mem_primeHeckeSet
import Theorems.Thm_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
import Theorems.Thm_Submodule_finiteAdeleBox_conjByFiniteIdele
import Theorems.Thm_CerednikDrinfeld_exists_mem_finiteIdeleStabilizer_mul_eq_natCast_smul_of_mem_uHeckeSet
import Theorems.Thm_CerednikDrinfeld_uHeckeSet_cosetDictionary_of_mem_primeHeckeSet
import Theorems.Thm_QuaternionAlgebra_IsOrder_mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_uHeckeSet_cosets_eq_finiteIdeleStabilizer_mul_of_conjByFiniteIdele_meetOrder_eq
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
open IsDedekindDomain NumberField

noncomputable section

namespace UHeckeCosets

section Places

def place (q : ℕ) (hq : q.Prime) : HeightOneSpectrum (𝓞 ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm ⟨q, hq⟩

variable (q : ℕ) (hq : q.Prime)

local notation "𝔳" => place q hq
local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)

theorem primesEquiv_place : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) 𝔳 = ⟨q, hq⟩ := by
  simp [place]

theorem natGenerator_place : Rat.HeightOneSpectrum.natGenerator 𝔳 = q :=
  congrArg Subtype.val (primesEquiv_place q hq)

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem eq_place_of_mem (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (q : 𝓞 ℚ) ∈ w.asIdeal) : w = 𝔳 := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [primesEquiv_place]
  apply Subtype.ext
  change Rat.HeightOneSpectrum.natGenerator w = q
  exact (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).1
    ((natCast_mem_asIdeal_iff w q).1 hw)

theorem natCast_mem_asIdeal_place_iff (n : ℕ) : (n : 𝓞 ℚ) ∈ (𝔳).asIdeal ↔ q ∣ n := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

theorem q_mem_asIdeal : (q : 𝓞 ℚ) ∈ (𝔳).asIdeal := (natCast_mem_asIdeal_place_iff q hq q).2 dvd_rfl

theorem q_notMem_asIdeal_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) : (q : 𝓞 ℚ) ∉ w.asIdeal :=
  fun h => hw (eq_place_of_mem q hq w h)

theorem valuation_natCast_eq_one_of_notMem (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 hn

theorem valuation_q_eq_one_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) : w.valuation ℚ (q : ℚ) = 1 :=
  valuation_natCast_eq_one_of_notMem w q (q_notMem_asIdeal_of_ne q hq w hw)

theorem asIdeal_place_eq_span : (𝔳).asIdeal = Ideal.span {(q : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) 𝔳
  rw [natGenerator_place] at h
  have h2 : (𝔳).asIdeal = Ideal.map ((Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)).symm : ℤ →+* 𝓞 ℚ)
      (Ideal.map (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) : 𝓞 ℚ →+* ℤ) (𝔳).asIdeal) := by
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

theorem valuation_q : (𝔳).valuation ℚ (q : ℚ) = WithZero.exp (-1) := by
  rw [show (q : ℚ) = algebraMap (𝓞 ℚ) ℚ q from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ (by exact_mod_cast hq.ne_zero) (asIdeal_place_eq_span q hq)

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem algebraMap_natCast (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ) = (n : w.adicCompletion ℚ) := map_natCast _ n

theorem valued_q : Valued.v ((q : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [← algebraMap_natCast, valued_algebraMap, valuation_q]

theorem q_ne_zero' : ((q : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_q q hq
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← algebraMap_natCast, valued_algebraMap,
    show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one w _

theorem algebraMap_zpow_mem_integers_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) (m : ℤ) :
    algebraMap ℚ (w.adicCompletion ℚ) ((q : ℚ) ^ m) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap, map_zpow₀,
    valuation_q_eq_one_of_ne q hq w hw, one_zpow]

theorem algebraMap_zpow_place (m : ℤ) : algebraMap ℚ 𝕂 ((q : ℚ) ^ m) = ((q : ℕ) : 𝕂) ^ m := by
  rw [map_zpow₀, algebraMap_natCast]

theorem valued_zpow (m : ℤ) : Valued.v (((q : ℕ) : 𝕂) ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, valued_q, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem valued_le_one_of_mem {x : 𝕂} (hx : x ∈ 𝓞v) : Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ 𝔳).1 hx

theorem mem_integers_of_valued_le_one {x : 𝕂} (hx : Valued.v x ≤ 1) : x ∈ 𝓞v :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ 𝔳).2 hx

theorem inv_mem_integers_of_valued_eq_one {x : 𝕂} (h : Valued.v x = 1) : x⁻¹ ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]

theorem exists_valued_eq_exp {c : 𝕂} (hc : c ≠ 0) : ∃ m : ℤ, Valued.v c = WithZero.exp m :=
  ⟨WithZero.log (Valued.v c), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hc)).symm⟩

theorem exists_inv_q_eq_mul {d : 𝕂} {k : ℤ} (hd : Valued.v d = WithZero.exp k) (hk : 1 ≤ k) :
    ∃ e ∈ 𝓞v, ((q : ℕ) : 𝕂)⁻¹ = d * e := by
  have hd0 : d ≠ 0 := by
    intro h; rw [h, map_zero] at hd; exact WithZero.zero_ne_coe hd
  refine ⟨d⁻¹ * ((q : ℕ) : 𝕂)⁻¹, ?_, by rw [← mul_assoc, mul_inv_cancel₀ hd0, one_mul]⟩
  apply mem_integers_of_valued_le_one
  rw [map_mul, map_inv₀, map_inv₀, hd, valued_q, ← WithZero.exp_neg, ← WithZero.exp_neg, ← WithZero.exp_add,
    ← WithZero.exp_zero, WithZero.exp_le_exp]
  omega

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

theorem mul_one_tmul_mem_localBox {x : D ⊗[ℚ] 𝕂} (hx : x ∈ Submodule.localBox Λ v) {c : 𝕂}
    (hc : c ∈ 𝓞v) : x * ((1 : D) ⊗ₜ[ℚ] c) ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    exact tmul_mem_localBox Λ v hz (mul_mem hc' hc)
  | zero => rw [zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact add_mem hx hy
  | neg x _ hx => exact (neg_mul x _).symm ▸ neg_mem hx

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

omit Λ in

theorem one_tmul_mul_comm (c : 𝕂) (x : D ⊗[ℚ] 𝕂) :
    ((1 : D) ⊗ₜ[ℚ] c) * x = x * ((1 : D) ⊗ₜ[ℚ] c) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | tmul z d => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one,
      mul_comm]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

omit Λ in
theorem one_tmul_mul_one_tmul (c d : 𝕂) :
    ((1 : D) ⊗ₜ[ℚ] c) * ((1 : D) ⊗ₜ[ℚ] d) = (1 : D) ⊗ₜ[ℚ] (c * d) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

end Box

section Global

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

open QuaternionAlgebra CerednikDrinfeld

theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (x : 𝔹) :
    x ∈ Submodule.finiteAdeleBox Λ ↔ ∀ w, ev w x ∈ Submodule.localBox Λ w :=
  Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop x

theorem box_mul_mem {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {x y : 𝔹}
    (hx : x ∈ Submodule.finiteAdeleBox Λ) (hy : y ∈ Submodule.finiteAdeleBox Λ) :
    x * y ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_box_iff hΛ] at hx hy ⊢
  intro w
  rw [map_mul]
  exact mul_mem_localBox Λ w (fun x y hx hy => hΛ.mul_mem hx hy) (hx w) (hy w)

theorem one_mem_box {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) : (1 : 𝔹) ∈ Submodule.finiteAdeleBox Λ := by
  rw [Algebra.TensorProduct.one_def]
  exact AddSubgroup.subset_closure ⟨1, hΛ.one_mem, 1, fun w => one_mem _, rfl⟩

theorem ev_units_mul_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    ev w (g : 𝔹) * ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) = 1 := by rw [← map_mul, Units.mul_inv, map_one]

theorem ev_units_inv_mul (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) * ev w (g : 𝔹) = 1 := by rw [← map_mul, Units.inv_mul, map_one]

theorem coe_units_map_ev (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    ((Units.map (ev w).toRingHom.toMonoidHom g : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = ev w (g : 𝔹) := rfl

theorem coe_units_map_ev_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    (((Units.map (ev w).toRingHom.toMonoidHom g)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) := by
  rw [← map_inv]; rfl

theorem ev_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    ev w (algebraMap ℚ 𝔹 r) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) r := by
  rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply']

theorem ev_ratCast_smul (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) (x : 𝔹) :
    ev w (r • x) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) r) * ev w x := by
  rw [map_smul, ratCast_smul_eq_one_tmul_mul]

theorem mem_stab_iff_forall {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (u : (𝔹)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      ∀ w, ev w (u : 𝔹) ∈ Submodule.localBox Λ w ∧ ev w ((u⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox Λ w := by
  rw [QuaternionAlgebra.IsOrder.mem_finiteIdeleStabilizer_iff_forall_map_finiteAdeleEvalAt_mem_localBoxUnits Λ hΛ u]
  refine forall_congr' fun w => ?_
  rw [Submodule.mem_localBoxUnits_iff, SetLike.mem_coe, SetLike.mem_coe, coe_units_map_ev, coe_units_map_ev_inv]

theorem mem_box_of_mem_stab {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) {u : (𝔹)ˣ}
    (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    (u : 𝔹) ∈ Submodule.finiteAdeleBox Λ ∧ ((u⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.finiteAdeleBox Λ := by
  rw [mem_stab_iff_forall hΛ] at hu
  rw [mem_box_iff hΛ, mem_box_iff hΛ]
  exact ⟨fun w => (hu w).1, fun w => (hu w).2⟩

def boxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup (CosetGraph.Loc a b w)ˣ where
  carrier := Submodule.localBoxUnits Λ w
  one_mem' := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_one, Algebra.TensorProduct.one_def]
      exact tmul_one_mem_localBox Λ w hΛ.one_mem
    · rw [inv_one, Units.val_one, Algebra.TensorProduct.one_def]
      exact tmul_one_mem_localBox Λ w hΛ.one_mem
  mul_mem' {x y} hx hy := by
    have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ Λ → y ∈ Λ → x * y ∈ Λ := fun x y hx hy => hΛ.mul_mem hx hy
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]; exact mul_mem_localBox Λ w hmul hx.1 hy.1
    · rw [mul_inv_rev, Units.val_mul]; exact mul_mem_localBox Λ w hmul hy.2 hx.2
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem closure_localBoxUnits {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ)) :
    Subgroup.closure (Submodule.localBoxUnits Λ w) = boxUnits hΛ w :=
  (boxUnits hΛ w).closure_eq

def sc (w : HeightOneSpectrum (𝓞 ℚ)) (c : (w.adicCompletion ℚ)ˣ) : (CosetGraph.Loc a b w)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight :
    w.adicCompletion ℚ →ₐ[ℚ] CosetGraph.Loc a b w).toRingHom.toMonoidHom c

theorem coe_sc (w : HeightOneSpectrum (𝓞 ℚ)) (c : (w.adicCompletion ℚ)ˣ) :
    ((sc w c : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) = (1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (c : w.adicCompletion ℚ) :=
  rfl

theorem sc_inv (w : HeightOneSpectrum (𝓞 ℚ)) (c : (w.adicCompletion ℚ)ˣ) :
    (sc w c : (CosetGraph.Loc a b w)ˣ)⁻¹ = sc w c⁻¹ := by
  rw [sc, sc, map_inv]

theorem sc_mul (w : HeightOneSpectrum (𝓞 ℚ)) (c c' : (w.adicCompletion ℚ)ˣ) :
    (sc w (c * c') : (CosetGraph.Loc a b w)ˣ) = sc w c * sc w c' := by
  rw [sc, sc, sc, map_mul]

theorem sc_mem_scalarUnits (w : HeightOneSpectrum (𝓞 ℚ)) (c : (w.adicCompletion ℚ)ˣ) :
    (sc w c : (CosetGraph.Loc a b w)ˣ) ∈ CosetGraph.scalarUnits w :=
  ⟨c, rfl⟩

theorem mem_scalarUnits_iff (w : HeightOneSpectrum (𝓞 ℚ)) (s : (CosetGraph.Loc a b w)ˣ) :
    s ∈ CosetGraph.scalarUnits w ↔ ∃ c, s = sc w c := by
  constructor
  · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
  · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩

theorem sc_mul_comm (w : HeightOneSpectrum (𝓞 ℚ)) (c : (w.adicCompletion ℚ)ˣ) (g : (CosetGraph.Loc a b w)ˣ) :
    sc w c * g = g * sc w c :=
  Units.ext (by rw [Units.val_mul, Units.val_mul, coe_sc]; exact one_tmul_mul_comm w _ _)

theorem mul_sc_mul (w : HeightOneSpectrum (𝓞 ℚ)) (c : (w.adicCompletion ℚ)ˣ) (g h : (CosetGraph.Loc a b w)ˣ) :
    g * (sc w c * h) = sc w c * (g * h) := by
  rw [← mul_assoc, ← sc_mul_comm, mul_assoc]

theorem scalarUnits_normal (w : HeightOneSpectrum (𝓞 ℚ)) : (CosetGraph.scalarUnits (a := a) (b := b) w).Normal :=
  ⟨fun s hs g => by
    obtain ⟨c, rfl⟩ := (mem_scalarUnits_iff w s).1 hs
    rw [← sc_mul_comm, mul_inv_cancel_right]
    exact sc_mem_scalarUnits w c⟩

theorem mem_level_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    (k : (CosetGraph.Loc a b w)ˣ) :
    k ∈ CosetGraph.level Λ w ↔
      ∃ c : (w.adicCompletion ℚ)ˣ, ∃ t ∈ Submodule.localBoxUnits Λ w, k = sc w c * t := by
  haveI := scalarUnits_normal (a := a) (b := b) w
  rw [CosetGraph.level, closure_localBoxUnits hΛ w]
  constructor
  · intro hk
    have hk' : k ∈ ((boxUnits hΛ w ⊔ CosetGraph.scalarUnits w : Subgroup (CosetGraph.Loc a b w)ˣ) :
        Set (CosetGraph.Loc a b w)ˣ) := hk
    rw [Subgroup.mul_normal] at hk'
    obtain ⟨t, ht, s, hs, rfl⟩ := Set.mem_mul.1 hk'
    obtain ⟨c, rfl⟩ := (mem_scalarUnits_iff w s).1 hs
    exact ⟨c, t, ht, (sc_mul_comm w c t).symm⟩
  · rintro ⟨c, t, ht, rfl⟩
    exact mul_mem (Subgroup.mem_sup_right (sc_mem_scalarUnits w c)) (Subgroup.mem_sup_left ht)

end Global

section SetConj

variable {M : Type*} [Monoid M]

def κ (g : Mˣ) : M → M := fun x => (g : M) * x * ((g⁻¹ : Mˣ) : M)

theorem κ_apply (g : Mˣ) (x : M) : κ g x = (g : M) * x * ((g⁻¹ : Mˣ) : M) := rfl

theorem κ_injective (g : Mˣ) : Function.Injective (κ g) := by
  intro x y h
  rwa [κ_apply, κ_apply, Units.mul_left_inj, Units.mul_right_inj] at h

theorem smul_set_eq_image (u : Mˣ) (X : Set M) : u • X = (fun x => (u : M) * x) '' X := by
  ext y; simp only [Set.mem_smul_set, Set.mem_image, Units.smul_def, smul_eq_mul]

theorem image_κ_smul (g u : Mˣ) (X : Set M) : κ g '' (u • X) = (g * u * g⁻¹) • (κ g '' X) := by
  rw [smul_set_eq_image, smul_set_eq_image, Set.image_image, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  simp only [κ_apply, Units.val_mul, mul_assoc, Units.inv_mul_cancel_left]

theorem conj_smul_eq_iff (g u : Mˣ) {X : Set M} (hX : κ g '' X = X) :
    (g * u * g⁻¹) • X = X ↔ u • X = X := by
  have e : (g * u * g⁻¹) • X = κ g '' (u • X) := by rw [image_κ_smul, hX]
  constructor
  · intro h
    apply (κ_injective g).image_injective
    rw [← e, h, hX]
  · intro h
    rw [e, h, hX]

end SetConj

section Frame

variable {a b : ℚ}

open QuaternionAlgebra CerednikDrinfeld

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

theorem coe_map_conj (X : AddSubgroup 𝔹) (g : (𝔹)ˣ) :
    ((X.map ((AddMonoidHom.mulRight ((g⁻¹ : (𝔹)ˣ) : 𝔹)).comp (AddMonoidHom.mulLeft (g : 𝔹))) :
        AddSubgroup 𝔹) : Set 𝔹) = κ g '' (X : Set 𝔹) := by
  rw [AddSubgroup.coe_map]
  refine Set.image_congr fun x _ => ?_
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight,
    κ_apply]

theorem mem_stab_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (u : (𝔹)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ ↔
      u • ((Submodule.finiteAdeleBox Λ : AddSubgroup 𝔹) : Set 𝔹) =
        ((Submodule.finiteAdeleBox Λ : AddSubgroup 𝔹) : Set 𝔹) :=
  Submodule.mem_finiteIdeleStabilizer_iff Λ u

def ratIdele (r : ℚ) (hr : r ≠ 0) : (𝔹)ˣ where
  val := algebraMap ℚ 𝔹 r
  inv := algebraMap ℚ 𝔹 r⁻¹
  val_inv := by rw [← map_mul, mul_inv_cancel₀ hr, map_one]
  inv_val := by rw [← map_mul, inv_mul_cancel₀ hr, map_one]

theorem coe_ratIdele (r : ℚ) (hr : r ≠ 0) : ((ratIdele (a := a) (b := b) r hr : (𝔹)ˣ) : 𝔹) = algebraMap ℚ 𝔹 r :=
  rfl

theorem coe_ratIdele_inv (r : ℚ) (hr : r ≠ 0) :
    (((ratIdele (a := a) (b := b) r hr)⁻¹ : (𝔹)ˣ) : 𝔹) = algebraMap ℚ 𝔹 r⁻¹ :=
  rfl

theorem ratIdele_comm (r : ℚ) (hr : r ≠ 0) (x : (𝔹)ˣ) : ratIdele r hr * x = x * ratIdele r hr :=
  Units.ext (Algebra.commutes r (x : 𝔹))

theorem mul_ratIdele_mul (r : ℚ) (hr : r ≠ 0) (x y : (𝔹)ˣ) : x * (ratIdele r hr * y) = ratIdele r hr * (x * y) := by
  rw [← mul_assoc, ← ratIdele_comm, mul_assoc]

theorem mul_ratIdele (r : ℚ) (hr : r ≠ 0) (x : (𝔹)ˣ) : x * ratIdele r hr = ratIdele r hr * x :=
  (ratIdele_comm r hr x).symm

theorem ratIdele_inv_comm (r : ℚ) (hr : r ≠ 0) (x : (𝔹)ˣ) : (ratIdele r hr)⁻¹ * x = x * (ratIdele r hr)⁻¹ := by
  rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ratIdele_comm, mul_inv_cancel_right]

theorem mul_ratIdele_inv_mul (r : ℚ) (hr : r ≠ 0) (x y : (𝔹)ˣ) :
    x * ((ratIdele r hr)⁻¹ * y) = (ratIdele r hr)⁻¹ * (x * y) := by
  rw [← mul_assoc, ← ratIdele_inv_comm, mul_assoc]

theorem mul_ratIdele_inv (r : ℚ) (hr : r ≠ 0) (x : (𝔹)ˣ) : x * (ratIdele r hr)⁻¹ = (ratIdele r hr)⁻¹ * x :=
  (ratIdele_inv_comm r hr x).symm

variable (q : ℕ) (hq : q.Prime)

local notation "𝔳" => place q hq
local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)
local notation "ϖ" => ((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ (place q hq))
set_option quotPrecheck false in
local notation "Lv" => CerednikDrinfeld.CosetGraph.Loc a b (place q hq)
set_option quotPrecheck false in
local notation "zq" => (ratIdele (a := a) (b := b) (q : ℚ) (by exact_mod_cast hq.ne_zero) : (𝔹)ˣ)

variable (R : Submodule ℤ ℍ[ℚ, a, b]) (hRo : IsOrder R)
  (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (hnH : n ∈ primeHeckeSet R q)

set_option quotPrecheck false in
local notation "nv" => (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (place q hq)).toRingHom.toMonoidHom n :
  (CosetGraph.Loc a b (place q hq))ˣ)
set_option quotPrecheck false in
local notation "E" => (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (place q hq)).toRingHom.toMonoidHom :
  (𝔹)ˣ →* (CosetGraph.Loc a b (place q hq))ˣ)

def qK : (𝕂)ˣ := Units.mk0 ϖ (q_ne_zero' q hq)

theorem coe_qK : ((qK q hq : (𝕂)ˣ) : 𝕂) = ϖ := rfl

theorem valued_qK : Valued.v ((qK q hq : (𝕂)ˣ) : 𝕂) = WithZero.exp (-1) := valued_q q hq

include hRo in
theorem isOrder_S : IsOrder (meetOrder R n) :=
  hRo.inf (QuaternionAlgebra.IsOrder.conjByFiniteIdele R hRo n)

theorem meetOrder_le : meetOrder R n ≤ R := inf_le_left

include hRo in

theorem coe_box_S :
    ((Submodule.finiteAdeleBox (meetOrder R n) : AddSubgroup 𝔹) : Set 𝔹) =
      ((Submodule.finiteAdeleBox R : AddSubgroup 𝔹) : Set 𝔹) ∩
        κ n '' ((Submodule.finiteAdeleBox R : AddSubgroup 𝔹) : Set 𝔹) := by
  have h := (QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le R hRo n).1
  rw [meetOrder, h, AddSubgroup.coe_inf, coe_map_conj]

include hRo in

theorem image_κ_box_S (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n) :
    κ n '' ((Submodule.finiteAdeleBox (meetOrder R n) : AddSubgroup 𝔹) : Set 𝔹) =
      ((Submodule.finiteAdeleBox (meetOrder R n) : AddSubgroup 𝔹) : Set 𝔹) := by
  have hS := isOrder_S R hRo n
  have h := Submodule.finiteAdeleBox_conjByFiniteIdele (meetOrder R n) hS.fg hS.spanTop n
  rw [hnorm] at h
  rw [← coe_map_conj, ← h]

include hRo in

theorem mem_stab_S_iff_conj (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n) (u : (𝔹)ˣ) :
    u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ↔
      n * u * n⁻¹ ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
  rw [mem_stab_iff, mem_stab_iff, conj_smul_eq_iff n u (image_κ_box_S R hRo n hnorm)]

include hRo in

theorem inv_mul_mul_mem_stab_S_iff (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (x : (𝔹)ˣ) :
    n⁻¹ * x * n ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ↔
      x ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
  rw [mem_stab_S_iff_conj R hRo n hnorm (n⁻¹ * x * n)]
  have e : n * (n⁻¹ * x * n) * n⁻¹ = x := by group
  rw [e]

include hRo in

theorem stab_S_le : Submodule.finiteIdeleStabilizer (meetOrder R n) ≤ Submodule.finiteIdeleStabilizer R :=
  (QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le R hRo n).2.2.1

include hRo in
theorem conj_mem_stab_R_of_mem_stab_S {u : (𝔹)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) :
    n⁻¹ * u * n ∈ Submodule.finiteIdeleStabilizer R :=
  (QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le R hRo n).2.2.2 u hu

include hRo in

theorem mem_stab_S_of (u : (𝔹)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer R)
    (hu' : n⁻¹ * u * n ∈ Submodule.finiteIdeleStabilizer R) :
    u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
  rw [mem_stab_iff] at hu hu' ⊢
  rw [coe_box_S R hRo n, Set.smul_set_inter, hu]
  congr 1
  have e : u = n * (n⁻¹ * u * n) * n⁻¹ := by group
  conv_lhs => rw [e]
  rw [← image_κ_smul, hu']

theorem E_zq : E zq = sc 𝔳 (qK q hq) := by
  apply Units.ext
  rw [coe_units_map_ev, coe_ratIdele, ev_algebraMap, coe_sc, coe_qK, algebraMap_natCast]

include hq hRo hnH in

theorem ev_n_mem (w : HeightOneSpectrum (𝓞 ℚ)) : ev w (n : 𝔹) ∈ Submodule.localBox R w :=
  (mem_box_iff hRo _).1 hnH.1 w

include hq hRo hnH in

theorem q_ev_n_inv_mem (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) (q : ℚ)) * ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) ∈
      Submodule.localBox R w := by
  have h := (mem_box_iff hRo _).1 hnH.2.1 w
  rwa [ev_ratCast_smul] at h

include hRo hnH in

theorem ev_n_inv_mem (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) :
    ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := by
  have h := q_ev_n_inv_mem q hq R hRo n hnH w
  have e : ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) ((q : ℚ) ^ (-1 : ℤ))) *
        (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) (q : ℚ)) * ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹)) := by
    rw [← mul_assoc, one_tmul_mul_one_tmul, ← map_mul, zpow_neg, zpow_one,
      inv_mul_cancel₀ (by exact_mod_cast hq.ne_zero : (q : ℚ) ≠ 0), map_one, ← Algebra.TensorProduct.one_def,
      one_mul]
  rw [e]
  exact one_tmul_mul_mem_localBox R w h (algebraMap_zpow_mem_integers_of_ne q hq w hw (-1))

include hRo hnH in

theorem false_of_ev_n_inv_mem (h : ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R 𝔳) : False := by
  apply hnH.2.2.1
  rw [mem_box_iff hRo]
  intro w
  by_cases hw : w = 𝔳
  · subst hw; exact h
  · exact ev_n_inv_mem q hq R hRo n hnH w hw

include hRo hnH in

theorem false_of_qinv_ev_n_mem
    (h : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ϖ)⁻¹) * ev 𝔳 (n : 𝔹) ∈ Submodule.localBox R 𝔳) : False := by
  apply hnH.2.2.2
  rw [mem_box_iff hRo]
  intro w
  rw [ev_ratCast_smul]
  by_cases hw : w = 𝔳
  · subst hw
    rwa [map_inv₀, algebraMap_natCast]
  · rw [← zpow_neg_one]
    exact one_tmul_mul_mem_localBox R w (ev_n_mem q hq R hRo n hnH w)
      (algebraMap_zpow_mem_integers_of_ne q hq w hw _)

include hRo hnH in

theorem false_of_qinv_mem (h : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ϖ)⁻¹ : Lv) ∈ Submodule.localBox R 𝔳) : False :=
  false_of_qinv_ev_n_mem q hq R hRo n hnH
    (mul_mem_localBox R 𝔳 (fun x y hx hy => hRo.mul_mem hx hy) h (ev_n_mem q hq R hRo n hnH 𝔳))

include hRo hnH in

theorem false_of_scalar_mem {d : 𝕂} {k : ℤ} (hd : Valued.v d = WithZero.exp k) (hk : 1 ≤ k)
    (h : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] d : Lv) ∈ Submodule.localBox R 𝔳) : False := by
  obtain ⟨e, he, hqe⟩ := exists_inv_q_eq_mul q hq hd hk
  apply false_of_qinv_mem q hq R hRo n hnH
  rw [hqe, ← one_tmul_mul_one_tmul]
  exact mul_one_tmul_mem_localBox R 𝔳 h he

include hRo hnH in

theorem valued_c_eq {c : (𝕂)ˣ} {t : (Lv)ˣ} (ht : t ∈ Submodule.localBoxUnits (meetOrder R n) 𝔳)
    (hnt : nv * nv = sc 𝔳 c * t) : Valued.v ((c : 𝕂)) = WithZero.exp (-1) := by
  letI : Algebra 𝕂 Lv := Algebra.TensorProduct.rightAlgebra
  have htm : ∀ s : 𝕂, ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s : Lv) = s • (1 : Lv) := fun s => by
    rw [Algebra.smul_def, mul_one]; rfl
  have hmulR : ∀ x y : ℍ[ℚ, a, b], x ∈ R → y ∈ R → x * y ∈ R := fun x y hx hy => hRo.mul_mem hx hy
  have hϖ : (ϖ : 𝕂) ≠ 0 := q_ne_zero' q hq
  have htR : (t : Lv) ∈ Submodule.localBox R 𝔳 := localBox_mono 𝔳 (meetOrder_le R n) ht.1
  have htiR : ((t⁻¹ : (Lv)ˣ) : Lv) ∈ Submodule.localBox R 𝔳 := localBox_mono 𝔳 (meetOrder_le R n) ht.2
  have hnR : ev 𝔳 (n : 𝔹) ∈ Submodule.localBox R 𝔳 := ev_n_mem q hq R hRo n hnH 𝔳
  have hqni : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ϖ : 𝕂)) * ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R 𝔳 := by
    have h := q_ev_n_inv_mem q hq R hRo n hnH 𝔳
    rwa [algebraMap_natCast] at h
  obtain ⟨m, hm⟩ := exists_valued_eq_exp q hq (c := (c : 𝕂)) c.ne_zero

  have u1 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (c : 𝕂) : Lv) = ev 𝔳 (n : 𝔹) * ev 𝔳 (n : 𝔹) * ((t⁻¹ : (Lv)ˣ) : Lv) := by
    have e : sc 𝔳 c = nv * nv * t⁻¹ := eq_mul_inv_of_mul_eq hnt.symm
    have := congrArg Units.val e
    rwa [coe_sc, Units.val_mul, Units.val_mul, coe_units_map_ev] at this
  have u2 : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((c : 𝕂)⁻¹) : Lv) =
      (t : Lv) * ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹) * ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹) := by
    have e : (sc 𝔳 c)⁻¹ = t * nv⁻¹ * nv⁻¹ := by rw [eq_mul_inv_of_mul_eq hnt.symm]; group
    have := congrArg Units.val e
    rwa [sc_inv, coe_sc, Units.val_inv_eq_inv_val c, Units.val_mul, Units.val_mul, coe_units_map_ev_inv] at this
  have u3 : ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹) =
      ev 𝔳 (n : 𝔹) * ((t⁻¹ : (Lv)ˣ) : Lv) * ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((c : 𝕂)⁻¹)) := by
    have e : nv⁻¹ = nv * t⁻¹ * (sc 𝔳 c)⁻¹ := by rw [eq_mul_inv_of_mul_eq hnt.symm]; group
    have := congrArg Units.val e
    rwa [coe_units_map_ev_inv, sc_inv, Units.val_mul, Units.val_mul, coe_units_map_ev, coe_sc,
      Units.val_inv_eq_inv_val c] at this
  have u4 : ev 𝔳 (n : 𝔹) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (c : 𝕂)) * (t : Lv) * ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹) := by
    have e : nv = sc 𝔳 c * t * nv⁻¹ := by rw [eq_mul_inv_of_mul_eq hnt.symm]; group
    have := congrArg Units.val e
    rwa [coe_units_map_ev, Units.val_mul, Units.val_mul, coe_sc, coe_units_map_ev_inv] at this

  have hcR : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (c : 𝕂) : Lv) ∈ Submodule.localBox R 𝔳 := by
    rw [u1]; exact mul_mem_localBox R 𝔳 hmulR (mul_mem_localBox R 𝔳 hmulR hnR hnR) htiR

  have hqcR : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ϖ * ϖ * (c : 𝕂)⁻¹) : Lv) ∈ Submodule.localBox R 𝔳 := by
    have hmem := mul_mem_localBox R 𝔳 hmulR (mul_mem_localBox R 𝔳 hmulR htR hqni) hqni
    convert hmem using 1
    have u2' : (t : Lv) * (ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹) * ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹)) = ((c : 𝕂)⁻¹) • (1 : Lv) := by
      rw [← mul_assoc, ← u2, htm]
    simp only [htm, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, mul_assoc, u2']
  have hvq2c : Valued.v (ϖ * ϖ * (c : 𝕂)⁻¹) = WithZero.exp (-2 - m) := by
    rw [map_mul, map_mul, map_inv₀, valued_q, hm, ← WithZero.exp_add, ← WithZero.exp_neg, ← WithZero.exp_add,
      show (-1 : ℤ) + -1 + -m = -2 - m by omega]

  by_contra hne
  rcases lt_trichotomy 0 m with hpos | hzero | hneg
  · exact false_of_scalar_mem q hq R hRo n hnH hm (by omega) hcR
  ·
    subst hzero
    apply false_of_ev_n_inv_mem q hq R hRo n hnH
    rw [u3]
    refine mul_one_tmul_mem_localBox R 𝔳 (mul_mem_localBox R 𝔳 hmulR hnR htiR) ?_
    exact inv_mem_integers_of_valued_eq_one q hq (by rw [hm, WithZero.exp_zero])
  · rcases lt_trichotomy m (-2) with hlt | heq | hgt
    · exact false_of_scalar_mem q hq R hRo n hnH hvq2c (by omega) hqcR
    ·
      subst heq
      apply false_of_qinv_ev_n_mem q hq R hRo n hnH
      have hunit : Valued.v (ϖ⁻¹ * ϖ⁻¹ * (c : 𝕂)) = 1 := by
        rw [map_mul, map_mul, map_inv₀, valued_q, hm, ← WithZero.exp_neg, ← WithZero.exp_add,
          ← WithZero.exp_add, ← WithZero.exp_zero]
        congr 1
      have hmem : ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ϖ⁻¹ * ϖ⁻¹ * (c : 𝕂))) * (t : Lv) *
          (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (ϖ : 𝕂)) * ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹)) ∈ Submodule.localBox R 𝔳 :=
        mul_mem_localBox R 𝔳 hmulR
          (one_tmul_mul_mem_localBox R 𝔳 htR (mem_integers_of_valued_le_one q hq hunit.le)) hqni
      convert hmem using 1
      rw [u4]
      simp only [htm, smul_mul_assoc, mul_smul_comm, smul_smul, one_mul, mul_one, mul_assoc]
      congr 1
      field_simp
    · obtain rfl : m = -1 := by omega
      exact hne hm

include hRo hnH in

theorem sq_mem_stab_R {c : (𝕂)ˣ} {t : (Lv)ˣ} (ht : t ∈ Submodule.localBoxUnits (meetOrder R n) 𝔳)
    (hnt : nv * nv = sc 𝔳 c * t) : zq⁻¹ * (n * n) ∈ Submodule.finiteIdeleStabilizer R := by
  have hm := valued_c_eq q hq R hRo n hnH ht hnt
  have hmulR : ∀ x y : ℍ[ℚ, a, b], x ∈ R → y ∈ R → x * y ∈ R := fun x y hx hy => hRo.mul_mem hx hy
  have hunit : Valued.v ((((qK q hq)⁻¹ * c : (𝕂)ˣ)) : 𝕂) = 1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, coe_qK, valued_q, hm, ← WithZero.exp_neg,
      ← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1
  have he : (((qK q hq)⁻¹ * c : (𝕂)ˣ) : 𝕂) ∈ 𝓞v := mem_integers_of_valued_le_one q hq hunit.le
  have hei : ((((qK q hq)⁻¹ * c)⁻¹ : (𝕂)ˣ) : 𝕂) ∈ 𝓞v := by
    rw [Units.val_inv_eq_inv_val]; exact inv_mem_integers_of_valued_eq_one q hq hunit
  have hE : E (zq⁻¹ * (n * n)) = sc 𝔳 ((qK q hq)⁻¹ * c) * t := by
    rw [map_mul, map_inv, map_mul, E_zq, hnt, sc_mul, ← sc_inv, mul_assoc]
  have htR : (t : Lv) ∈ Submodule.localBox R 𝔳 := localBox_mono 𝔳 (meetOrder_le R n) ht.1
  have htiR : ((t⁻¹ : (Lv)ˣ) : Lv) ∈ Submodule.localBox R 𝔳 := localBox_mono 𝔳 (meetOrder_le R n) ht.2
  rw [mem_stab_iff_forall hRo]
  intro w
  by_cases hw : w = 𝔳
  · subst hw
    rw [← coe_units_map_ev, ← coe_units_map_ev_inv, hE, mul_inv_rev, sc_inv, Units.val_mul, Units.val_mul,
      coe_sc, coe_sc]
    exact ⟨one_tmul_mul_mem_localBox R _ htR he, mul_one_tmul_mem_localBox R _ htiR hei⟩
  · have hq1 : algebraMap ℚ (w.adicCompletion ℚ) (q : ℚ) ∈ w.adicCompletionIntegers ℚ := by
      have := algebraMap_zpow_mem_integers_of_ne q hq w hw 1
      rwa [zpow_one] at this
    have hq2 : algebraMap ℚ (w.adicCompletion ℚ) (q : ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
      have := algebraMap_zpow_mem_integers_of_ne q hq w hw (-1)
      rwa [zpow_neg_one] at this
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Units.val_mul, coe_ratIdele_inv, map_mul, map_mul, ev_algebraMap]
      exact one_tmul_mul_mem_localBox R w
        (mul_mem_localBox R w hmulR (ev_n_mem q hq R hRo n hnH w) (ev_n_mem q hq R hRo n hnH w)) hq2
    · rw [mul_inv_rev, mul_inv_rev, inv_inv, Units.val_mul, Units.val_mul, coe_ratIdele, map_mul, map_mul,
        ev_algebraMap]
      exact mul_one_tmul_mem_localBox R w
        (mul_mem_localBox R w hmulR (ev_n_inv_mem q hq R hRo n hnH w hw) (ev_n_inv_mem q hq R hRo n hnH w hw)) hq1

include hRo hnH in

theorem sq_mem_stab_S {c : (𝕂)ˣ} {t : (Lv)ˣ} (ht : t ∈ Submodule.localBoxUnits (meetOrder R n) 𝔳)
    (hnt : nv * nv = sc 𝔳 c * t) : zq⁻¹ * (n * n) ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
  refine mem_stab_S_of R hRo n _ (sq_mem_stab_R q hq R hRo n hnH ht hnt) ?_
  have e : n⁻¹ * (zq⁻¹ * (n * n)) * n = zq⁻¹ * (n * n) := by
    rw [mul_ratIdele_inv_mul, inv_mul_cancel_left, mul_assoc]
  rw [e]
  exact sq_mem_stab_R q hq R hRo n hnH ht hnt

variable {N : ℕ} [Fact q.Prime] (hR : IsEichlerOrder R N) (hqN : ¬ q ∣ N) {q' : ℕ} [Fact q'.Prime] (hqq' : q' ≠ q)
  (hdef : IsDefiniteRamifiedExactlyAt a b q')

include hR hqN hqq' hdef hnH in

theorem exists_eq_of_mem_uHeckeSet (h : (𝔹)ˣ) (hh : h ∈ uHeckeSet R n q) :
    ∃ g ∈ Submodule.finiteIdeleStabilizer R, h = g * n * (zq⁻¹ * (n * n))⁻¹ := by
  obtain ⟨g, hg, hgn⟩ :=
    CerednikDrinfeld.exists_mem_finiteIdeleStabilizer_mul_eq_natCast_smul_of_mem_uHeckeSet q q' hqq' hdef R hR hqN
      n hnH h hh
  refine ⟨g, hg, ?_⟩
  have hh' : h * n = zq * g := by
    apply Units.ext
    rw [hgn, Units.val_mul, coe_ratIdele]
    exact Algebra.smul_def (q : ℚ) (g : 𝔹)
  have e1 : h = zq * (g * n⁻¹) := by rw [← mul_assoc]; exact eq_mul_inv_of_mul_eq hh'
  rw [e1, ratIdele_comm]
  group

include hR hqN hqq' hdef hnH hRo in

theorem claim2 (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (s₀ : (𝔹)ˣ) (hs₀ : s₀ ∈ Submodule.finiteIdeleStabilizer (meetOrder R n))
    (hs₀' : ∀ h ∈ uHeckeSet R n q, ∃ g ∈ Submodule.finiteIdeleStabilizer R, h = g * n * s₀⁻¹)
    (h : (𝔹)ˣ) (hh : h ∈ uHeckeSet R n q) :
    ∃ u ∈ Submodule.finiteIdeleStabilizer R, u ∉ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧
      h⁻¹ * (u * n) ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
  obtain ⟨g, hg, hs⟩ := hs₀' h hh
  refine ⟨g, hg, fun hgS => ?_, ?_⟩
  · apply (CerednikDrinfeld.uHeckeSet_cosetDictionary_of_mem_primeHeckeSet q q' hqq' hdef R hR hqN n hnH).2.2.1 h hh
    rw [hs]
    have e : (g * n * s₀⁻¹)⁻¹ * n = s₀ * (n⁻¹ * g⁻¹ * n) := by group
    rw [e]
    exact stab_S_le R hRo n (mul_mem hs₀ ((inv_mul_mul_mem_stab_S_iff R hRo n hnorm _).2 (inv_mem hgS)))
  · rw [hs]
    have e : (g * n * s₀⁻¹)⁻¹ * (g * n) = s₀ := by group
    rw [e]
    exact hs₀

include hRo hnH in

theorem mul_mem_primeHeckeSet_of_mem_stab {u : (𝔹)ˣ} (hu : u ∈ Submodule.finiteIdeleStabilizer R) :
    u * n ∈ primeHeckeSet R q := by
  obtain ⟨huR, huiR⟩ := mem_box_of_mem_stab hRo hu
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]; exact box_mul_mem hRo huR hnH.1
  · rw [mul_inv_rev, Units.val_mul, ← smul_mul_assoc]; exact box_mul_mem hRo hnH.2.1 huiR
  · intro h
    apply hnH.2.2.1
    rw [show n⁻¹ = (u * n)⁻¹ * u by group, Units.val_mul]
    exact box_mul_mem hRo h huR
  · intro h
    apply hnH.2.2.2
    have e : (q : ℚ)⁻¹ • (n : 𝔹) = ((u⁻¹ : (𝔹)ˣ) : 𝔹) * ((q : ℚ)⁻¹ • ((u * n : (𝔹)ˣ) : 𝔹)) := by
      rw [Units.val_mul, mul_smul_comm, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e]
    exact box_mul_mem hRo huiR h

include hR hqN hqq' hdef hnH hRo in

theorem claim3 (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (s₀ : (𝔹)ˣ) (hs₀ : s₀ ∈ Submodule.finiteIdeleStabilizer (meetOrder R n))
    (hs₀' : ∀ h ∈ uHeckeSet R n q, ∃ g ∈ Submodule.finiteIdeleStabilizer R, h = g * n * s₀⁻¹)
    (u : (𝔹)ˣ) (hu : u ∈ Submodule.finiteIdeleStabilizer R) (huS : u ∉ Submodule.finiteIdeleStabilizer (meetOrder R n)) :
    ∃ h ∈ uHeckeSet R n q, h⁻¹ * (u * n) ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := by
  have hnu : n⁻¹ * u * n ∉ Submodule.finiteIdeleStabilizer R := fun h' => huS (mem_stab_S_of R hRo n u hu h')
  have hg₀ : u * n ∈ primeHeckeSet R q := mul_mem_primeHeckeSet_of_mem_stab q R hRo n hnH hu
  have hg₀' : (u * n)⁻¹ * n ∉ Submodule.finiteIdeleStabilizer R := by
    intro h'
    apply hnu
    rw [show n⁻¹ * u * n = ((u * n)⁻¹ * n)⁻¹ by group]
    exact inv_mem h'
  obtain ⟨h, hh, hh'⟩ :=
    (CerednikDrinfeld.uHeckeSet_cosetDictionary_of_mem_primeHeckeSet q q' hqq' hdef R hR hqN n hnH).2.2.2.2 (u * n)
      hg₀ hg₀'
  obtain ⟨g, hg, hs⟩ := hs₀' h hh
  refine ⟨h, hh, ?_⟩
  have h1 : u⁻¹ * g ∈ Submodule.finiteIdeleStabilizer R := mul_mem (inv_mem hu) hg
  have h2 : n⁻¹ * (u⁻¹ * g) * n ∈ Submodule.finiteIdeleStabilizer R := by
    have e : n⁻¹ * (u⁻¹ * g) * n = (u * n)⁻¹ * h * s₀ := by rw [hs]; group
    rw [e]
    exact mul_mem hh' (stab_S_le R hRo n hs₀)
  have h3 : u⁻¹ * g ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) := mem_stab_S_of R hRo n _ h1 h2
  have h4 : n⁻¹ * (u⁻¹ * g)⁻¹ * n ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) :=
    (inv_mul_mul_mem_stab_S_iff R hRo n hnorm _).2 (inv_mem h3)
  have e : h⁻¹ * (u * n) = s₀ * (n⁻¹ * (u⁻¹ * g)⁻¹ * n) := by rw [hs]; group
  rw [e]
  exact mul_mem hs₀ h4

end Frame

end UHeckeCosets

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (q : ℕ) [Fact q.Prime]
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hR : IsEichlerOrder R N) (hqN : ¬ q ∣ N) {q' : ℕ} [Fact q'.Prime] (hqq' : q' ≠ q)
    (hdef : IsDefiniteRamifiedExactlyAt a b q') (hnH : n ∈ primeHeckeSet R q)
    (hn : IsEichlerOrder (meetOrder R n) (N * q))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n) :
    (∀ u : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ,
        u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n) ↔
          n * u * n⁻¹ ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) ∧
    (∀ h ∈ uHeckeSet R n q, ∃ u ∈ Submodule.finiteIdeleStabilizer R,
        u ∉ Submodule.finiteIdeleStabilizer (meetOrder R n) ∧
          h⁻¹ * (u * n) ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) ∧
    (∀ u ∈ Submodule.finiteIdeleStabilizer R, u ∉ Submodule.finiteIdeleStabilizer (meetOrder R n) →
        ∃ h ∈ uHeckeSet R n q, h⁻¹ * (u * n) ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) := by
  have hq : q.Prime := Fact.out
  have hRo : IsOrder R := hR.isOrder
  have hSo : IsOrder (meetOrder R n) := UHeckeCosets.isOrder_S R hRo n
  haveI : NeZero N := ⟨fun h0 => hqN (h0 ▸ dvd_zero q)⟩
  have hAL := CosetGraph.mul_self_mem_level_and_not_mem_level_and_mem_inf_conj_iff_of_mem_primeHeckeSet hdef hR
    hqq'.symm hqN (UHeckeCosets.place q hq) (UHeckeCosets.q_mem_asIdeal q hq) hnH hnorm
  have hlev : Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (UHeckeCosets.place q hq)).toRingHom.toMonoidHom n *
      Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (UHeckeCosets.place q hq)).toRingHom.toMonoidHom n ∈
        CosetGraph.level (meetOrder R n) (UHeckeCosets.place q hq) := by
    refine (hAL.2.2 _).1 ⟨hAL.1, ?_⟩
    rw [show ∀ x : (CosetGraph.Loc a b (UHeckeCosets.place q hq))ˣ, x⁻¹ * (x * x) * x = x * x from fun x => by group]
    exact hAL.1
  obtain ⟨c, t, ht, hnt⟩ := (UHeckeCosets.mem_level_iff hSo _ _).1 hlev
  have hs₀ := UHeckeCosets.sq_mem_stab_S q hq R hRo n hnH ht hnt
  refine ⟨fun u => UHeckeCosets.mem_stab_S_iff_conj R hRo n hnorm u, fun h hh => ?_, fun u hu huS => ?_⟩
  · exact UHeckeCosets.claim2 q R hRo n hnH hR hqN hqq' hdef hnorm _ hs₀
      (UHeckeCosets.exists_eq_of_mem_uHeckeSet q hq R n hnH hR hqN hqq' hdef) h hh
  · exact UHeckeCosets.claim3 q R hRo n hnH hR hqN hqq' hdef hnorm _ hs₀
      (UHeckeCosets.exists_eq_of_mem_uHeckeSet q hq R n hnH hR hqN hqq' hdef) u hu huS

end
end S_CerednikDrinfeld_uHeckeSet_cosets_eq_finiteIdeleStabilizer_mul_of_conjByFiniteIdele_meetOrder_eq
end P2MW
export P2MW.S_CerednikDrinfeld_uHeckeSet_cosets_eq_finiteIdeleStabilizer_mul_of_conjByFiniteIdele_meetOrder_eq (solution)
