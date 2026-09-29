-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.natCard_stabilizer_dart_eq_natCard_isUnitOf_conjByFiniteIdele_meetOrder_div_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/d84b7037-242f-5b51-a1d5-9b40ad3a11c9

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_CerednikDrinfeld_CosetGraph_mul_self_mem_level_and_not_mem_level_and_mem_inf_conj_iff_of_mem_primeHeckeSet
import Theorems.Thm_CerednikDrinfeld_CosetGraph_exists_coe_eq_smul_one_of_forall_smul_vert_eq
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_finite_isUnitOf_and_nrd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_natCard_stabilizer_dart_eq_natCard_isUnitOf_conjByFiniteIdele_meetOrder_div_two
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

namespace R1CDWidth

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

theorem exists_zpow_mul_valued_eq_one {c : 𝕂} (hc : c ≠ 0) :
    ∃ m : ℤ, Valued.v (((q : ℕ) : 𝕂) ^ m * c) = 1 := by
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v c = WithZero.exp k :=
    ⟨WithZero.log (Valued.v c), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hc)).symm⟩
  refine ⟨k, ?_⟩
  rw [map_mul, valued_zpow, hk, ← WithZero.exp_add, ← WithZero.exp_zero]
  congr 1
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

theorem ev_tmul_one (w : HeightOneSpectrum (𝓞 ℚ)) (z : ℍ[ℚ, a, b]) :
    ev w (z ⊗ₜ[ℚ] (1 : 𝔸f)) = z ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [Submodule.finiteAdeleEvalAt_tmul]; rfl

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

theorem mem_conj_iff (Λ : Submodule ℤ ℍ[ℚ, a, b]) (g : (𝔹)ˣ) (y : ℍ[ℚ, a, b]) :
    y ∈ Submodule.conjByFiniteIdele Λ g ↔
      ((g⁻¹ : (𝔹)ˣ) : 𝔹) * (y ⊗ₜ[ℚ] (1 : 𝔸f)) * (g : 𝔹) ∈ Submodule.finiteAdeleBox Λ := by
  rw [Submodule.mem_conjByFiniteIdele_iff, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxy⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      AddMonoidHom.coe_mulRight] at hxy
    rw [← hxy]
    have : ((g⁻¹ : (𝔹)ˣ) : 𝔹) * ((g : 𝔹) * x * ((g⁻¹ : (𝔹)ˣ) : 𝔹)) * (g : 𝔹) = x := by
      rw [← mul_assoc, ← mul_assoc, Units.inv_mul, one_mul, mul_assoc, Units.inv_mul, mul_one]
    rw [this]; exact hx
  · intro h
    refine ⟨_, h, ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft,
      AddMonoidHom.coe_mulRight]
    rw [← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]

theorem mem_conj_iff_forall {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (g : (𝔹)ˣ) (y : ℍ[ℚ, a, b]) :
    y ∈ Submodule.conjByFiniteIdele Λ g ↔
      ∀ w, ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) * (y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) * ev w (g : 𝔹) ∈
        Submodule.localBox Λ w := by
  rw [mem_conj_iff, mem_box_iff hΛ]
  refine forall_congr' fun w => ?_
  rw [map_mul, map_mul, ev_tmul_one]

theorem mem_localBox_conj_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (β : (𝔹)ˣ)
    (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    x ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ β) w ↔
      ev w ((β⁻¹ : (𝔹)ˣ) : 𝔹) * x * ev w (β : 𝔹) ∈ Submodule.localBox Λ w := by
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff Λ hΛ.fg hΛ.spanTop β w x]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : ev w ((β⁻¹ : (𝔹)ˣ) : 𝔹) * (ev w (β : 𝔹) * y * ev w ((β⁻¹ : (𝔹)ˣ) : 𝔹)) * ev w (β : 𝔹) =
        (ev w ((β⁻¹ : (𝔹)ˣ) : 𝔹) * ev w (β : 𝔹)) * y * (ev w ((β⁻¹ : (𝔹)ˣ) : 𝔹) * ev w (β : 𝔹)) := by
      noncomm_ring
    rw [e, ev_units_inv_mul, one_mul, mul_one]
    exact hy
  · intro h
    refine ⟨_, h, ?_⟩
    have e : ev w (β : 𝔹) * (ev w ((β⁻¹ : (𝔹)ˣ) : 𝔹) * x * ev w (β : 𝔹)) * ev w ((β⁻¹ : (𝔹)ˣ) : 𝔹) =
        (ev w (β : 𝔹) * ev w ((β⁻¹ : (𝔹)ˣ) : 𝔹)) * x * (ev w (β : 𝔹) * ev w ((β⁻¹ : (𝔹)ˣ) : 𝔹)) := by
      noncomm_ring
    rw [e, ev_units_mul_inv, one_mul, mul_one]

end Global

section Coset

variable {a b : ℚ}

open QuaternionAlgebra CerednikDrinfeld

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

theorem mem_boxUnits_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (w : HeightOneSpectrum (𝓞 ℚ))
    (u : (CosetGraph.Loc a b w)ˣ) :
    u ∈ boxUnits hΛ w ↔ (u : CosetGraph.Loc a b w) ∈ Submodule.localBox Λ w ∧
      ((u⁻¹ : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) ∈ Submodule.localBox Λ w :=
  Iff.rfl

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

theorem localBoxUnits_le_level (Λ : Submodule ℤ ℍ[ℚ, a, b]) (w : HeightOneSpectrum (𝓞 ℚ))
    {t : (CosetGraph.Loc a b w)ˣ} (ht : t ∈ Submodule.localBoxUnits Λ w) : t ∈ CosetGraph.level Λ w :=
  Subgroup.mem_sup_left (Subgroup.subset_closure ht)

theorem sc_mem_level (Λ : Submodule ℤ ℍ[ℚ, a, b]) (w : HeightOneSpectrum (𝓞 ℚ)) (c : (w.adicCompletion ℚ)ˣ) :
    (sc w c : (CosetGraph.Loc a b w)ˣ) ∈ CosetGraph.level Λ w :=
  Subgroup.mem_sup_right (sc_mem_scalarUnits w c)

def ratUnits : ℚˣ →* (ℍ[ℚ, a, b])ˣ := Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom

theorem coe_ratUnits (u : ℚˣ) : ((ratUnits u : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = algebraMap ℚ ℍ[ℚ, a, b] (u : ℚ) :=
  rfl

theorem coe_toLoc (w : HeightOneSpectrum (𝓞 ℚ)) (γ : (ℍ[ℚ, a, b])ˣ) :
    ((CosetGraph.toLoc w γ : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) =
      (γ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) :=
  rfl

theorem coe_toLoc_inv (w : HeightOneSpectrum (𝓞 ℚ)) (γ : (ℍ[ℚ, a, b])ˣ) :
    (((CosetGraph.toLoc w γ)⁻¹ : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Loc a b w) =
      ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) := by
  rw [← map_inv]; rfl

theorem toLoc_ratUnits (w : HeightOneSpectrum (𝓞 ℚ)) (u : ℚˣ) :
    CosetGraph.toLoc w (ratUnits (a := a) (b := b) u) =
      sc w (Units.map (algebraMap ℚ (w.adicCompletion ℚ)).toMonoidHom u) := by
  apply Units.ext
  rw [coe_toLoc, coe_ratUnits, coe_sc, Units.coe_map, ← Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.algebraMap_apply']
  rfl

theorem toLoc_ratUnits_mul_coe_eq (Λ : Submodule ℤ ℍ[ℚ, a, b]) (w : HeightOneSpectrum (𝓞 ℚ)) (u : ℚˣ)
    (g : (CosetGraph.Loc a b w)ˣ) :
    ((CosetGraph.toLoc w (ratUnits (a := a) (b := b) u) * g : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Vert Λ w) =
      ((g : (CosetGraph.Loc a b w)ˣ) : CosetGraph.Vert Λ w) := by
  rw [toLoc_ratUnits, sc_mul_comm]
  refine QuotientGroup.eq.2 ?_
  rw [mul_inv_rev, inv_mul_cancel_right]
  exact inv_mem (sc_mem_level Λ w _)

theorem ratUnits_smul_vert (Λ : Submodule ℤ ℍ[ℚ, a, b]) (w : HeightOneSpectrum (𝓞 ℚ)) (u : ℚˣ)
    (x : CosetGraph.Vert Λ w) : (ratUnits (a := a) (b := b) u) • x = x := by
  induction x using QuotientGroup.induction_on with
  | H g => rw [CosetGraph.smul_vert_mk]; exact toLoc_ratUnits_mul_coe_eq Λ w u g

end Coset

section Frame

variable {a b : ℚ} (r : ℕ) (hr : r.Prime)

open QuaternionAlgebra CerednikDrinfeld

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]
local notation "𝔳" => place r hr
local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place r hr)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place r hr)
local notation "ϖ" => ((r : ℕ) : HeightOneSpectrum.adicCompletion ℚ (place r hr))
set_option quotPrecheck false in
local notation "Lv" => CerednikDrinfeld.CosetGraph.Loc a b (place r hr)

variable (R : Submodule ℤ ℍ[ℚ, a, b]) (hRo : IsOrder R)
  (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  (hnR : ((n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
    Submodule.finiteAdeleBox R)
  (hnR' : (r : ℚ) • ((n⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) ∈
    Submodule.finiteAdeleBox R)
  (z : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  (hz : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ place r hr →
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
      ((z : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)

set_option quotPrecheck false in
local notation "zv" => (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (place r hr)).toRingHom.toMonoidHom z :
  (CosetGraph.Loc a b (place r hr))ˣ)

include hRo in
omit hr in
theorem isOrder_conj : IsOrder (Submodule.conjByFiniteIdele R n) :=
  QuaternionAlgebra.IsOrder.conjByFiniteIdele R hRo n

include hRo in
omit hr in
theorem isOrder_S : IsOrder (meetOrder R n) :=
  hRo.inf (QuaternionAlgebra.IsOrder.conjByFiniteIdele R hRo n)

include hRo in
omit hr in
theorem isOrder_O : IsOrder (Submodule.conjByFiniteIdele (meetOrder R n) z) :=
  QuaternionAlgebra.IsOrder.conjByFiniteIdele _ (isOrder_S R hRo n) z

include hz in
omit R n in
theorem ev_z_inv (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) : ev w ((z⁻¹ : (𝔹)ˣ) : 𝔹) = 1 := by
  have := ev_units_inv_mul w z
  rwa [hz w hw, mul_one] at this

include hRo hnR hnR' in
omit z in

theorem ev_n_mem (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) :
    ev w (n : 𝔹) ∈ Submodule.localBox R w ∧ ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := by
  refine ⟨(mem_box_iff hRo _).1 hnR w, ?_⟩
  have h := (mem_box_iff hRo _).1 hnR' w
  rw [map_smul, ratCast_smul_eq_one_tmul_mul] at h
  have e : ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) ((r : ℚ) ^ (-1 : ℤ))) *
      (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) (r : ℚ)) * ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹)) := by
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← map_mul, zpow_neg, zpow_one,
      inv_mul_cancel₀ (by exact_mod_cast hr.ne_zero : (r : ℚ) ≠ 0), map_one, ← Algebra.TensorProduct.one_def,
      one_mul]
  rw [e]
  exact one_tmul_mul_mem_localBox R w h (algebraMap_zpow_mem_integers_of_ne r hr w hw (-1))

include hRo in
omit hr z in

theorem mem_localBox_S_iff (w : HeightOneSpectrum (𝓞 ℚ)) (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    x ∈ Submodule.localBox (meetOrder R n) w ↔
      x ∈ Submodule.localBox R w ∧ ev w ((n⁻¹ : (𝔹)ˣ) : 𝔹) * x * ev w (n : 𝔹) ∈ Submodule.localBox R w := by
  have hR' := isOrder_conj R hRo n
  rw [meetOrder, Submodule.localBox_inf R _ hRo.fg hRo.spanTop hR'.fg hR'.spanTop w, AddSubgroup.mem_inf,
    mem_localBox_conj_iff hRo n w x]

omit hr hRo z in
theorem localBox_S_le (w : HeightOneSpectrum (𝓞 ℚ)) : Submodule.localBox (meetOrder R n) w ≤ Submodule.localBox R w :=
  localBox_mono w inf_le_left

include hRo hnR hnR' in
omit z in

theorem localBox_R_le_S (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) :
    Submodule.localBox R w ≤ Submodule.localBox (meetOrder R n) w := by
  intro x hx
  have hmul : ∀ x y : ℍ[ℚ, a, b], x ∈ R → y ∈ R → x * y ∈ R := fun x y hx hy => hRo.mul_mem hx hy
  exact (mem_localBox_S_iff R hRo n w x).2 ⟨hx, mul_mem_localBox R w hmul
    (mul_mem_localBox R w hmul (ev_n_mem r hr R hRo n hnR hnR' w hw).2 hx) (ev_n_mem r hr R hRo n hnR hnR' w hw).1⟩

include hRo hz in
omit hnR hnR' in

theorem mem_O_iff (y : ℍ[ℚ, a, b]) :
    y ∈ Submodule.conjByFiniteIdele (meetOrder R n) z ↔
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ 𝔳 →
        y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox (meetOrder R n) w) ∧
      ((zv⁻¹ : (Lv)ˣ) : Lv) * (y ⊗ₜ[ℚ] (1 : 𝕂)) * (zv : Lv) ∈ Submodule.localBox (meetOrder R n) 𝔳 := by
  rw [mem_conj_iff_forall (isOrder_S R hRo n) z y]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, h 𝔳⟩
    have := h w
    rwa [hz w hw, ev_z_inv r hr z hz w hw, one_mul, mul_one] at this
  · rintro ⟨h1, h2⟩ w
    by_cases hw : w = 𝔳
    · subst hw; exact h2
    · rw [hz w hw, ev_z_inv r hr z hz w hw, one_mul, mul_one]; exact h1 w hw

include hRo hz in
omit hnR hnR' in
theorem unit_mem_awayUnits (u : (ℍ[ℚ, a, b])ˣ)
    (hu : (u : ℍ[ℚ, a, b]) ∈ Submodule.conjByFiniteIdele (meetOrder R n) z)
    (hui : ((u⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Submodule.conjByFiniteIdele (meetOrder R n) z) :
    u ∈ CosetGraph.awayUnits R 𝔳 ∧
      zv⁻¹ * CosetGraph.toLoc 𝔳 u * zv ∈ CosetGraph.level (meetOrder R n) 𝔳 := by
  obtain ⟨h1, h2⟩ := (mem_O_iff r hr R hRo n z hz _).1 hu
  obtain ⟨h1', h2'⟩ := (mem_O_iff r hr R hRo n z hz _).1 hui
  refine ⟨?_, ?_⟩
  · rw [CosetGraph.awayUnits, Subgroup.mem_iInf]
    intro w
    rw [Subgroup.mem_iInf]
    intro hw
    rw [Subgroup.mem_comap]
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, coe_toLoc]; exact localBox_S_le R n w (h1 w hw)
    · rw [SetLike.mem_coe, coe_toLoc_inv]; exact localBox_S_le R n w (h1' w hw)
  · apply localBoxUnits_le_level
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, Units.val_mul, Units.val_mul, coe_toLoc]; exact h2
    · have e : (zv⁻¹ * CosetGraph.toLoc 𝔳 u * zv)⁻¹ = zv⁻¹ * (CosetGraph.toLoc 𝔳 u)⁻¹ * zv := by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
      rw [SetLike.mem_coe, e, Units.val_mul, Units.val_mul, coe_toLoc_inv]; exact h2'

omit hr in
theorem coe_ratUnits_zpow_mul_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (u : ℚˣ) (m : ℤ) (γ : (ℍ[ℚ, a, b])ˣ) :
    ((ratUnits (a := a) (b := b) u ^ m * γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) ((u : ℚ) ^ m)) *
        ((γ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) := by
  rw [Units.val_mul, ← map_zpow, coe_ratUnits, Units.val_zpow_eq_zpow_val,
    ← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul]

omit hr in
theorem coe_ratUnits_zpow_mul_inv_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (u : ℚˣ) (m : ℤ) (γ : (ℍ[ℚ, a, b])ˣ) :
    (((ratUnits (a := a) (b := b) u ^ m * γ)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) ((u : ℚ) ^ (-m))) *
        (((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) := by
  rw [mul_inv_rev, ← zpow_neg, Units.val_mul, ← map_zpow, coe_ratUnits, Units.val_zpow_eq_zpow_val,
    one_tmul_mul_comm, ← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]

omit hr in
theorem conj_one_tmul_mul (w : HeightOneSpectrum (𝓞 ℚ)) (s : w.adicCompletion ℚ)
    (p p' x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    p * (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s) * x) * p' = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s) * (p * x * p') := by
  rw [← mul_assoc p, ← one_tmul_mul_comm w s p]
  simp only [mul_assoc]

include hRo in
omit n z in

theorem toLoc_mem_boxUnits_of_mem_awayUnits {γ : (ℍ[ℚ, a, b])ˣ} (hγ : γ ∈ CosetGraph.awayUnits R 𝔳)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) : CosetGraph.toLoc w γ ∈ boxUnits hRo w := by
  rw [CosetGraph.awayUnits, Subgroup.mem_iInf] at hγ
  have h := hγ w
  rw [Subgroup.mem_iInf] at h
  have h' := h hw
  rwa [Subgroup.mem_comap, closure_localBoxUnits hRo] at h'

include hRo hnR hnR' hz in

theorem exists_zpow_mul_mem (γ : (ℍ[ℚ, a, b])ˣ) (hγ : γ ∈ CosetGraph.awayUnits R 𝔳)
    (hk : zv⁻¹ * CosetGraph.toLoc 𝔳 γ * zv ∈ CosetGraph.level (meetOrder R n) 𝔳) :
    ∃ m : ℤ,
      ((ratUnits (Units.mk0 (r : ℚ) (by exact_mod_cast hr.ne_zero)) ^ m * γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈
          Submodule.conjByFiniteIdele (meetOrder R n) z ∧
        (((ratUnits (Units.mk0 (r : ℚ) (by exact_mod_cast hr.ne_zero)) ^ m * γ)⁻¹ : (ℍ[ℚ, a, b])ˣ) :
            ℍ[ℚ, a, b]) ∈ Submodule.conjByFiniteIdele (meetOrder R n) z := by
  have hS := isOrder_S R hRo n
  obtain ⟨c, t, ht, hkt⟩ := (mem_level_iff hS 𝔳 _).1 hk
  obtain ⟨m, hm⟩ := exists_zpow_mul_valued_eq_one r hr (c := (c : 𝕂)) c.ne_zero
  have he : ϖ ^ m * (c : 𝕂) ∈ 𝓞v := mem_integers_of_valued_le_one r hr hm.le
  have hei : (ϖ ^ m * (c : 𝕂))⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one r hr hm

  have hprod : ((zv⁻¹ : (Lv)ˣ) : Lv) * ((γ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝕂)) * (zv : Lv) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (c : 𝕂)) * (t : Lv) := by
    have := congrArg Units.val hkt
    rwa [Units.val_mul, Units.val_mul, Units.val_mul, coe_sc, coe_toLoc] at this
  have hprod' : ((zv⁻¹ : (Lv)ˣ) : Lv) * (((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝕂)) * (zv : Lv) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((c⁻¹ : (𝕂)ˣ) : 𝕂)) * ((t⁻¹ : (Lv)ˣ) : Lv) := by
    have e : (zv⁻¹ * CosetGraph.toLoc 𝔳 γ * zv)⁻¹ = zv⁻¹ * (CosetGraph.toLoc 𝔳 γ)⁻¹ * zv := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
    have := congrArg (fun x : (Lv)ˣ => ((x⁻¹ : (Lv)ˣ) : Lv)) hkt
    rwa [e, mul_inv_rev, sc_inv, ← sc_mul_comm, Units.val_mul, Units.val_mul, Units.val_mul, coe_sc,
      coe_toLoc_inv] at this
  have hRunit : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ 𝔳 → CosetGraph.toLoc w γ ∈ boxUnits hRo w :=
    fun w hw => toLoc_mem_boxUnits_of_mem_awayUnits r hr R hRo hγ w hw
  refine ⟨m, (mem_O_iff r hr R hRo n z hz _).2 ⟨fun w hw => ?_, ?_⟩, (mem_O_iff r hr R hRo n z hz _).2 ⟨fun w hw => ?_, ?_⟩⟩
  · rw [coe_ratUnits_zpow_mul_tmul]
    apply localBox_R_le_S r hr R hRo n hnR hnR' w hw
    have h := (hRunit w hw).1
    rw [coe_toLoc] at h
    exact one_tmul_mul_mem_localBox R w h (algebraMap_zpow_mem_integers_of_ne r hr w hw m)
  · rw [coe_ratUnits_zpow_mul_tmul, conj_one_tmul_mul, hprod, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, Units.val_mk0, algebraMap_zpow_place]
    exact one_tmul_mul_mem_localBox _ _ ht.1 he
  · rw [coe_ratUnits_zpow_mul_inv_tmul]
    apply localBox_R_le_S r hr R hRo n hnR hnR' w hw
    have h := (hRunit w hw).2
    rw [coe_toLoc_inv] at h
    exact one_tmul_mul_mem_localBox R w h (algebraMap_zpow_mem_integers_of_ne r hr w hw (-m))
  · rw [coe_ratUnits_zpow_mul_inv_tmul, conj_one_tmul_mul, hprod', ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, Units.val_mk0, algebraMap_zpow_place]
    have e : ϖ ^ (-m) * ((c⁻¹ : (𝕂)ˣ) : 𝕂) = (ϖ ^ m * (c : 𝕂))⁻¹ := by
      rw [mul_inv, zpow_neg, Units.val_inv_eq_inv_val]
    rw [e]
    exact one_tmul_mul_mem_localBox _ _ ht.2 hei

include hRo in
omit n z in
theorem ratUnits_zpow_mem_awayUnits (m : ℤ) :
    ratUnits (a := a) (b := b) (Units.mk0 (r : ℚ) (by exact_mod_cast hr.ne_zero)) ^ m ∈ CosetGraph.awayUnits R 𝔳 := by
  rw [CosetGraph.awayUnits, Subgroup.mem_iInf]
  intro w
  rw [Subgroup.mem_iInf]
  intro hw
  rw [Subgroup.mem_comap, ← map_zpow, toLoc_ratUnits]
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, coe_sc, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    exact tmul_mem_localBox R w hRo.one_mem (algebraMap_zpow_mem_integers_of_ne r hr w hw m)
  · rw [SetLike.mem_coe, sc_inv, ← map_inv, ← zpow_neg, coe_sc, Units.coe_map, Units.val_zpow_eq_zpow_val,
      Units.val_mk0]
    exact tmul_mem_localBox R w hRo.one_mem (algebraMap_zpow_mem_integers_of_ne r hr w hw (-m))

omit hr hRo n z in
theorem mem_actionKer_iff (w : HeightOneSpectrum (𝓞 ℚ)) (γ : ↥(CosetGraph.awayUnits R w)) :
    γ ∈ CosetGraph.actionKer R w ↔ ∀ x : CosetGraph.Vert R w, (γ : (ℍ[ℚ, a, b])ˣ) • x = x := by
  rw [CosetGraph.actionKer, MonoidHom.mem_ker, Equiv.ext_iff]
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq]
  rfl

omit hr hRo n z in
theorem ratUnits_zpow_mem_actionKer (w : HeightOneSpectrum (𝓞 ℚ)) (u : ℚˣ) (m : ℤ)
    (h : ratUnits (a := a) (b := b) u ^ m ∈ CosetGraph.awayUnits R w) :
    (⟨ratUnits u ^ m, h⟩ : ↥(CosetGraph.awayUnits R w)) ∈ CosetGraph.actionKer R w := by
  rw [mem_actionKer_iff]
  intro x
  show (ratUnits (a := a) (b := b) u ^ m) • x = x
  rw [← map_zpow]
  exact ratUnits_smul_vert R w _ x

end Frame

section Main

variable {a b : ℚ}

open QuaternionAlgebra CerednikDrinfeld

def unitsOf (𝒪 : Submodule ℤ ℍ[ℚ, a, b]) (h𝒪 : IsOrder 𝒪) : Subgroup (ℍ[ℚ, a, b])ˣ where
  carrier := {u | (u : ℍ[ℚ, a, b]) ∈ 𝒪 ∧ ((u⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ 𝒪}
  one_mem' := ⟨by rw [Units.val_one]; exact h𝒪.one_mem, by rw [inv_one, Units.val_one]; exact h𝒪.one_mem⟩
  mul_mem' {x y} hx hy :=
    ⟨by rw [Units.val_mul]; exact h𝒪.mul_mem hx.1 hy.1,
     by rw [mul_inv_rev, Units.val_mul]; exact h𝒪.mul_mem hy.2 hx.2⟩
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

omit a b in
theorem isUnit_of_isUnitOf {a b : ℚ} {𝒪 : Submodule ℤ ℍ[ℚ, a, b]} {u : ℍ[ℚ, a, b]} (h : IsUnitOf 𝒪 u) : IsUnit u := by
  obtain ⟨-, w, -, h1, h2⟩ := h
  exact ⟨⟨u, w, h1, h2⟩, rfl⟩

def unitsOfEquiv (𝒪 : Submodule ℤ ℍ[ℚ, a, b]) (h𝒪 : IsOrder 𝒪) :
    {u : ℍ[ℚ, a, b] // IsUnitOf 𝒪 u} ≃ ↥(unitsOf 𝒪 h𝒪) where
  toFun x := ⟨(isUnit_of_isUnitOf x.2).unit, by
    obtain ⟨hmem, w, hw, h1, h2⟩ := x.2
    refine ⟨by rw [IsUnit.unit_spec]; exact hmem, ?_⟩
    rw [Units.inv_eq_of_mul_eq_one_right (show ((isUnit_of_isUnitOf x.2).unit : ℍ[ℚ, a, b]) * w = 1 by
      rw [IsUnit.unit_spec]; exact h1)]
    exact hw⟩
  invFun y := ⟨(y : (ℍ[ℚ, a, b])ˣ), y.2.1, ((y : (ℍ[ℚ, a, b])ˣ)⁻¹ : (ℍ[ℚ, a, b])ˣ), y.2.2, Units.mul_inv _,
    Units.inv_mul _⟩
  left_inv x := Subtype.ext (IsUnit.unit_spec (isUnit_of_isUnitOf x.2))
  right_inv y := Subtype.ext (Units.ext (IsUnit.unit_spec (Units.isUnit (y : (ℍ[ℚ, a, b])ˣ))))

theorem isUnitOf_of_mem_unitsOf {𝒪 : Submodule ℤ ℍ[ℚ, a, b]} {h𝒪 : IsOrder 𝒪} {u : (ℍ[ℚ, a, b])ˣ}
    (hu : u ∈ unitsOf 𝒪 h𝒪) : IsUnitOf 𝒪 (u : ℍ[ℚ, a, b]) :=
  ⟨hu.1, ((u⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]), hu.2, Units.mul_inv _, Units.inv_mul _⟩

theorem nrd_smul_one (c : ℚ) : nrd (c • (1 : ℍ[ℚ, a, b])) = c ^ 2 := by
  simp [nrd]

variable (r : ℕ) (hr : r.Prime)

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]
local notation "𝔳" => place r hr
set_option quotPrecheck false in
local notation "Lv" => CerednikDrinfeld.CosetGraph.Loc a b (place r hr)

set_option quotPrecheck false in
set_option hygiene false in
local notation "zv" => (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (place r hr)).toRingHom.toMonoidHom z :
  (CerednikDrinfeld.CosetGraph.Loc a b (place r hr))ˣ)
set_option quotPrecheck false in
set_option hygiene false in
local notation "nv" => (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (place r hr)).toRingHom.toMonoidHom n :
  (CerednikDrinfeld.CosetGraph.Loc a b (place r hr))ˣ)

theorem main {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N)
    (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hn : n ∈ primeHeckeSet R r)
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (z : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ 𝔳 →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (d : (CosetGraph.graph R 𝔳 nv).Dart)
    (hd₁ : d.fst = ((zv : (Lv)ˣ) : CosetGraph.Vert R 𝔳))
    (hd₂ : d.snd = ((zv * nv : (Lv)ˣ) : CosetGraph.Vert R 𝔳)) :
    Finite (MulAction.stabilizer (CosetGraph.ProjAwayUnits R 𝔳) d) ∧
      Nat.card (MulAction.stabilizer (CosetGraph.ProjAwayUnits R 𝔳) d) =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) z) u} / 2 := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hRo : IsOrder R := hR.isOrder
  have hv : ((r : ℕ) : 𝓞 ℚ) ∈ (𝔳).asIdeal := q_mem_asIdeal r hr
  have hO : IsOrder (Submodule.conjByFiniteIdele (meetOrder R n) z) := isOrder_O R hRo n z
  have hnR := hn.1
  have hnR' := hn.2.1

  have hAL := (CosetGraph.mul_self_mem_level_and_not_mem_level_and_mem_inf_conj_iff_of_mem_primeHeckeSet hdef hR
    hrq' hrN 𝔳 hv hn hnorm).2.2
  have hfixH : ∀ γ : (ℍ[ℚ, a, b])ˣ, (γ • d.fst = d.fst ∧ γ • d.snd = d.snd) ↔
      zv⁻¹ * CosetGraph.toLoc 𝔳 γ * zv ∈ CosetGraph.level (meetOrder R n) 𝔳 := by
    intro γ
    rw [← hAL, hd₁, hd₂, CosetGraph.smul_vert_mk, CosetGraph.smul_vert_mk, QuotientGroup.eq, QuotientGroup.eq]
    have e1 : (CosetGraph.toLoc 𝔳 γ * zv)⁻¹ * zv = (zv⁻¹ * CosetGraph.toLoc 𝔳 γ * zv)⁻¹ := by group
    have e2 : (CosetGraph.toLoc 𝔳 γ * (zv * nv))⁻¹ * (zv * nv) = (nv⁻¹ * (zv⁻¹ * CosetGraph.toLoc 𝔳 γ * zv) * nv)⁻¹ := by
      group
    rw [e1, e2, inv_mem_iff, inv_mem_iff]
  have hfix : ∀ γ : ↥(CosetGraph.awayUnits R 𝔳),
      (QuotientGroup.mk γ : CosetGraph.ProjAwayUnits R 𝔳) • d = d ↔
        zv⁻¹ * CosetGraph.toLoc 𝔳 (γ : (ℍ[ℚ, a, b])ˣ) * zv ∈ CosetGraph.level (meetOrder R n) 𝔳 := by
    intro γ
    rw [← hfixH, SimpleGraph.Dart.ext_iff, Prod.ext_iff]
    rfl

  have hUA : unitsOf _ hO ≤ CosetGraph.awayUnits R 𝔳 := fun u hu => (unit_mem_awayUnits r hr R hRo n z hz u hu.1 hu.2).1
  let f : ↥(unitsOf _ hO) →* CosetGraph.ProjAwayUnits R 𝔳 :=
    (QuotientGroup.mk' (CosetGraph.actionKer R 𝔳)).comp (Subgroup.inclusion hUA)
  have hf : ∀ u : ↥(unitsOf _ hO), f u = (QuotientGroup.mk (Subgroup.inclusion hUA u) : CosetGraph.ProjAwayUnits R 𝔳) :=
    fun u => rfl

  have hrange : f.range = MulAction.stabilizer (CosetGraph.ProjAwayUnits R 𝔳) d := by
    ext q
    constructor
    · rintro ⟨u, rfl⟩
      rw [MulAction.mem_stabilizer_iff, hf, hfix]
      exact (unit_mem_awayUnits r hr R hRo n z hz (u : (ℍ[ℚ, a, b])ˣ) u.2.1 u.2.2).2
    · intro hq
      obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
      rw [MulAction.mem_stabilizer_iff, hfix] at hq
      obtain ⟨m, h1, h2⟩ := exists_zpow_mul_mem r hr R hRo n hnR hnR' z hz (γ : (ℍ[ℚ, a, b])ˣ) γ.2 hq
      have hρA := ratUnits_zpow_mem_awayUnits r hr R hRo m
      have hρK := ratUnits_zpow_mem_actionKer R 𝔳 _ m hρA
      refine ⟨⟨_, h1, h2⟩, ?_⟩
      rw [hf]
      have e : Subgroup.inclusion hUA ⟨_, h1, h2⟩ =
          (⟨_, hρA⟩ : ↥(CosetGraph.awayUnits R 𝔳)) * γ := rfl
      rw [e, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hρK, one_mul]

  have hkerIff : ∀ u : ↥(unitsOf _ hO), u ∈ f.ker ↔
      ∀ x : CosetGraph.Vert R 𝔳, ((u : ↥(unitsOf _ hO)) : (ℍ[ℚ, a, b])ˣ) • x = x := by
    intro u
    rw [MonoidHom.mem_ker, hf, QuotientGroup.eq_one_iff, mem_actionKer_iff]
    rfl
  have hneg : (-1 : (ℍ[ℚ, a, b])ˣ) ∈ unitsOf _ hO := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_neg, Units.val_one]; exact neg_mem hO.one_mem
    · have : (((-1 : (ℍ[ℚ, a, b])ˣ)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = -1 := by simp
      rw [this]; exact neg_mem hO.one_mem
  have hnegval : ratUnits (a := a) (b := b) (-1) = -1 := by
    apply Units.ext; simp [coe_ratUnits]
  have hker : Nat.card f.ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨⟨-1, hneg⟩, (hkerIff _).2 fun x => ?_⟩, fun h => ?_, ?_⟩
    · show (-1 : (ℍ[ℚ, a, b])ˣ) • x = x
      rw [← hnegval]; exact ratUnits_smul_vert R 𝔳 _ x
    · have h' := congrArg (fun t : ↥f.ker => (((t : ↥(unitsOf _ hO)) : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]).re) h
      simp at h'
      norm_num at h'
    · refine Set.eq_univ_iff_forall.2 fun w => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

      have hwU : IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) z)
          (((w : ↥(unitsOf _ hO)) : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) := isUnitOf_of_mem_unitsOf (w : ↥(unitsOf _ hO)).2
      have htriv := (hkerIff (w : ↥(unitsOf _ hO))).1 w.2
      obtain ⟨c, hc⟩ := CosetGraph.exists_coe_eq_smul_one_of_forall_smul_vert_eq hdef hR hrq' hrN 𝔳 hv
        ((w : ↥(unitsOf _ hO)) : (ℍ[ℚ, a, b])ˣ) (fun g => htriv (g : CosetGraph.Vert R 𝔳))
      have hn1 : nrd (((w : ↥(unitsOf _ hO)) : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) = 1 :=
        (QuaternionAlgebra.IsOrder.finite_isUnitOf_and_nrd_eq_one hdef.neg_left hdef.neg_right hO).2 _ hwU
      rw [hc, nrd_smul_one, sq_eq_one_iff] at hn1
      rcases hn1 with rfl | rfl
      · left
        apply Subtype.ext; apply Subtype.ext; apply Units.ext
        rw [hc, one_smul]; rfl
      · right
        apply Subtype.ext; apply Subtype.ext; apply Units.ext
        rw [hc, neg_smul, one_smul]; rfl

  haveI hfinU' : Finite {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) z) u} :=
    (QuaternionAlgebra.IsOrder.finite_isUnitOf_and_nrd_eq_one hdef.neg_left hdef.neg_right hO).1
  haveI hfinU : Finite ↥(unitsOf _ hO) := Finite.of_equiv _ (unitsOfEquiv _ hO)
  have hcardU : Nat.card ↥(unitsOf _ hO) =
      Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) z) u} :=
    Nat.card_congr (unitsOfEquiv _ hO).symm
  have hquot : Nat.card ↥f.range = Nat.card (↥(unitsOf _ hO) ⧸ f.ker) :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange f).symm.toEquiv
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [hker, hcardU] at hlag
  rw [← hrange]
  refine ⟨Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective, ?_⟩
  rw [hquot]
  exact (Nat.div_eq_of_eq_mul_left (by norm_num) hlag).symm

end Main

end R1CDWidth

end

open QuaternionAlgebra CerednikDrinfeld R1CDWidth in
theorem solution
    {a b : ℚ} {q' : ℕ} [Fact q'.Prime] (hdef : IsDefiniteRamifiedExactlyAt a b q')
    {N : ℕ} [NeZero N] {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsEichlerOrder R N)
    {r : ℕ} [Fact r.Prime] (hrq' : r ≠ q') (hrN : ¬ r ∣ N)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hn : n ∈ primeHeckeSet R r)
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n)
    (z : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hz : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w (z : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)
    (d : (CosetGraph.graph R v (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n)).Dart)
    (hd₁ : d.fst = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom z :
      (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v))
    (hd₂ : d.snd = ((Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom z *
      Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n : (CosetGraph.Loc a b v)ˣ) :
        CosetGraph.Vert R v)) :
    Finite (MulAction.stabilizer (CosetGraph.ProjAwayUnits R v) d) ∧
      Nat.card (MulAction.stabilizer (CosetGraph.ProjAwayUnits R v) d) =
        Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele (meetOrder R n) z) u} / 2 := by
  obtain rfl : v = place r (Fact.out : r.Prime) := eq_place_of_mem r Fact.out v hv
  exact main r Fact.out hdef hR hrq' hrN hn hnorm z hz d hd₁ hd₂

end S_CerednikDrinfeld_CosetGraph_natCard_stabilizer_dart_eq_natCard_isUnitOf_conjByFiniteIdele_meetOrder_div_two
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_natCard_stabilizer_dart_eq_natCard_isUnitOf_conjByFiniteIdele_meetOrder_div_two (solution)
