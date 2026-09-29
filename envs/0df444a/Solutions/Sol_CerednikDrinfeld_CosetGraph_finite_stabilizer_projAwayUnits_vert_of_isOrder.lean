-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.finite_stabilizer_projAwayUnits_vert_of_isOrder
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/e2a76846-799e-5293-bf51-76bc65c2f273

import Mathlib
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_Submodule_LocalBox
import Definitions.Def_Submodule_FiniteAdeleBox
import Theorems.Thm_Submodule_exists_units_finiteAdeleEvalAt_eq_of_forall_ne
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_finite_isUnitOf_and_nrd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_finite_stabilizer_projAwayUnits_vert_of_isOrder

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

namespace CosetDiscAux

section Places

variable (v : HeightOneSpectrum (𝓞 ℚ))

def pgen : ℕ := Rat.HeightOneSpectrum.natGenerator (R := 𝓞 ℚ) v

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v

theorem pgen_prime : (pgen v).Prime := Rat.HeightOneSpectrum.prime_natGenerator (R := 𝓞 ℚ) v

theorem natCast_mem_asIdeal_iff (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ pgen w ∣ n := by
  rw [pgen, Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem pgen_mem_asIdeal : (pgen v : 𝓞 ℚ) ∈ v.asIdeal := (natCast_mem_asIdeal_iff v _).2 dvd_rfl

theorem eq_of_pgen_mem (w : HeightOneSpectrum (𝓞 ℚ)) (hw : (pgen v : 𝓞 ℚ) ∈ w.asIdeal) : w = v := by
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  apply Subtype.ext
  change pgen w = pgen v
  exact (Nat.prime_dvd_prime_iff_eq (pgen_prime w) (pgen_prime v)).1 ((natCast_mem_asIdeal_iff w _).1 hw)

theorem pgen_notMem_asIdeal_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) : (pgen v : 𝓞 ℚ) ∉ w.asIdeal :=
  fun h => hw (eq_of_pgen_mem v w h)

theorem valuation_natCast_eq_one_of_notMem (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 hn

theorem valuation_pgen_eq_one_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) : w.valuation ℚ (pgen v : ℚ) = 1 :=
  valuation_natCast_eq_one_of_notMem w _ (pgen_notMem_asIdeal_of_ne v w hw)

theorem asIdeal_eq_span : v.asIdeal = Ideal.span {(pgen v : 𝓞 ℚ)} := by
  have h := Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v
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
  simp [pgen]

theorem valuation_pgen : v.valuation ℚ (pgen v : ℚ) = WithZero.exp (-1) := by
  rw [show (pgen v : ℚ) = algebraMap (𝓞 ℚ) ℚ (pgen v) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ (by exact_mod_cast (pgen_prime v).ne_zero) (asIdeal_eq_span v)

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem algebraMap_natCast (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ) = (n : w.adicCompletion ℚ) := map_natCast _ n

theorem valued_pgen : Valued.v ((pgen v : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [← algebraMap_natCast, valued_algebraMap, valuation_pgen]

theorem algebraMap_zpow_mem_integers_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) (m : ℤ) :
    algebraMap ℚ (w.adicCompletion ℚ) ((pgen v : ℚ) ^ m) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap, map_zpow₀,
    valuation_pgen_eq_one_of_ne v w hw, one_zpow]

theorem algebraMap_zpow_place (m : ℤ) : algebraMap ℚ 𝕂 ((pgen v : ℚ) ^ m) = ((pgen v : ℕ) : 𝕂) ^ m := by
  rw [map_zpow₀, algebraMap_natCast]

theorem valued_zpow (m : ℤ) : Valued.v (((pgen v : ℕ) : 𝕂) ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, valued_pgen, ← WithZero.exp_zsmul]
  congr 1
  simp

theorem mem_integers_of_valued_le_one {x : 𝕂} (hx : Valued.v x ≤ 1) : x ∈ 𝓞v :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hx

theorem inv_mem_integers_of_valued_eq_one {x : 𝕂} (h : Valued.v x = 1) : x⁻¹ ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]

theorem exists_zpow_mul_valued_eq_one {c : 𝕂} (hc : c ≠ 0) :
    ∃ m : ℤ, Valued.v (((pgen v : ℕ) : 𝕂) ^ m * c) = 1 := by
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

variable {a b : ℚ} (v : HeightOneSpectrum (𝓞 ℚ))

open QuaternionAlgebra CerednikDrinfeld

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]
local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "ϖ" => ((pgen v : ℕ) : HeightOneSpectrum.adicCompletion ℚ v)
set_option quotPrecheck false in
local notation "Lv" => CerednikDrinfeld.CosetGraph.Loc a b v

variable (R : Submodule ℤ ℍ[ℚ, a, b]) (hRo : IsOrder R)

include hRo in

theorem exists_idele (g : (Lv)ˣ) :
    ∃ z : (𝔹)ˣ, Units.map (ev v).toRingHom.toMonoidHom z = g ∧
      ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → ev w (z : 𝔹) = 1 := by
  have hg1 : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
      ev w ((1 : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w ∧
      ev w (((1 : (𝔹)ˣ)⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := by
    intro w hw
    rw [inv_one, Units.val_one, map_one, Algebra.TensorProduct.one_def]
    exact ⟨tmul_one_mem_localBox R w hRo.one_mem, tmul_one_mem_localBox R w hRo.one_mem⟩
  obtain ⟨h, hv1, hv2, hw⟩ := Submodule.exists_units_finiteAdeleEvalAt_eq_of_forall_ne R hRo.fg hRo.spanTop v
    (g : Lv) ((g⁻¹ : (Lv)ˣ) : Lv) (Units.mul_inv g) (Units.inv_mul g) 1 hg1
  refine ⟨h, Units.ext hv1, fun w hww => ?_⟩
  rw [(hw w hww).1, Units.val_one, map_one]

variable (z : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  (hz : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
    Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] w
      ((z : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ) = 1)

set_option quotPrecheck false in
local notation "zv" => (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom z :
  (CosetGraph.Loc a b v)ˣ)

include hRo in
theorem isOrder_O : IsOrder (Submodule.conjByFiniteIdele R z) :=
  QuaternionAlgebra.IsOrder.conjByFiniteIdele R hRo z

include hz in
omit R in
theorem ev_z_inv (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) : ev w ((z⁻¹ : (𝔹)ˣ) : 𝔹) = 1 := by
  have := ev_units_inv_mul w z
  rwa [hz w hw, mul_one] at this

include hRo hz in

theorem mem_O_iff (y : ℍ[ℚ, a, b]) :
    y ∈ Submodule.conjByFiniteIdele R z ↔
      (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v →
        y ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) ∈ Submodule.localBox R w) ∧
      ((zv⁻¹ : (Lv)ˣ) : Lv) * (y ⊗ₜ[ℚ] (1 : 𝕂)) * (zv : Lv) ∈ Submodule.localBox R v := by
  rw [mem_conj_iff_forall hRo z y]
  constructor
  · intro h
    refine ⟨fun w hw => ?_, h v⟩
    have := h w
    rwa [hz w hw, ev_z_inv v z hz w hw, one_mul, mul_one] at this
  · rintro ⟨h1, h2⟩ w
    by_cases hw : w = v
    · subst hw; exact h2
    · rw [hz w hw, ev_z_inv v z hz w hw, one_mul, mul_one]; exact h1 w hw

include hRo hz in
theorem unit_mem_awayUnits (u : (ℍ[ℚ, a, b])ˣ)
    (hu : (u : ℍ[ℚ, a, b]) ∈ Submodule.conjByFiniteIdele R z)
    (hui : ((u⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Submodule.conjByFiniteIdele R z) :
    u ∈ CosetGraph.awayUnits R v ∧
      zv⁻¹ * CosetGraph.toLoc v u * zv ∈ CosetGraph.level R v := by
  obtain ⟨h1, h2⟩ := (mem_O_iff v R hRo z hz _).1 hu
  obtain ⟨h1', h2'⟩ := (mem_O_iff v R hRo z hz _).1 hui
  refine ⟨?_, ?_⟩
  · rw [CosetGraph.awayUnits, Subgroup.mem_iInf]
    intro w
    rw [Subgroup.mem_iInf]
    intro hw
    rw [Subgroup.mem_comap]
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, coe_toLoc]; exact h1 w hw
    · rw [SetLike.mem_coe, coe_toLoc_inv]; exact h1' w hw
  · apply localBoxUnits_le_level
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, Units.val_mul, Units.val_mul, coe_toLoc]; exact h2
    · have e : (zv⁻¹ * CosetGraph.toLoc v u * zv)⁻¹ = zv⁻¹ * (CosetGraph.toLoc v u)⁻¹ * zv := by
        rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
      rw [SetLike.mem_coe, e, Units.val_mul, Units.val_mul, coe_toLoc_inv]; exact h2'

omit v in
theorem coe_ratUnits_zpow_mul_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (u : ℚˣ) (m : ℤ) (γ : (ℍ[ℚ, a, b])ˣ) :
    ((ratUnits (a := a) (b := b) u ^ m * γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) ((u : ℚ) ^ m)) *
        ((γ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) := by
  rw [Units.val_mul, ← map_zpow, coe_ratUnits, Units.val_zpow_eq_zpow_val,
    ← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul]

omit v in
theorem coe_ratUnits_zpow_mul_inv_tmul (w : HeightOneSpectrum (𝓞 ℚ)) (u : ℚˣ) (m : ℤ) (γ : (ℍ[ℚ, a, b])ˣ) :
    (((ratUnits (a := a) (b := b) u ^ m * γ)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) ((u : ℚ) ^ (-m))) *
        (((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) := by
  rw [mul_inv_rev, ← zpow_neg, Units.val_mul, ← map_zpow, coe_ratUnits, Units.val_zpow_eq_zpow_val,
    one_tmul_mul_comm, ← Algebra.TensorProduct.algebraMap_apply', Algebra.TensorProduct.algebraMap_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]

omit v in
theorem conj_one_tmul_mul (w : HeightOneSpectrum (𝓞 ℚ)) (s : w.adicCompletion ℚ)
    (p p' x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    p * (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s) * x) * p' = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] s) * (p * x * p') := by
  rw [← mul_assoc p, ← one_tmul_mul_comm w s p]
  simp only [mul_assoc]

include hRo in
omit z in

theorem toLoc_mem_boxUnits_of_mem_awayUnits {γ : (ℍ[ℚ, a, b])ˣ} (hγ : γ ∈ CosetGraph.awayUnits R v)
    (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ v) : CosetGraph.toLoc w γ ∈ boxUnits hRo w := by
  rw [CosetGraph.awayUnits, Subgroup.mem_iInf] at hγ
  have h := hγ w
  rw [Subgroup.mem_iInf] at h
  have h' := h hw
  rwa [Subgroup.mem_comap, closure_localBoxUnits hRo] at h'

include hRo hz in

theorem exists_zpow_mul_mem (γ : (ℍ[ℚ, a, b])ˣ) (hγ : γ ∈ CosetGraph.awayUnits R v)
    (hk : zv⁻¹ * CosetGraph.toLoc v γ * zv ∈ CosetGraph.level R v) :
    ∃ m : ℤ,
      ((ratUnits (Units.mk0 (pgen v : ℚ) (by exact_mod_cast (pgen_prime v).ne_zero)) ^ m * γ : (ℍ[ℚ, a, b])ˣ) :
            ℍ[ℚ, a, b]) ∈ Submodule.conjByFiniteIdele R z ∧
        (((ratUnits (Units.mk0 (pgen v : ℚ) (by exact_mod_cast (pgen_prime v).ne_zero)) ^ m * γ)⁻¹ :
            (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ∈ Submodule.conjByFiniteIdele R z := by
  obtain ⟨c, t, ht, hkt⟩ := (mem_level_iff hRo v _).1 hk
  obtain ⟨m, hm⟩ := exists_zpow_mul_valued_eq_one v (c := (c : 𝕂)) c.ne_zero
  have he : ϖ ^ m * (c : 𝕂) ∈ 𝓞v := mem_integers_of_valued_le_one v hm.le
  have hei : (ϖ ^ m * (c : 𝕂))⁻¹ ∈ 𝓞v := inv_mem_integers_of_valued_eq_one v hm

  have hprod : ((zv⁻¹ : (Lv)ˣ) : Lv) * ((γ : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝕂)) * (zv : Lv) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (c : 𝕂)) * (t : Lv) := by
    have := congrArg Units.val hkt
    rwa [Units.val_mul, Units.val_mul, Units.val_mul, coe_sc, coe_toLoc] at this
  have hprod' : ((zv⁻¹ : (Lv)ˣ) : Lv) * (((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (1 : 𝕂)) * (zv : Lv) =
      ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((c⁻¹ : (𝕂)ˣ) : 𝕂)) * ((t⁻¹ : (Lv)ˣ) : Lv) := by
    have e : (zv⁻¹ * CosetGraph.toLoc v γ * zv)⁻¹ = zv⁻¹ * (CosetGraph.toLoc v γ)⁻¹ * zv := by
      rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
    have := congrArg (fun x : (Lv)ˣ => ((x⁻¹ : (Lv)ˣ) : Lv)) hkt
    rwa [e, mul_inv_rev, sc_inv, ← sc_mul_comm, Units.val_mul, Units.val_mul, Units.val_mul, coe_sc,
      coe_toLoc_inv] at this
  have hRunit : ∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ v → CosetGraph.toLoc w γ ∈ boxUnits hRo w :=
    fun w hw => toLoc_mem_boxUnits_of_mem_awayUnits v R hRo hγ w hw
  refine ⟨m, (mem_O_iff v R hRo z hz _).2 ⟨fun w hw => ?_, ?_⟩, (mem_O_iff v R hRo z hz _).2 ⟨fun w hw => ?_, ?_⟩⟩
  · rw [coe_ratUnits_zpow_mul_tmul]
    have h := (hRunit w hw).1
    rw [coe_toLoc] at h
    exact one_tmul_mul_mem_localBox R w h (algebraMap_zpow_mem_integers_of_ne v w hw m)
  · rw [coe_ratUnits_zpow_mul_tmul, conj_one_tmul_mul, hprod, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, Units.val_mk0, algebraMap_zpow_place]
    exact one_tmul_mul_mem_localBox _ _ ht.1 he
  · rw [coe_ratUnits_zpow_mul_inv_tmul]
    have h := (hRunit w hw).2
    rw [coe_toLoc_inv] at h
    exact one_tmul_mul_mem_localBox R w h (algebraMap_zpow_mem_integers_of_ne v w hw (-m))
  · rw [coe_ratUnits_zpow_mul_inv_tmul, conj_one_tmul_mul, hprod', ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, Units.val_mk0, algebraMap_zpow_place]
    have e : ϖ ^ (-m) * ((c⁻¹ : (𝕂)ˣ) : 𝕂) = (ϖ ^ m * (c : 𝕂))⁻¹ := by
      rw [mul_inv, zpow_neg, Units.val_inv_eq_inv_val]
    rw [e]
    exact one_tmul_mul_mem_localBox _ _ ht.2 hei

include hRo in
omit z in
theorem ratUnits_zpow_mem_awayUnits (m : ℤ) :
    ratUnits (a := a) (b := b) (Units.mk0 (pgen v : ℚ) (by exact_mod_cast (pgen_prime v).ne_zero)) ^ m ∈
      CosetGraph.awayUnits R v := by
  rw [CosetGraph.awayUnits, Subgroup.mem_iInf]
  intro w
  rw [Subgroup.mem_iInf]
  intro hw
  rw [Subgroup.mem_comap, ← map_zpow, toLoc_ratUnits]
  apply Subgroup.subset_closure
  refine ⟨?_, ?_⟩
  · rw [SetLike.mem_coe, coe_sc, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0]
    exact tmul_mem_localBox R w hRo.one_mem (algebraMap_zpow_mem_integers_of_ne v w hw m)
  · rw [SetLike.mem_coe, sc_inv, ← map_inv, ← zpow_neg, coe_sc, Units.coe_map, Units.val_zpow_eq_zpow_val,
      Units.val_mk0]
    exact tmul_mem_localBox R w hRo.one_mem (algebraMap_zpow_mem_integers_of_ne v w hw (-m))

omit z in
theorem mem_actionKer_iff (w : HeightOneSpectrum (𝓞 ℚ)) (γ : ↥(CosetGraph.awayUnits R w)) :
    γ ∈ CosetGraph.actionKer R w ↔ ∀ x : CosetGraph.Vert R w, (γ : (ℍ[ℚ, a, b])ˣ) • x = x := by
  rw [CosetGraph.actionKer, MonoidHom.mem_ker, Equiv.ext_iff]
  simp only [MulAction.toPermHom_apply, MulAction.toPerm_apply, Equiv.Perm.coe_one, id_eq]
  rfl

omit z in
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

theorem finite_unitsOf (𝒪 : Submodule ℤ ℍ[ℚ, a, b]) (h𝒪 : IsOrder 𝒪)
    (hfin : Finite {u : ℍ[ℚ, a, b] // IsUnitOf 𝒪 u}) : Finite ↥(unitsOf 𝒪 h𝒪) := by
  refine Finite.of_injective (fun y : ↥(unitsOf 𝒪 h𝒪) =>
    (⟨((y : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]), y.2.1, (((y : (ℍ[ℚ, a, b])ˣ)⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]), y.2.2,
      Units.mul_inv _, Units.inv_mul _⟩ : {u : ℍ[ℚ, a, b] // IsUnitOf 𝒪 u})) ?_
  intro y y' h
  have h' := congrArg Subtype.val h
  exact Subtype.ext (Units.ext h')

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

theorem main (ha : a < 0) (hb : b < 0) {R : Submodule ℤ ℍ[ℚ, a, b]} (hRo : IsOrder R)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : CosetGraph.Vert R v) :
    Finite ↥(MulAction.stabilizer (CosetGraph.ProjAwayUnits R v) x) := by
  induction x using QuotientGroup.induction_on with
  | H g =>

  obtain ⟨z, hzv, hz⟩ := exists_idele v R hRo g
  have hO : IsOrder (Submodule.conjByFiniteIdele R z) := isOrder_O R hRo z

  have hfix : ∀ γ : ↥(CosetGraph.awayUnits R v),
      (QuotientGroup.mk γ : CosetGraph.ProjAwayUnits R v) • ((g : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v) =
          ((g : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v) ↔
        (Units.map (ev v).toRingHom.toMonoidHom z)⁻¹ * CosetGraph.toLoc v (γ : (ℍ[ℚ, a, b])ˣ) *
            Units.map (ev v).toRingHom.toMonoidHom z ∈ CosetGraph.level R v := by
    intro γ
    rw [CosetGraph.mk_smul_vert, hzv]
    change (CosetGraph.toLoc v (γ : (ℍ[ℚ, a, b])ˣ) * g : CosetGraph.Vert R v) = (g : CosetGraph.Vert R v) ↔ _
    rw [QuotientGroup.eq]
    have e1 : (CosetGraph.toLoc v (γ : (ℍ[ℚ, a, b])ˣ) * g)⁻¹ * g = (g⁻¹ * CosetGraph.toLoc v (γ : (ℍ[ℚ, a, b])ˣ) * g)⁻¹ := by
      group
    rw [e1, inv_mem_iff]

  have hUA : unitsOf _ hO ≤ CosetGraph.awayUnits R v := fun u hu => (unit_mem_awayUnits v R hRo z hz u hu.1 hu.2).1
  let f : ↥(unitsOf _ hO) →* CosetGraph.ProjAwayUnits R v :=
    (QuotientGroup.mk' (CosetGraph.actionKer R v)).comp (Subgroup.inclusion hUA)
  have hf : ∀ u : ↥(unitsOf _ hO), f u = (QuotientGroup.mk (Subgroup.inclusion hUA u) : CosetGraph.ProjAwayUnits R v) :=
    fun u => rfl

  have hsub : ∀ q : CosetGraph.ProjAwayUnits R v,
      q ∈ MulAction.stabilizer (CosetGraph.ProjAwayUnits R v) ((g : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v) →
        q ∈ Set.range f := by
    intro q hq
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk_surjective q
    rw [MulAction.mem_stabilizer_iff, hfix] at hq
    obtain ⟨m, h1, h2⟩ := exists_zpow_mul_mem v R hRo z hz (γ : (ℍ[ℚ, a, b])ˣ) γ.2 hq
    have hρA := ratUnits_zpow_mem_awayUnits v R hRo m
    have hρK := ratUnits_zpow_mem_actionKer R v _ m hρA
    refine ⟨⟨_, h1, h2⟩, ?_⟩
    rw [hf]
    have e : Subgroup.inclusion hUA ⟨_, h1, h2⟩ =
        (⟨_, hρA⟩ : ↥(CosetGraph.awayUnits R v)) * γ := rfl
    rw [e, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).2 hρK, one_mul]

  haveI hfinU' : Finite {u : ℍ[ℚ, a, b] // IsUnitOf (Submodule.conjByFiniteIdele R z) u} :=
    (QuaternionAlgebra.IsOrder.finite_isUnitOf_and_nrd_eq_one ha hb hO).1
  haveI hfinU : Finite ↥(unitsOf _ hO) := finite_unitsOf _ hO hfinU'
  refine Finite.of_injective
    (fun q : ↥(MulAction.stabilizer (CosetGraph.ProjAwayUnits R v) ((g : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v)) =>
      (⟨(q : CosetGraph.ProjAwayUnits R v), hsub q q.2⟩ : Set.range f)) ?_
  intro q q' h
  have h' : (q : CosetGraph.ProjAwayUnits R v) = (q' : CosetGraph.ProjAwayUnits R v) :=
    congrArg (fun t : ↥(Set.range f) => (t : CosetGraph.ProjAwayUnits R v)) h
  exact Subtype.ext h'

end Main

end CosetDiscAux

end

open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld in
theorem solution
    {a b : ℚ} (ha : a < 0) (hb : b < 0) {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
    (v : HeightOneSpectrum (𝓞 ℚ)) (x : CosetGraph.Vert R v) :
    Finite ↥(MulAction.stabilizer (CosetGraph.ProjAwayUnits R v) x) :=
  CosetDiscAux.main ha hb hR v x

end S_CerednikDrinfeld_CosetGraph_finite_stabilizer_projAwayUnits_vert_of_isOrder
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_finite_stabilizer_projAwayUnits_vert_of_isOrder (solution)
