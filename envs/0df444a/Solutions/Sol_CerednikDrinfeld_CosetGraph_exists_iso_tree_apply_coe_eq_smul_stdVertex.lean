-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.exists_iso_tree_apply_coe_eq_smul_stdVertex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/b73e507f-c2df-5fa9-9705-90d28f435a1a

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Matrix_exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers
import Theorems.Thm_LT_LatticeTree_exists_act_stdVertex_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_exists_iso_tree_apply_coe_eq_smul_stdVertex
p2m_attr_erase "simp" "LocalGL2.swapUnit_val"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.multiGoal false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped TensorProduct Quaternion Pointwise MatrixGroups
open IsDedekindDomain NumberField

noncomputable section

namespace R5IsoTree

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

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) c) = w.valuation ℚ c := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w c

theorem algebraMap_natCast (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ) = (n : w.adicCompletion ℚ) := map_natCast _ n

theorem valued_q : Valued.v ((q : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [← algebraMap_natCast, valued_algebraMap, valuation_q]

theorem q_ne_zero' : ((q : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_q q hq
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem valued_natCast_eq_one_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) :
    Valued.v ((q : ℕ) : w.adicCompletion ℚ) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := ℚ) w (q : 𝓞 ℚ)
  rw [(HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w)).mpr
    (q_notMem_asIdeal_of_ne q hq w hw)] at h
  change Valued.v (algebraMap (𝓞 ℚ) (w.adicCompletion ℚ) q) = 1 at h
  rwa [map_natCast] at h

theorem natCast_ne_zero_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) :
    ((q : ℕ) : w.adicCompletion ℚ) ≠ 0 := by
  intro h
  have := valued_natCast_eq_one_of_ne q hq w hw
  rw [h, map_zero] at this
  exact zero_ne_one this

theorem natCast_inv_mem_integers_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) :
    ((q : ℕ) : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, valued_natCast_eq_one_of_ne q hq w hw, inv_one]

theorem valued_zpow (m : ℤ) : Valued.v (((q : ℕ) : 𝕂) ^ m) = WithZero.exp (-m) := by
  rw [map_zpow₀, valued_q, ← WithZero.exp_zsmul]
  congr 1
  simp

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

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem one_tmul_mul_mem_localBox {x : D ⊗[ℚ] v.adicCompletion ℚ} (hx : x ∈ Submodule.localBox Λ v)
    {c : v.adicCompletion ℚ} (hc : c ∈ v.adicCompletionIntegers ℚ) :
    ((1 : D) ⊗ₜ[ℚ] c) * x ∈ Submodule.localBox Λ v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨z, hz, c', hc', rfl⟩ := hy
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact tmul_mem_localBox Λ v hz (mul_mem hc hc')
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => exact (mul_neg _ x).symm ▸ neg_mem hx

omit Λ in
theorem ratCast_smul_eq_one_tmul_mul (c : ℚ) (x : D ⊗[ℚ] v.adicCompletion ℚ) :
    c • x = ((1 : D) ⊗ₜ[ℚ] (algebraMap ℚ (v.adicCompletion ℚ) c)) * x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, mul_zero]
  | tmul z d =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.smul_tmul', TensorProduct.smul_tmul,
      Algebra.smul_def]
  | add x y hx hy => rw [smul_add, mul_add, hx, hy]

end Box

section LocalMatrix

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)

theorem valued_le_one_of_mem {x : 𝕂} (hx : x ∈ 𝓞v) : Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hx

theorem mem_integers_of_valued_le_one {x : 𝕂} (hx : Valued.v x ≤ 1) : x ∈ 𝓞v :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hx

theorem inv_mem_integers_of_valued_eq_one {x : 𝕂} (h : Valued.v x = 1) : x⁻¹ ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]

theorem div_mem_integers {x y : 𝕂} (hy : y ≠ 0) (h : Valued.v x ≤ Valued.v y) : x / y ∈ 𝓞v := by
  apply mem_integers_of_valued_le_one
  have hy' : Valued.v y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
  rw [map_div₀]
  calc Valued.v x / Valued.v y ≤ Valued.v y / Valued.v y := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_left h _
    _ = 1 := div_self hy'

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

theorem of_mem_intMat {a b c d : 𝕂} (ha : a ∈ 𝓞v) (hb : b ∈ 𝓞v) (hc : c ∈ 𝓞v) (hd : d ∈ 𝓞v) :
    !![a, b; c, d] ∈ intMat v := by
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using ha
  · simpa using hb
  · simpa using hc
  · simpa using hd

def K0 : Subgroup (M₂)ˣ where
  carrier := {g | (g : M₂) ∈ intMat v ∧ ((g⁻¹ : (M₂)ˣ) : M₂) ∈ intMat v}
  one_mem' := ⟨by rw [Units.val_one]; exact one_mem _, by rw [inv_one, Units.val_one]; exact one_mem _⟩
  mul_mem' {x y} hx hy :=
    ⟨by rw [Units.val_mul]; exact mul_mem hx.1 hy.1,
     by rw [mul_inv_rev, Units.val_mul]; exact mul_mem hy.2 hx.2⟩
  inv_mem' {x} hx := ⟨hx.2, by rw [inv_inv]; exact hx.1⟩

theorem mem_K0_iff (g : (M₂)ˣ) :
    g ∈ K0 v ↔ (g : M₂) ∈ intMat v ∧ ((g⁻¹ : (M₂)ˣ) : M₂) ∈ intMat v := Iff.rfl

theorem det_coe_ne_zero (X : (M₂)ˣ) : (X : M₂).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det X.mul_inv
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

end LocalMatrix

section Global

variable {a b : ℚ} (r : ℕ) (hr : r.Prime)

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]
local notation "𝔳" => place r hr
local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place r hr)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place r hr)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place r hr))
set_option quotPrecheck false in
local notation "Lv" => CerednikDrinfeld.CosetGraph.Loc a b (place r hr)

p2m_open "QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_CosetGraph_exists_iso_tree_apply_coe_eq_smul_stdVertex.CerednikDrinfeld"

omit hr in
theorem mem_box_iff {Λ : Submodule ℤ ℍ[ℚ, a, b]} (hΛ : IsOrder Λ) (x : 𝔹) :
    x ∈ Submodule.finiteAdeleBox Λ ↔ ∀ w, ev w x ∈ Submodule.localBox Λ w :=
  Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hΛ.fg hΛ.spanTop x

omit hr in
theorem ev_ratCast_smul (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℚ) (x : 𝔹) :
    ev w (c • x) = ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (algebraMap ℚ _ c)) * ev w x := by
  rw [map_smul, ratCast_smul_eq_one_tmul_mul]

omit hr in
theorem ev_units_mul_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    ev w (g : 𝔹) * ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) = 1 := by rw [← map_mul, Units.mul_inv, map_one]

omit hr in
theorem ev_units_inv_mul (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) * ev w (g : 𝔹) = 1 := by rw [← map_mul, Units.inv_mul, map_one]

omit hr in

theorem coe_units_map_ev (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    ((Units.map (ev w).toRingHom.toMonoidHom g : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = ev w (g : 𝔹) := rfl

omit hr in
theorem coe_units_map_ev_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (𝔹)ˣ) :
    (((Units.map (ev w).toRingHom.toMonoidHom g)⁻¹ : (ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ)ˣ) :
      ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) = ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) := by
  rw [← map_inv]; rfl

theorem one_tmul_natCast_inv_mul_cancel (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳)
    (x : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) :
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((r : ℕ) : w.adicCompletion ℚ)⁻¹) *
      (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((r : ℕ) : w.adicCompletion ℚ)) * x) = x := by
  rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    inv_mul_cancel₀ (natCast_ne_zero_of_ne r hr w hw)]
  change (1 : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ) * x = x
  rw [one_mul]

theorem local_of_mem_primeHeckeSet (R : Submodule ℤ ℍ[ℚ, a, b]) (hRo : IsOrder R)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] (place r hr).adicCompletion ℚ ≃+*
      Matrix (Fin 2) (Fin 2) ((place r hr).adicCompletion ℚ))
    (hφ1 : ∀ t : (place r hr).adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) ((place r hr).adicCompletion ℚ)))
    (hφR : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] (place r hr).adicCompletion ℚ,
      x ∈ Submodule.localBox R (place r hr) ↔ ∀ i j, φ x i j ∈ (place r hr).adicCompletionIntegers ℚ)
    {g : (𝔹)ˣ} (hg : g ∈ primeHeckeSet R r) :
    (∀ i j, φ (ev 𝔳 (g : 𝔹)) i j ∈ 𝓞v) ∧
    (∀ i j, (((r : ℕ) : 𝕂) • φ (ev 𝔳 ((g⁻¹ : (𝔹)ˣ) : 𝔹))) i j ∈ 𝓞v) ∧
    (¬ ∀ i j, φ (ev 𝔳 ((g⁻¹ : (𝔹)ˣ) : 𝔹)) i j ∈ 𝓞v) ∧
    ¬ ∀ i j, (((r : ℕ) : 𝕂)⁻¹ • φ (ev 𝔳 (g : 𝔹))) i j ∈ 𝓞v := by
  have map_one_tmul_mul : ∀ (c : 𝕂) (x : Lv), φ (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x) = c • φ x := by
    intro c x; rw [map_mul, hφ1, smul_mul_assoc, one_mul]
  obtain ⟨h1, h2, h3, h4⟩ := hg
  have hw1 : ∀ w, ev w (g : 𝔹) ∈ Submodule.localBox R w := (mem_box_iff hRo _).1 h1
  have hw2' : ∀ w, ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((r : ℕ) : w.adicCompletion ℚ)) *
      ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := by
    intro w
    have := (mem_box_iff hRo _).1 h2 w
    rwa [ev_ratCast_smul, map_natCast] at this
  have hw2 : ∀ w, w ≠ 𝔳 → ev w ((g⁻¹ : (𝔹)ˣ) : 𝔹) ∈ Submodule.localBox R w := fun w hw => by
    have := one_tmul_mul_mem_localBox R w (hw2' w) (natCast_inv_mem_integers_of_ne r hr w hw)
    rwa [one_tmul_natCast_inv_mul_cancel r hr w hw] at this
  refine ⟨(hφR _).1 (hw1 𝔳), ?_, ?_, ?_⟩
  · rw [← map_one_tmul_mul]; exact (hφR _).1 (hw2' 𝔳)
  · intro H
    apply h3
    rw [mem_box_iff hRo]
    intro w
    by_cases hw : w = 𝔳
    · subst hw; exact (hφR _).2 H
    · exact hw2 w hw
  · intro H
    apply h4
    rw [mem_box_iff hRo]
    intro w
    rw [ev_ratCast_smul, map_inv₀, map_natCast]
    by_cases hw : w = 𝔳
    · subst hw; rw [hφR, map_one_tmul_mul]; exact H
    · exact one_tmul_mul_mem_localBox R w (hw1 w) (natCast_inv_mem_integers_of_ne r hr w hw)

end Global

section Lattice

variable (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ v)

open LT.LatticeTree CerednikDrinfeld.BruhatTits

theorem isInteger_iff_mem {x : 𝕂} : IsLocalization.IsInteger 𝓞v x ↔ x ∈ 𝓞v := by
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem latticeMap_stdLattice_le_of_mem_intMat {g : (M₂)ˣ} (hg : (g : M₂) ∈ intMat v) :
    latticeMap g (stdLattice 𝓞v 𝕂) ≤ stdLattice 𝓞v 𝕂 :=
  latticeMap_le_stdLattice_of_isInteger fun i j => (isInteger_iff_mem v).2 (hg i j)

theorem mem_intMat_of_latticeMap_stdLattice_le {g : (M₂)ˣ}
    (h : latticeMap g (stdLattice 𝓞v 𝕂) ≤ stdLattice 𝓞v 𝕂) : (g : M₂) ∈ intMat v := by
  intro i j
  have hj : Matrix.mulVec (g : M₂) (Pi.single j 1) ∈ stdLattice 𝓞v 𝕂 :=
    h (mulVec_mem_latticeMap (single_one_mem_stdLattice 𝓞v 𝕂 j))
  have hij := hj i
  rw [mulVec_single_one] at hij
  exact (isInteger_iff_mem v).1 hij

theorem latticeMap_stdLattice_eq_of_mem_K0 {g : (M₂)ˣ} (hg : g ∈ K0 v) :
    latticeMap g (stdLattice 𝓞v 𝕂) = stdLattice 𝓞v 𝕂 := by
  refine le_antisymm (latticeMap_stdLattice_le_of_mem_intMat v hg.1) ?_
  have h := latticeMap_mono g (latticeMap_stdLattice_le_of_mem_intMat v hg.2)
  rwa [latticeMap_latticeMap_inv] at h

theorem mem_K0_of_latticeMap_stdLattice_eq {g : (M₂)ˣ}
    (hg : latticeMap g (stdLattice 𝓞v 𝕂) = stdLattice 𝓞v 𝕂) : g ∈ K0 v := by
  refine ⟨mem_intMat_of_latticeMap_stdLattice_le v hg.le, mem_intMat_of_latticeMap_stdLattice_le v ?_⟩
  have h := latticeMap_inv_latticeMap g (stdLattice 𝓞v 𝕂)
  rw [hg] at h
  exact h.le

theorem mem_K0_iff_latticeMap_stdLattice_eq (g : (M₂)ˣ) :
    g ∈ K0 v ↔ latticeMap g (stdLattice 𝓞v 𝕂) = stdLattice 𝓞v 𝕂 :=
  ⟨latticeMap_stdLattice_eq_of_mem_K0 v, mem_K0_of_latticeMap_stdLattice_eq v⟩

theorem smul_stdVertex_of_mem_K0 {g : (M₂)ˣ} (hg : g ∈ K0 v) :
    g • stdVertex 𝓞v 𝕂 = stdVertex 𝓞v 𝕂 := by
  rw [stdVertex, gl_smul_mk, Vertex.mk_eq_mk_iff, latticeMap_stdLattice_eq_of_mem_K0 v hg]
  exact Homothetic.refl _

theorem smul_stdVertex_eq_iff (g : (M₂)ˣ) :
    g • stdVertex 𝓞v 𝕂 = stdVertex 𝓞v 𝕂 ↔ ∃ c : (𝕂)ˣ, scalarGL c * g ∈ K0 v := by
  rw [gl_smul_def, stdVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, mem_K0_of_latticeMap_stdLattice_eq v ?_⟩
    rw [latticeMap_mul]
    exact hc
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [← latticeMap_mul]
    exact latticeMap_stdLattice_eq_of_mem_K0 v hc

theorem scalarGL_smul (c : (𝕂)ˣ) (X : Vertex 𝓞v 𝕂) : scalarGL c • X = X :=
  isFixedVertex_scalarGL c X

end Lattice

section Neighbours

variable (r : ℕ) (hr : r.Prime)

local notation "𝔳" => place r hr
local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place r hr)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place r hr)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place r hr))

open LT.LatticeTree CerednikDrinfeld.BruhatTits

def piK : (𝕂)ˣ := Units.mk0 ((r : ℕ) : 𝕂) (q_ne_zero' r hr)

@[scoped simp] theorem coe_piK : ((piK r hr : (𝕂)ˣ) : 𝕂) = ((r : ℕ) : 𝕂) := rfl

theorem natCast_mem_integers : ((r : ℕ) : 𝕂) ∈ 𝓞v :=
  mem_integers_of_valued_le_one _ (by rw [valued_q r hr, ← WithZero.exp_zero, WithZero.exp_le_exp]; norm_num)

def piO : 𝓞v := ⟨((r : ℕ) : 𝕂), natCast_mem_integers r hr⟩

@[scoped simp] theorem coe_piO : ((piO r hr : 𝓞v) : 𝕂) = ((r : ℕ) : 𝕂) := rfl

theorem piO_ne_zero : piO r hr ≠ 0 := fun h =>
  q_ne_zero' r hr (by rw [← coe_piO r hr, h]; rfl)

theorem exists_valued_eq_exp {x : 𝓞v} (hx : x ≠ 0) : ∃ m : ℤ, m ≤ 0 ∧ Valued.v (x : 𝕂) = WithZero.exp m := by
  have hx' : (x : 𝕂) ≠ 0 := fun h => hx (Subtype.ext h)
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v (x : 𝕂) = WithZero.exp k :=
    ⟨WithZero.log (Valued.v (x : 𝕂)), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx')).symm⟩
  refine ⟨k, ?_, hk⟩
  have h1 : Valued.v (x : 𝕂) ≤ 1 := valued_le_one_of_mem _ x.2
  rw [hk, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
  exact h1

theorem irreducible_piO : Irreducible (piO r hr) := by
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one] at hu
    change Valued.v ((r : ℕ) : 𝕂) = 1 at hu
    rw [valued_q r hr, ← WithZero.exp_zero] at hu
    exact absurd (WithZero.exp_injective hu) (by norm_num)
  · have ha0 : a ≠ 0 := fun h => piO_ne_zero r hr (by rw [hab, h, zero_mul])
    have hb0 : b ≠ 0 := fun h => piO_ne_zero r hr (by rw [hab, h, mul_zero])
    obtain ⟨m, hm, hma⟩ := exists_valued_eq_exp r hr ha0
    obtain ⟨m', hm', hmb⟩ := exists_valued_eq_exp r hr hb0
    have hv : Valued.v ((piO r hr : 𝓞v) : 𝕂) = Valued.v ((a : 𝕂) * (b : 𝕂)) := by rw [hab]; rfl
    rw [coe_piO, valued_q r hr, map_mul, hma, hmb, ← WithZero.exp_add] at hv
    have hsum : (-1 : ℤ) = m + m' := WithZero.exp_injective hv
    rcases (show m = 0 ∨ m' = 0 by omega) with h | h
    · left
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      change Valued.v (a : 𝕂) = 1
      rw [hma, h, WithZero.exp_zero]
    · right
      rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
      change Valued.v (b : 𝕂) = 1
      rw [hmb, h, WithZero.exp_zero]

theorem unitOfNeZero_piO :
    unitOfNeZero (K := 𝕂) (irreducible_piO r hr).ne_zero = piK r hr :=
  Units.ext rfl

theorem latticeMap_scalarGL_unitOfNeZero_eq {ϖ : 𝓞v} (hϖ : Irreducible ϖ) :
    latticeMap (scalarGL (unitOfNeZero (K := 𝕂) hϖ.ne_zero)) (stdLattice 𝓞v 𝕂) =
      latticeMap (scalarGL (piK r hr)) (stdLattice 𝓞v 𝕂) := by
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible _ (irreducible_piO r hr) hϖ
  have he : unitOfNeZero (K := 𝕂) hϖ.ne_zero =
      piK r hr * Units.map (algebraMap 𝓞v 𝕂).toMonoidHom u := by
    apply Units.ext
    rw [unitOfNeZero_coe, Units.val_mul, ← hu, map_mul]
    rfl
  have hfix : latticeMap (scalarGL (Units.map (algebraMap 𝓞v 𝕂).toMonoidHom u)) (stdLattice 𝓞v 𝕂) =
      stdLattice 𝓞v 𝕂 :=
    latticeMap_scalarGL_eq_self_of_isUnit (u := (u : 𝓞v)) u.isUnit rfl _
  rw [he, scalarGL_mul, latticeMap_mul, hfix]

theorem coe_diagSnd_piK :
    ((diagSnd (piK r hr) : (M₂)ˣ) : M₂) = !![1, 0; 0, ((r : ℕ) : 𝕂)] := by
  rw [diagSnd_coe, coe_piK]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem adjacentLattice_stdLattice_diagSnd_piK :
    AdjacentLattice (stdLattice 𝓞v 𝕂) (latticeMap (diagSnd (piK r hr)) (stdLattice 𝓞v 𝕂)) := by
  rw [← unitOfNeZero_piO r hr]
  exact adjacentLattice_stdLattice_diagSnd (irreducible_piO r hr)

theorem exists_mem_K0_eq_latticeMap_mul_diagSnd {N : Submodule 𝓞v (Fin 2 → 𝕂)}
    (hlow : latticeMap (scalarGL (piK r hr)) (stdLattice 𝓞v 𝕂) < N) (hup : N < stdLattice 𝓞v 𝕂) :
    ∃ k ∈ K0 𝔳, N = latticeMap (k * diagSnd (piK r hr)) (stdLattice 𝓞v 𝕂) := by
  have hlow' : latticeMap (scalarGL (unitOfNeZero (K := 𝕂) (irreducible_piO r hr).ne_zero))
      (stdLattice 𝓞v 𝕂) ≤ N := by rw [unitOfNeZero_piO]; exact hlow.le
  have hN : IsFullLattice N := isFullLattice_of_le_of_le (irreducible_piO r hr).ne_zero hlow' hup.le
  obtain ⟨g, hg⟩ := LT.LatticeTree.exists_act_stdVertex_eq 𝓞v 𝕂 (Vertex.mk 𝓞v 𝕂 N hN)
  rw [stdVertex, Vertex.act_mk, Vertex.mk_eq_mk_iff] at hg
  obtain ⟨c, hc⟩ := hg
  rw [← latticeMap_mul] at hc

  generalize hg'def : scalarGL c * g = g' at hc
  have h1 : (g' : M₂) * ((g'⁻¹ : (M₂)ˣ) : M₂) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h2 : ((g'⁻¹ : (M₂)ˣ) : M₂) * (g' : M₂) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

  have hY : ∀ i j, (g' : M₂) i j ∈ 𝓞v :=
    mem_intMat_of_latticeMap_stdLattice_le 𝔳 (by rw [hc]; exact hup.le)

  have hpYi : ∀ i j, ((((r : ℕ) : 𝕂)) • ((g'⁻¹ : (M₂)ˣ) : M₂)) i j ∈ 𝓞v := by
    have hle : latticeMap (g'⁻¹ * scalarGL (piK r hr)) (stdLattice 𝓞v 𝕂) ≤ stdLattice 𝓞v 𝕂 := by
      have h := latticeMap_mono g'⁻¹ (hc.symm ▸ hlow.le : latticeMap (scalarGL (piK r hr))
        (stdLattice 𝓞v 𝕂) ≤ latticeMap g' (stdLattice 𝓞v 𝕂))
      rwa [latticeMap_inv_latticeMap, ← latticeMap_mul] at h
    have hint := mem_intMat_of_latticeMap_stdLattice_le 𝔳 hle
    have heq : ((g'⁻¹ * scalarGL (piK r hr) : (M₂)ˣ) : M₂) =
        ((r : ℕ) : 𝕂) • ((g'⁻¹ : (M₂)ˣ) : M₂) := by
      rw [Units.val_mul, scalarGL_coe, Matrix.mul_smul, Matrix.mul_one, coe_piK]
    rw [heq] at hint
    exact hint

  have hYi : ¬ ∀ i j, ((g'⁻¹ : (M₂)ˣ) : M₂) i j ∈ 𝓞v := by
    intro H
    have hle : latticeMap g'⁻¹ (stdLattice 𝓞v 𝕂) ≤ stdLattice 𝓞v 𝕂 :=
      latticeMap_stdLattice_le_of_mem_intMat 𝔳 H
    have h := latticeMap_mono g' hle
    rw [latticeMap_latticeMap_inv, hc] at h
    exact lt_irrefl _ (lt_of_le_of_lt h hup)

  have hpY : ¬ ∀ i j, ((((r : ℕ) : 𝕂))⁻¹ • (g' : M₂)) i j ∈ 𝓞v := by
    intro H
    have heq : ((((r : ℕ) : 𝕂))⁻¹ • (g' : M₂)) = ((scalarGL (piK r hr)⁻¹ * g' : (M₂)ˣ) : M₂) := by
      rw [Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.one_mul, Units.val_inv_eq_inv_val, coe_piK]
    rw [heq] at H
    have hle : latticeMap (scalarGL (piK r hr)⁻¹ * g') (stdLattice 𝓞v 𝕂) ≤ stdLattice 𝓞v 𝕂 :=
      latticeMap_stdLattice_le_of_mem_intMat 𝔳 H
    have h := latticeMap_mono (scalarGL (piK r hr)) hle
    rw [← latticeMap_mul, ← mul_assoc, ← scalarGL_mul, mul_inv_cancel, scalarGL_one, one_mul, hc] at h
    exact lt_irrefl _ (lt_of_lt_of_le hlow h)

  obtain ⟨K₁, K₁i, K₂, K₂i, hK₁, hK₁i, hK₂, hK₂i, e₁, e₁', e₂, e₂', hYeq⟩ :=
    Matrix.exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers r hr 𝔳 (q_mem_asIdeal r hr)
      (g' : M₂) ((g'⁻¹ : (M₂)ˣ) : M₂) h1 h2 hY hpYi hYi hpY
  let k₁ : (M₂)ˣ := ⟨K₁, K₁i, e₁, e₁'⟩
  let k₂ : (M₂)ˣ := ⟨K₂, K₂i, e₂, e₂'⟩
  have hk₁ : k₁ ∈ K0 𝔳 := ⟨hK₁, hK₁i⟩
  have hk₂ : k₂ ∈ K0 𝔳 := ⟨hK₂, hK₂i⟩
  have hg'eq : g' = k₁ * diagSnd (piK r hr) * k₂ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, coe_diagSnd_piK, hYeq]
  refine ⟨k₁, hk₁, ?_⟩
  rw [← hc, hg'eq, latticeMap_mul (k₁ * diagSnd (piK r hr)) k₂, latticeMap_stdLattice_eq_of_mem_K0 𝔳 hk₂]

end Neighbours

section Transport

variable {a b : ℚ} (r : ℕ) (hr : r.Prime)

set_option quotPrecheck false in
local notation "𝔹" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]
local notation "𝔳" => place r hr
local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place r hr)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place r hr)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place r hr))
set_option quotPrecheck false in
local notation "Lv" => CerednikDrinfeld.CosetGraph.Loc a b (place r hr)
variable (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)

set_option quotPrecheck false in
local notation "nv" => (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] (place r hr)).toRingHom.toMonoidHom n :
  (CerednikDrinfeld.CosetGraph.Loc a b (place r hr))ˣ)

variable (R : Submodule ℤ ℍ[ℚ, a, b])
  (φ : ℍ[ℚ, a, b] ⊗[ℚ] (place r hr).adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) ((place r hr).adicCompletion ℚ))

set_option quotPrecheck false in
local notation "Vt" => CerednikDrinfeld.CosetGraph.Vert R (place r hr)

set_option quotPrecheck false in

local notation "ψ" => (Units.map (RingEquiv.toRingHom φ).toMonoidHom :
  (CerednikDrinfeld.CosetGraph.Loc a b (place r hr))ˣ →* (Matrix (Fin 2) (Fin 2) ((place r hr).adicCompletion ℚ))ˣ)

p2m_open "QuaternionAlgebra CerednikDrinfeld P2MW.S_CerednikDrinfeld_CosetGraph_exists_iso_tree_apply_coe_eq_smul_stdVertex.CerednikDrinfeld LT.LatticeTree CerednikDrinfeld.BruhatTits"

theorem coe_ψ (g : (Lv)ˣ) : ((ψ g : (M₂)ˣ) : M₂) = φ (g : Lv) := rfl

theorem ψ_surjective (X : (M₂)ˣ) : ∃ g : (Lv)ˣ, ψ g = X :=
  ⟨Units.map (RingEquiv.toRingHom φ.symm).toMonoidHom X, Units.ext (φ.apply_symm_apply _)⟩

theorem ψ_mem_K0_iff
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v) (g : (Lv)ˣ) :
    ψ g ∈ K0 𝔳 ↔ g ∈ Submodule.localBoxUnits R 𝔳 := by
  rw [mem_K0_iff, mem_intMat_iff, mem_intMat_iff, Submodule.mem_localBoxUnits_iff, SetLike.mem_coe,
    SetLike.mem_coe, hφR, hφR]
  rfl

theorem ψ_unitsMap_includeRight (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂)) (t : (𝕂)ˣ) :
    ψ (Units.map (Algebra.TensorProduct.includeRight : 𝕂 →ₐ[ℚ] Lv).toRingHom.toMonoidHom t) = scalarGL t := by
  apply Units.ext
  change φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] (t : 𝕂)) = (t : 𝕂) • (1 : M₂)
  exact hφ1 t

theorem ψ_smul_of_mem_scalarUnits (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    {s : (Lv)ˣ} (hs : s ∈ CosetGraph.scalarUnits 𝔳) (X : Vertex 𝓞v 𝕂) : ψ s • X = X := by
  obtain ⟨t, rfl⟩ := hs
  have h : ψ (Units.map (Algebra.TensorProduct.includeRight : 𝕂 →ₐ[ℚ] Lv).toRingHom.toMonoidHom t) =
      scalarGL t := ψ_unitsMap_includeRight r hr φ hφ1 t
  rw [h]
  exact scalarGL_smul 𝔳 t X

def actsLikeK0 : Subgroup (Lv)ˣ where
  carrier := {k | ∃ m ∈ K0 𝔳, ∀ X : Vertex 𝓞v 𝕂, ψ k • X = m • X}
  one_mem' := ⟨1, one_mem _, fun X => by rw [map_one]⟩
  mul_mem' := fun {x y} ⟨m₁, hm₁, h₁⟩ ⟨m₂, hm₂, h₂⟩ =>
    ⟨m₁ * m₂, mul_mem hm₁ hm₂, fun X => by rw [map_mul, mul_smul, mul_smul, h₂, h₁]⟩
  inv_mem' := fun {x} ⟨m, hm, h⟩ =>
    ⟨m⁻¹, inv_mem hm, fun X => by rw [map_inv, inv_smul_eq_iff, h, smul_inv_smul]⟩

theorem level_le_actsLikeK0 (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v) :
    CosetGraph.level R 𝔳 ≤ actsLikeK0 r hr φ := by
  refine sup_le ?_ ?_
  · rw [Subgroup.closure_le]
    intro k hk
    exact ⟨ψ k, (ψ_mem_K0_iff r hr R φ hφR k).2 hk, fun X => rfl⟩
  · intro s hs
    exact ⟨1, one_mem _, fun X => by rw [one_smul]; exact ψ_smul_of_mem_scalarUnits r hr φ hφ1 hs X⟩

theorem exists_mem_K0_forall_smul_eq (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v)
    {k : (Lv)ˣ} (hk : k ∈ CosetGraph.level R 𝔳) :
    ∃ m ∈ K0 𝔳, ∀ X : Vertex 𝓞v 𝕂, ψ k • X = m • X :=
  level_le_actsLikeK0 r hr R φ hφ1 hφR hk

theorem smul_stdVertex_of_mem_level (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v)
    {k : (Lv)ˣ} (hk : k ∈ CosetGraph.level R 𝔳) : ψ k • stdVertex 𝓞v 𝕂 = stdVertex 𝓞v 𝕂 := by
  obtain ⟨m, hm, h⟩ := exists_mem_K0_forall_smul_eq r hr R φ hφ1 hφR hk
  rw [h, smul_stdVertex_of_mem_K0 𝔳 hm]

theorem mem_level_of_smul_stdVertex (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v)
    {g : (Lv)ˣ} (h : ψ g • stdVertex 𝓞v 𝕂 = stdVertex 𝓞v 𝕂) : g ∈ CosetGraph.level R 𝔳 := by
  obtain ⟨c, hc⟩ := (smul_stdVertex_eq_iff 𝔳 (ψ g)).1 h
  let s : (Lv)ˣ := Units.map (Algebra.TensorProduct.includeRight : 𝕂 →ₐ[ℚ] Lv).toRingHom.toMonoidHom c
  have hs : s ∈ CosetGraph.scalarUnits 𝔳 := ⟨c, rfl⟩
  have hsg : s * g ∈ Submodule.localBoxUnits R 𝔳 := by
    rw [← ψ_mem_K0_iff r hr R φ hφR, map_mul, ψ_unitsMap_includeRight r hr φ hφ1]
    exact hc
  rw [← inv_mul_cancel_left s g]
  exact mul_mem (Subgroup.mem_sup_right (inv_mem hs)) (Subgroup.mem_sup_left (Subgroup.subset_closure hsg))

def vmap (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v) (x : Vt) : Vertex 𝓞v 𝕂 :=
  Quotient.liftOn' x (fun g : (Lv)ˣ => ψ g • stdVertex 𝓞v 𝕂) (fun g h hgh => by
    rw [QuotientGroup.leftRel_apply] at hgh
    change ψ g • stdVertex 𝓞v 𝕂 = ψ h • stdVertex 𝓞v 𝕂
    rw [← mul_inv_cancel_left g h, map_mul, mul_smul, smul_stdVertex_of_mem_level r hr R φ hφ1 hφR hgh])

theorem vmap_coe (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v) (g : (Lv)ˣ) :
    vmap r hr R φ hφ1 hφR ((g : (Lv)ˣ) : Vt) = ψ g • stdVertex 𝓞v 𝕂 := rfl

theorem vmap_injective (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v) :
    Function.Injective (vmap r hr R φ hφ1 hφR) := by
  intro x y
  induction x using QuotientGroup.induction_on with | H g => ?_
  induction y using QuotientGroup.induction_on with | H h => ?_
  intro hxy
  rw [vmap_coe, vmap_coe] at hxy
  apply QuotientGroup.eq.2
  apply mem_level_of_smul_stdVertex r hr R φ hφ1 hφR
  rw [map_mul, map_inv, mul_smul, inv_smul_eq_iff]
  exact hxy.symm

theorem vmap_surjective (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v) :
    Function.Surjective (vmap r hr R φ hφ1 hφR) := by
  intro X
  obtain ⟨M, hM⟩ := LT.LatticeTree.exists_act_stdVertex_eq 𝓞v 𝕂 X
  obtain ⟨g, rfl⟩ := ψ_surjective r hr φ M
  exact ⟨(g : Vt), hM⟩

theorem exists_ψ_nv_eq (hRo : IsOrder R)
    (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v) (hn : n ∈ primeHeckeSet R r) :
    ∃ k₁ ∈ K0 𝔳, ∃ k₂ ∈ K0 𝔳, ψ nv = k₁ * diagSnd (piK r hr) * k₂ := by
  have hloc := local_of_mem_primeHeckeSet r hr R hRo φ hφ1 hφR hn
  have e1 : φ (ev 𝔳 (n : 𝔹)) * φ (ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹)) = 1 := by
    rw [← φ.map_mul, ev_units_mul_inv, φ.map_one]
  have e2 : φ (ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹)) * φ (ev 𝔳 (n : 𝔹)) = 1 := by
    rw [← φ.map_mul, ev_units_inv_mul, φ.map_one]
  obtain ⟨K₁, K₁i, K₂, K₂i, hK₁, hK₁i, hK₂, hK₂i, e₁, e₁', e₂, e₂', hY⟩ :=
    Matrix.exists_eq_mul_diagonal_mul_of_forall_mem_adicCompletionIntegers r hr 𝔳 (q_mem_asIdeal r hr)
      (φ (ev 𝔳 (n : 𝔹))) (φ (ev 𝔳 ((n⁻¹ : (𝔹)ˣ) : 𝔹))) e1 e2 hloc.1 hloc.2.1 hloc.2.2.1 hloc.2.2.2
  refine ⟨⟨K₁, K₁i, e₁, e₁'⟩, ⟨hK₁, hK₁i⟩, ⟨K₂, K₂i, e₂, e₂'⟩, ⟨hK₂, hK₂i⟩, ?_⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_diagSnd_piK]
  exact hY

theorem vertRel_vmap_coe_mul (hRo : IsOrder R)
    (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v) (hn : n ∈ primeHeckeSet R r)
    (g k : (Lv)ˣ) (hk : k ∈ CosetGraph.level R 𝔳) :
    VertRel 𝓞v 𝕂 (vmap r hr R φ hφ1 hφR (g : Vt)) (vmap r hr R φ hφ1 hφR ((g * k * nv : (Lv)ˣ) : Vt)) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hnv⟩ := exists_ψ_nv_eq r hr n R φ hRo hφ1 hφR hn
  obtain ⟨m, hm, hmX⟩ := exists_mem_K0_forall_smul_eq r hr R φ hφ1 hφR hk
  refine ⟨latticeMap (ψ g * m * k₁) (stdLattice 𝓞v 𝕂),
    latticeMap (ψ g * m * k₁) (latticeMap (diagSnd (piK r hr)) (stdLattice 𝓞v 𝕂)),
    isFullLattice_stdLattice.map _, (isFullLattice_stdLattice.map _).map _, ?_, ?_,
    adjacentLattice_latticeMap _ (adjacentLattice_stdLattice_diagSnd_piK r hr)⟩
  · rw [vmap_coe]
    change (ψ g * m * k₁) • stdVertex 𝓞v 𝕂 = ψ g • stdVertex 𝓞v 𝕂
    rw [mul_smul, mul_smul, smul_stdVertex_of_mem_K0 𝔳 hk₁, smul_stdVertex_of_mem_K0 𝔳 hm]
  · rw [vmap_coe]
    change (ψ g * m * k₁) • ((diagSnd (piK r hr)) • stdVertex 𝓞v 𝕂) = ψ (g * k * nv) • stdVertex 𝓞v 𝕂
    rw [map_mul, map_mul, hnv]
    simp only [mul_smul]
    rw [smul_stdVertex_of_mem_K0 𝔳 hk₂, hmX]

theorem exists_eq_vmap_of_vertRel (hRo : IsOrder R)
    (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v) (hn : n ∈ primeHeckeSet R r)
    (g : (Lv)ˣ) {Y : Vertex 𝓞v 𝕂} (hY : VertRel 𝓞v 𝕂 (vmap r hr R φ hφ1 hφR (g : Vt)) Y) :
    ∃ k ∈ Submodule.localBoxUnits R 𝔳, Y = vmap r hr R φ hφ1 hφR ((g * k * nv : (Lv)ˣ) : Vt) := by
  obtain ⟨k₁, hk₁, k₂, hk₂, hnv⟩ := exists_ψ_nv_eq r hr n R φ hRo hφ1 hφR hn
  obtain ⟨L, L', hL, hL', hLx, rfl, ϖ, hϖ, hlow, hup⟩ := hY
  rw [vmap_coe] at hLx
  change Vertex.mk 𝓞v 𝕂 L hL =
    Vertex.mk 𝓞v 𝕂 (latticeMap (ψ g) (stdLattice 𝓞v 𝕂)) (isFullLattice_stdLattice.map _) at hLx
  rw [Vertex.mk_eq_mk_iff] at hLx
  obtain ⟨c, hc⟩ := hLx
  have hL_eq : L = latticeMap ((scalarGL c)⁻¹ * ψ g) (stdLattice 𝓞v 𝕂) := by
    rw [latticeMap_mul, ← hc, latticeMap_inv_latticeMap]
  have hup' : latticeMap ((scalarGL c)⁻¹ * ψ g)⁻¹ L' < stdLattice 𝓞v 𝕂 := by
    rw [← latticeMap_lt_latticeMap_iff ((scalarGL c)⁻¹ * ψ g), latticeMap_latticeMap_inv, ← hL_eq]
    exact hup
  have hlow' : latticeMap (scalarGL (piK r hr)) (stdLattice 𝓞v 𝕂) < latticeMap ((scalarGL c)⁻¹ * ψ g)⁻¹ L' := by
    rw [← latticeMap_scalarGL_unitOfNeZero_eq r hr hϖ, ← latticeMap_lt_latticeMap_iff ((scalarGL c)⁻¹ * ψ g),
      latticeMap_latticeMap_inv, ← latticeMap_mul, ← scalarGL_mul_comm, latticeMap_mul, ← hL_eq]
    exact hlow
  obtain ⟨m, hm, hN⟩ := exists_mem_K0_eq_latticeMap_mul_diagSnd r hr hlow' hup'
  have hL' : L' = latticeMap (((scalarGL c)⁻¹ * ψ g) * (m * diagSnd (piK r hr))) (stdLattice 𝓞v 𝕂) := by
    rw [latticeMap_mul, ← hN, latticeMap_latticeMap_inv]
  obtain ⟨k, hk⟩ := ψ_surjective r hr φ (m * k₁⁻¹)
  refine ⟨k, (ψ_mem_K0_iff r hr R φ hφR k).1 (hk ▸ mul_mem hm (inv_mem hk₁)), ?_⟩
  subst hL'
  rw [vmap_coe, map_mul, map_mul, hk, hnv]
  change (((scalarGL c)⁻¹ * ψ g) * (m * diagSnd (piK r hr))) • stdVertex 𝓞v 𝕂 = _
  simp only [mul_smul]
  rw [inv_smul_eq_iff, scalarGL_smul, smul_stdVertex_of_mem_K0 𝔳 hk₂, inv_smul_smul]

theorem main (hRo : IsOrder R)
    (hφ1 : ∀ t : 𝕂, φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : M₂))
    (hφR : ∀ x : Lv, x ∈ Submodule.localBox R 𝔳 ↔ ∀ i j, φ x i j ∈ 𝓞v) (hn : n ∈ primeHeckeSet R r) :
    ∃ e : CosetGraph.graph R 𝔳 nv ≃g tree 𝓞v 𝕂,
      (∀ g : (Lv)ˣ, e ((g : (Lv)ˣ) : Vt) = ψ g • stdVertex 𝓞v 𝕂) ∧
      (∀ γ g : (Lv)ˣ, e ((γ * g : (Lv)ˣ) : Vt) = ψ γ • e ((g : (Lv)ˣ) : Vt)) := by
  refine ⟨⟨Equiv.ofBijective (vmap r hr R φ hφ1 hφR)
    ⟨vmap_injective r hr R φ hφ1 hφR, vmap_surjective r hr R φ hφ1 hφR⟩, ?_⟩, fun g => rfl, fun γ g => ?_⟩
  · intro x y
    change (tree 𝓞v 𝕂).Adj (vmap r hr R φ hφ1 hφR x) (vmap r hr R φ hφ1 hφR y) ↔
      (CosetGraph.graph R 𝔳 nv).Adj x y
    induction x using QuotientGroup.induction_on with | H g => ?_
    induction y using QuotientGroup.induction_on with | H g' => ?_
    rw [tree_adj_iff]
    constructor
    · rintro ⟨hne, hrel | hrel⟩
      · obtain ⟨k, hk, hk'⟩ := exists_eq_vmap_of_vertRel r hr n R φ hRo hφ1 hφR hn g hrel
        exact ⟨fun h => hne (congrArg _ h), g, k, Subgroup.mem_sup_left (Subgroup.subset_closure hk),
          Or.inl ⟨rfl, vmap_injective r hr R φ hφ1 hφR hk'⟩⟩
      · obtain ⟨k, hk, hk'⟩ := exists_eq_vmap_of_vertRel r hr n R φ hRo hφ1 hφR hn g' hrel
        exact ⟨fun h => hne (congrArg _ h), g', k, Subgroup.mem_sup_left (Subgroup.subset_closure hk),
          Or.inr ⟨rfl, vmap_injective r hr R φ hφ1 hφR hk'⟩⟩
    · rintro ⟨hne, g₀, k, hk, h | h⟩
      · refine ⟨fun e => hne (vmap_injective r hr R φ hφ1 hφR e), Or.inl ?_⟩
        rw [h.1, h.2]
        exact vertRel_vmap_coe_mul r hr n R φ hRo hφ1 hφR hn g₀ k hk
      · refine ⟨fun e => hne (vmap_injective r hr R φ hφ1 hφR e), Or.inr ?_⟩
        rw [h.1, h.2]
        exact vertRel_vmap_coe_mul r hr n R φ hRo hφ1 hφR hn g₀ k hk
  · change vmap r hr R φ hφ1 hφR ((γ * g : (Lv)ˣ) : Vt) = ψ γ • vmap r hr R φ hφ1 hφR ((g : (Lv)ˣ) : Vt)
    rw [vmap_coe, vmap_coe, map_mul, mul_smul]

end Transport

end R5IsoTree
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_iso_tree_apply_coe_eq_smul_stdVertex.R5IsoTree"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_CosetGraph_exists_iso_tree_apply_coe_eq_smul_stdVertex.R5IsoTree"

open QuaternionAlgebra _root_.CerednikDrinfeld R5IsoTree in
theorem solution
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : IsOrder R)
    {r : ℕ} [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ t : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hφR : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ)
    {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hn : n ∈ primeHeckeSet R r) :
    ∃ e : CosetGraph.graph R v
          (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n) ≃g
        BruhatTits.tree (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ),
      (∀ g : (CosetGraph.Loc a b v)ˣ,
        e ((g : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v) =
          (Units.map φ.toRingHom.toMonoidHom g : GL (Fin 2) (v.adicCompletion ℚ)) •
            LT.LatticeTree.stdVertex (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) ∧
      (∀ γ g : (CosetGraph.Loc a b v)ˣ,
        e ((γ * g : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v) =
          (Units.map φ.toRingHom.toMonoidHom γ : GL (Fin 2) (v.adicCompletion ℚ)) •
            e ((g : (CosetGraph.Loc a b v)ˣ) : CosetGraph.Vert R v)) := by
  obtain rfl : v = place r (Fact.out : r.Prime) := eq_place_of_mem r Fact.out v hv
  exact main r Fact.out n R φ hR hφ hφR hn

namespace CerednikDrinfeld p2m_export "CerednikDrinfeld" "CosetGraph.Loc CosetGraph.scalarUnits CosetGraph.level CosetGraph.Vert CosetGraph.graph gl_smul_def gl_smul_mk adjacentLattice_latticeMap VertRel tree tree_adj_iff BruhatTits.tree" namespace CosetGraph p2m_export "CerednikDrinfeld.CosetGraph" "Loc scalarUnits level Vert graph" end CerednikDrinfeld.CosetGraph
p2m_open_scoped "CerednikDrinfeld CerednikDrinfeld.CosetGraph" in

theorem CerednikDrinfeld.CosetGraph.exists_iso_tree_apply_coe_eq_smul_stdVertex
    {a b : ℚ} {R : Submodule ℤ ℍ[ℚ, a, b]} (hR : QuaternionAlgebra.IsOrder R)
    {r : ℕ} [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (φ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ ≃+* Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ))
    (hφ : ∀ t : v.adicCompletion ℚ,
      φ ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] t) = t • (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)))
    (hφR : ∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ,
      x ∈ Submodule.localBox R v ↔ ∀ i j, φ x i j ∈ v.adicCompletionIntegers ℚ)
    {n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hn : n ∈ QuaternionAlgebra.primeHeckeSet R r) :
    ∃ e : CerednikDrinfeld.CosetGraph.graph R v
          (Units.map (Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b] v).toRingHom.toMonoidHom n) ≃g
        CerednikDrinfeld.BruhatTits.tree (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ),
      (∀ g : (CerednikDrinfeld.CosetGraph.Loc a b v)ˣ,
        e ((g : (CerednikDrinfeld.CosetGraph.Loc a b v)ˣ) : CerednikDrinfeld.CosetGraph.Vert R v) =
          (Units.map φ.toRingHom.toMonoidHom g : GL (Fin 2) (v.adicCompletion ℚ)) •
            LT.LatticeTree.stdVertex (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)) ∧
      (∀ γ g : (CerednikDrinfeld.CosetGraph.Loc a b v)ˣ,
        e ((γ * g : (CerednikDrinfeld.CosetGraph.Loc a b v)ˣ) : CerednikDrinfeld.CosetGraph.Vert R v) =
          (Units.map φ.toRingHom.toMonoidHom γ : GL (Fin 2) (v.adicCompletion ℚ)) •
            e ((g : (CerednikDrinfeld.CosetGraph.Loc a b v)ˣ) : CerednikDrinfeld.CosetGraph.Vert R v)) :=
  solution hR v hv φ hφ hφR hn

end S_CerednikDrinfeld_CosetGraph_exists_iso_tree_apply_coe_eq_smul_stdVertex
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_exists_iso_tree_apply_coe_eq_smul_stdVertex (solution)
