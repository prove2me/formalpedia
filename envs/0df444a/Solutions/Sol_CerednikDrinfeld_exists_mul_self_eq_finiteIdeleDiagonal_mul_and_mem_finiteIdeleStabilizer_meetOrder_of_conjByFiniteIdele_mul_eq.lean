-- Prove2me | solution 1 for CerednikDrinfeld.exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9bb440cf-bc5c-5978-ae81-051f36c92239

import Mathlib
import Definitions.Def_QuaternionAlgebra_EichlerOrder
import Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Definitions.Def_Submodule_LocalBox
import Theorems.Thm_QuaternionAlgebra_exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet
import Theorems.Thm_Submodule_mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox
import Theorems.Thm_Submodule_localBox_inf
import Theorems.Thm_Submodule_mem_localBox_conjByFiniteIdele_iff
import Theorems.Thm_QuaternionAlgebra_IsOrder_conjByFiniteIdele
import Theorems.Thm_QuaternionAlgebra_IsOrder_finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq
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

namespace ALSquare

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

theorem natCast_mem_asIdeal_place_iff (n : ℕ) : (n : 𝓞 ℚ) ∈ (𝔳).asIdeal ↔ q ∣ n := by
  rw [natCast_mem_asIdeal_iff, natGenerator_place]

theorem q_mem_asIdeal : (q : 𝓞 ℚ) ∈ (𝔳).asIdeal := (natCast_mem_asIdeal_place_iff q hq q).2 dvd_rfl

theorem q_notMem_asIdeal_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) : (q : 𝓞 ℚ) ∉ w.asIdeal := by
  rw [natCast_mem_asIdeal_iff]
  intro h
  have : Rat.HeightOneSpectrum.natGenerator w = q :=
    (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator w) hq).mp h
  apply hw
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  rw [primesEquiv_place]
  exact Subtype.ext this

theorem valuation_natCast_eq_one_of_notMem (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) (hn : (n : 𝓞 ℚ) ∉ w.asIdeal) :
    w.valuation ℚ (n : ℚ) = 1 := by
  rw [show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact (HeightOneSpectrum.valuation_eq_one_iff_notMem (K := ℚ) (v := w) (r := (n : 𝓞 ℚ))).2 hn

theorem valuation_q_eq_one_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) : w.valuation ℚ (q : ℚ) = 1 :=
  valuation_natCast_eq_one_of_notMem w q (q_notMem_asIdeal_of_ne q hq w hw)

theorem valuation_natCast_eq_one_of_not_dvd (n : ℕ) (hn : ¬ q ∣ n) : (𝔳).valuation ℚ (n : ℚ) = 1 :=
  valuation_natCast_eq_one_of_notMem _ n (mt (natCast_mem_asIdeal_place_iff q hq n).1 hn)

theorem valued_algebraMap (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) :
    Valued.v (algebraMap ℚ (w.adicCompletion ℚ) r) = w.valuation ℚ r := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w r

theorem algebraMap_natCast (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    algebraMap ℚ (w.adicCompletion ℚ) (n : ℚ) = (n : w.adicCompletion ℚ) := map_natCast _ n

theorem natCast_mem_integers (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    ((n : ℕ) : w.adicCompletion ℚ) ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, ← algebraMap_natCast, valued_algebraMap,
    show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ n from (map_natCast _ _).symm]
  exact HeightOneSpectrum.valuation_le_one w _

theorem inv_natCast_mem_integers_of_valuation (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ)
    (hc : w.valuation ℚ (c : ℚ) = 1) : ((c : ℕ) : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ← algebraMap_natCast, valued_algebraMap, hc, inv_one]

theorem inv_q_mem_integers_of_ne (w : HeightOneSpectrum (𝓞 ℚ)) (hw : w ≠ 𝔳) :
    ((q : ℕ) : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ :=
  inv_natCast_mem_integers_of_valuation w q (valuation_q_eq_one_of_ne q hq w hw)

theorem natCast_ne_zero_of_valuation (w : HeightOneSpectrum (𝓞 ℚ)) (c : ℕ) (hc : w.valuation ℚ (c : ℚ) = 1) :
    ((c : ℕ) : w.adicCompletion ℚ) ≠ 0 := by
  intro h
  have := valued_algebraMap w (c : ℚ)
  rw [algebraMap_natCast, h, map_zero, hc] at this
  exact zero_ne_one this

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
  rw [show (q : ℚ) = algebraMap (𝓞 ℚ) ℚ (q : 𝓞 ℚ) from (map_natCast _ _).symm,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton _ (by exact_mod_cast hq.ne_zero) (asIdeal_place_eq_span q hq)

theorem valued_q : Valued.v ((q : ℕ) : 𝕂) = WithZero.exp (-1) := by
  rw [← algebraMap_natCast, valued_algebraMap, valuation_q]

theorem q_ne_zero' : ((q : ℕ) : 𝕂) ≠ 0 := by
  intro h
  have := valued_q q hq
  rw [h, map_zero] at this
  exact WithZero.zero_ne_coe this

theorem q_mem_integers : ((q : ℕ) : 𝕂) ∈ 𝓞v := natCast_mem_integers (𝔳) q

theorem valued_le_one_of_mem {x : 𝕂} (hx : x ∈ 𝓞v) : Valued.v x ≤ 1 :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ (𝔳)).1 hx

theorem mem_integers_of_valued_le_one {x : 𝕂} (hx : Valued.v x ≤ 1) : x ∈ 𝓞v :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ (𝔳)).2 hx

theorem inv_q_notMem_integers : ((q : ℕ) : 𝕂)⁻¹ ∉ 𝓞v := by
  intro h
  have := valued_le_one_of_mem q hq h
  rw [map_inv₀, valued_q, ← WithZero.exp_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
  norm_num at this

theorem q_inv_mul_mem_integers_iff {x : 𝕂} (hx : x ∈ 𝓞v) :
    ((q : ℕ) : 𝕂)⁻¹ * x ∈ 𝓞v ↔ Valued.v x < 1 := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, map_inv₀, valued_q]
  by_cases hx0 : x = 0
  · simp [hx0]
  · obtain ⟨m, hm⟩ : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
      ⟨WithZero.log (Valued.v x), (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx0)).symm⟩
    rw [hm, ← WithZero.exp_neg, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp,
      WithZero.exp_lt_exp]
    omega

theorem inv_mem_integers_of_valued_eq_one {x : 𝕂} (h : Valued.v x = 1) : x⁻¹ ∈ 𝓞v := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h, inv_one]

theorem inv_mem_or_q_inv_mul_mem {x : 𝕂} (hx : x ∈ 𝓞v) :
    x⁻¹ ∈ 𝓞v ∨ ((q : ℕ) : 𝕂)⁻¹ * x ∈ 𝓞v := by
  rcases (valued_le_one_of_mem q hq hx).lt_or_eq with h | h
  · exact Or.inr ((q_inv_mul_mem_integers_iff q hq hx).2 h)
  · exact Or.inl (inv_mem_integers_of_valued_eq_one q hq h)

theorem valued_eq_one_of_mul_eq_one {x y : 𝕂} (hx : x ∈ 𝓞v) (hy : y ∈ 𝓞v) (h : x * y = 1) :
    Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, h, map_one]
  have hx1 := valued_le_one_of_mem q hq hx
  have hy1 := valued_le_one_of_mem q hq hy
  by_contra hne
  have hlt : Valued.v x < 1 := lt_of_le_of_ne hx1 hne
  have : Valued.v x * Valued.v y < 1 := by
    calc Valued.v x * Valued.v y ≤ Valued.v x * 1 := mul_le_mul_right hy1 _
      _ = Valued.v x := mul_one _
      _ < 1 := hlt
  rw [h1] at this
  exact lt_irrefl _ this

end Places

section Box

variable {D : Type*} [Ring D] [Algebra ℚ D] (Λ : Submodule ℤ D) (v : HeightOneSpectrum (𝓞 ℚ))

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ v
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ v
local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem tmul_mem_localBox {z : D} (hz : z ∈ Λ) {c : 𝕂} (hc : c ∈ 𝓞v) :
    z ⊗ₜ[ℚ] c ∈ Submodule.localBox Λ v :=
  AddSubgroup.subset_closure ⟨z, hz, c, hc, rfl⟩

theorem tmul_one_mem_localBox {z : D} (hz : z ∈ Λ) :
    z ⊗ₜ[ℚ] (1 : 𝕂) ∈ Submodule.localBox Λ v :=
  tmul_mem_localBox Λ v hz (one_mem _)

theorem localBox_mono {Λ Λ' : Submodule ℤ D} (h : Λ ≤ Λ') :
    Submodule.localBox Λ v ≤ Submodule.localBox Λ' v :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

theorem localBox_le_of_forall_tmul_mem (S : AddSubgroup (D ⊗[ℚ] 𝕂))
    (h : ∀ z ∈ Λ, ∀ c : 𝕂, c ∈ 𝓞v → z ⊗ₜ[ℚ] c ∈ S) : Submodule.localBox Λ v ≤ S :=
  (AddSubgroup.closure_le _).2 fun _ ⟨z, hz, c, hc, hx⟩ => hx ▸ h z hz c hc

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

omit Λ in

theorem one_tmul_comm (c : 𝕂) (x : D ⊗[ℚ] 𝕂) : ((1 : D) ⊗ₜ[ℚ] c) * x = x * ((1 : D) ⊗ₜ[ℚ] c) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [mul_zero, zero_mul]
  | tmul z d => rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, mul_comm]
  | add x y hx hy => rw [mul_add, add_mul, hx, hy]

omit Λ in
theorem one_tmul_mul_one_tmul (c d : 𝕂) :
    ((1 : D) ⊗ₜ[ℚ] c) * ((1 : D) ⊗ₜ[ℚ] d) = (1 : D) ⊗ₜ[ℚ] (c * d) := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

omit Λ v in
theorem one_tmul_one_eq (w : HeightOneSpectrum (𝓞 ℚ)) :
    ((1 : D) ⊗ₜ[ℚ] (1 : w.adicCompletion ℚ)) = (1 : D ⊗[ℚ] w.adicCompletion ℚ) := rfl

abbrev unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ :=
  Units.map (Submodule.finiteAdeleEvalAt D w).toRingHom.toMonoidHom g

omit Λ in
theorem coe_unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    ((unitAt w g : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) : D ⊗[ℚ] w.adicCompletion ℚ) =
      Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] 𝔸f) := rfl

omit Λ in
theorem unitAt_mul (w : HeightOneSpectrum (𝓞 ℚ)) (g h : (D ⊗[ℚ] 𝔸f)ˣ) : unitAt w (g * h) = unitAt w g * unitAt w h :=
  map_mul _ _ _

omit Λ in
theorem unitAt_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) : unitAt w g⁻¹ = (unitAt w g)⁻¹ :=
  map_inv _ _

omit Λ in
theorem coe_inv_unitAt (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    ((unitAt w g)⁻¹ : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) =
      Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) := by
  rw [← map_inv]; rfl

omit Λ in
theorem ev_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) =
      ((unitAt w g)⁻¹ : (D ⊗[ℚ] w.adicCompletion ℚ)ˣ) := (coe_inv_unitAt w g).symm

omit Λ in
theorem ev_smul (w : HeightOneSpectrum (𝓞 ℚ)) (r : ℚ) (x : D ⊗[ℚ] 𝔸f) :
    Submodule.finiteAdeleEvalAt D w (r • x) =
      ((1 : D) ⊗ₜ[ℚ] algebraMap ℚ (w.adicCompletion ℚ) r) * Submodule.finiteAdeleEvalAt D w x := by
  rw [map_smul, ratCast_smul_eq_one_tmul_mul]

theorem mem_finiteAdeleBox_iff (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤) (x : D ⊗[ℚ] 𝔸f) :
    x ∈ Submodule.finiteAdeleBox Λ ↔ ∀ w : HeightOneSpectrum (𝓞 ℚ),
      Submodule.finiteAdeleEvalAt D w x ∈ Submodule.localBox Λ w :=
  Submodule.mem_finiteAdeleBox_iff_forall_finiteAdeleEvalAt_mem_localBox Λ hfg hspan x

theorem localBox_eq_of_nsmul_mem {A B : Submodule ℤ D} (hBA : B ≤ A) (c : ℕ)
    (hcA : ∀ z ∈ A, c • z ∈ B) (w : HeightOneSpectrum (𝓞 ℚ)) (hcw : w.valuation ℚ (c : ℚ) = 1) :
    Submodule.localBox A w = Submodule.localBox B w := by
  refine le_antisymm ?_ (localBox_mono w hBA)
  refine localBox_le_of_forall_tmul_mem A w _ fun z hz d hd => ?_
  have hc0 : (c : ℚ) ≠ 0 := by
    intro h; rw [h, map_zero] at hcw; exact zero_ne_one hcw
  have : z ⊗ₜ[ℚ] d = (((c : ℕ) : ℚ) • z) ⊗ₜ[ℚ] (((c : ℕ) : ℚ)⁻¹ • d) := by
    rw [TensorProduct.smul_tmul, smul_smul, mul_inv_cancel₀ hc0, one_smul]
  rw [this, Nat.cast_smul_eq_nsmul]
  refine tmul_mem_localBox B w (hcA z hz) ?_
  rw [← algebraMap_smul (HeightOneSpectrum.adicCompletion ℚ w) ((c : ℚ)⁻¹) d, smul_eq_mul]
  refine mul_mem ?_ hd
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, valued_algebraMap, map_inv₀, hcw, inv_one]

theorem finiteAdeleBox_mono {A B : Submodule ℤ D} (h : A ≤ B) : Submodule.finiteAdeleBox A ≤ Submodule.finiteAdeleBox B :=
  AddSubgroup.closure_mono fun _ ⟨z, hz, c, hc, hx⟩ => ⟨z, h hz, c, hc, hx⟩

omit Λ in
theorem ev_units_mul_inv (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] 𝔸f) *
      Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) = 1 := by
  rw [← map_mul, Units.mul_inv, map_one]

omit Λ in
theorem ev_units_inv_mul (w : HeightOneSpectrum (𝓞 ℚ)) (g : (D ⊗[ℚ] 𝔸f)ˣ) :
    Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) *
      Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] 𝔸f) = 1 := by
  rw [← map_mul, Units.inv_mul, map_one]

theorem mem_localBox_conj_iff (hfg : Λ.FG) (hspan : Submodule.span ℚ (Λ : Set D) = ⊤)
    (g : (D ⊗[ℚ] 𝔸f)ˣ) (w : HeightOneSpectrum (𝓞 ℚ)) (y : D ⊗[ℚ] w.adicCompletion ℚ) :
    y ∈ Submodule.localBox (Submodule.conjByFiniteIdele Λ g) w ↔
      Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) * y *
        Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] 𝔸f) ∈ Submodule.localBox Λ w := by
  rw [Submodule.mem_localBox_conjByFiniteIdele_iff Λ hfg hspan g w y]
  set gw := Submodule.finiteAdeleEvalAt D w (g : D ⊗[ℚ] 𝔸f)
  set gwi := Submodule.finiteAdeleEvalAt D w ((g⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f)
  have h1 : gw * gwi = 1 := ev_units_mul_inv w g
  have h2 : gwi * gw = 1 := ev_units_inv_mul w g
  constructor
  · rintro ⟨t, ht, rfl⟩
    have e : gwi * (gw * t * gwi) * gw = (gwi * gw) * t * (gwi * gw) := by noncomm_ring
    rw [e, h2, one_mul, mul_one]; exact ht
  · intro h
    refine ⟨_, h, ?_⟩
    calc y = (gw * gwi) * y * (gw * gwi) := by rw [h1, one_mul, mul_one]
      _ = gw * (gwi * y * gw) * gwi := by noncomm_ring

end Box

section LocalMatrix

variable (q : ℕ) (hq : q.Prime)

local notation "𝕂" => HeightOneSpectrum.adicCompletion ℚ (place q hq)
local notation "𝓞v" => HeightOneSpectrum.adicCompletionIntegers ℚ (place q hq)
local notation "M₂" => Matrix (Fin 2) (Fin 2) (HeightOneSpectrum.adicCompletion ℚ (place q hq))
local notation "ϖ" => (((q : ℕ) : HeightOneSpectrum.adicCompletion ℚ (place q hq)))

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

theorem mem_intMat_iff (M : M₂) : M ∈ intMat q hq ↔ ∀ i j, M i j ∈ 𝓞v := Iff.rfl

theorem mem_intMat_iff' (M : M₂) :
    M ∈ intMat q hq ↔ M 0 0 ∈ 𝓞v ∧ M 0 1 ∈ 𝓞v ∧ M 1 0 ∈ 𝓞v ∧ M 1 1 ∈ 𝓞v := by
  rw [mem_intMat_iff]
  simp only [Fin.forall_fin_two]
  tauto

theorem of_mem_intMat_iff (x₀₀ x₀₁ x₁₀ x₁₁ : 𝕂) :
    (!![x₀₀, x₀₁; x₁₀, x₁₁] : M₂) ∈ intMat q hq ↔ x₀₀ ∈ 𝓞v ∧ x₀₁ ∈ 𝓞v ∧ x₁₀ ∈ 𝓞v ∧ x₁₁ ∈ 𝓞v := by
  rw [mem_intMat_iff']
  simp

theorem smul_mem_intMat {c : 𝕂} (hc : c ∈ 𝓞v) {M : M₂} (hM : M ∈ intMat q hq) : c • M ∈ intMat q hq :=
  fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact mul_mem hc (hM i j)

theorem det_mem_integers {M : M₂} (hM : M ∈ intMat q hq) : M.det ∈ 𝓞v := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

theorem adjugate_mem_intMat {M : M₂} (hM : M ∈ intMat q hq) : M.adjugate ∈ intMat q hq := by
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

theorem valued_det_eq_one {M Mi : M₂} (hM : M ∈ intMat q hq) (hMi : Mi ∈ intMat q hq) (h1 : M * Mi = 1) :
    Valued.v M.det = 1 :=
  valued_eq_one_of_mul_eq_one q hq (det_mem_integers q hq hM) (det_mem_integers q hq hMi) (det_mul_det_eq_one q hq h1)

theorem inv_mem_intMat_of_valued_det {M Mi : M₂} (hM : M ∈ intMat q hq) (h1 : M * Mi = 1) (h2 : Mi * M = 1)
    (hdet : Valued.v M.det = 1) : Mi ∈ intMat q hq := by
  rw [eq_smul_adjugate q hq h1 h2]
  exact smul_mem_intMat q hq (inv_mem_integers_of_valued_eq_one q hq hdet) (adjugate_mem_intMat q hq hM)

theorem conj_mem_intMat_iff {P Pi Y : M₂} (hP : P ∈ intMat q hq) (hPi : Pi ∈ intMat q hq)
    (h1 : P * Pi = 1) (h2 : Pi * P = 1) : Pi * Y * P ∈ intMat q hq ↔ Y ∈ intMat q hq := by
  refine ⟨fun h => ?_, fun hY => (intMat q hq).mul_mem ((intMat q hq).mul_mem hPi hY) hP⟩
  have := (intMat q hq).mul_mem ((intMat q hq).mul_mem hP h) hPi
  have e : P * (Pi * Y * P) * Pi = (P * Pi) * Y * (P * Pi) := by noncomm_ring
  rwa [e, h1, one_mul, mul_one] at this

theorem mul_mem_intMat_iff_left {P Pi Y : M₂} (hP : P ∈ intMat q hq) (hPi : Pi ∈ intMat q hq)
    (h2 : Pi * P = 1) : P * Y ∈ intMat q hq ↔ Y ∈ intMat q hq := by
  refine ⟨fun h => ?_, fun hY => (intMat q hq).mul_mem hP hY⟩
  have := (intMat q hq).mul_mem hPi h
  rwa [← mul_assoc, h2, one_mul] at this

def tM : M₂ := !![1, 0; 0, ϖ]

def tMi : M₂ := !![1, 0; 0, ϖ⁻¹]

def E00 : M₂ := !![1, 0; 0, 0]
def E01 : M₂ := !![0, 1; 0, 0]
def E10 : M₂ := !![0, 0; 1, 0]
def E11 : M₂ := !![0, 0; 0, 1]

theorem tM_mul_tMi : tM q hq * tMi q hq = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tM, tMi, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ (q_ne_zero' q hq)]

theorem tMi_mul_tM : tMi q hq * tM q hq = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [tM, tMi, Matrix.mul_apply, Fin.sum_univ_two, inv_mul_cancel₀ (q_ne_zero' q hq)]

theorem tM_mem : tM q hq ∈ intMat q hq := by
  rw [tM, of_mem_intMat_iff]
  exact ⟨one_mem _, zero_mem _, zero_mem _, q_mem_integers q hq⟩

theorem det_tM : (tM q hq).det = ϖ := by simp [tM, Matrix.det_fin_two_of]

theorem tMi_mul (Y : M₂) : tMi q hq * Y = !![Y 0 0, Y 0 1; ϖ⁻¹ * Y 1 0, ϖ⁻¹ * Y 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tMi, Matrix.mul_apply, Fin.sum_univ_two]

theorem tM_mul (Y : M₂) : tM q hq * Y = !![Y 0 0, Y 0 1; ϖ * Y 1 0, ϖ * Y 1 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tM, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_tM (Y : M₂) : Y * tM q hq = !![Y 0 0, Y 0 1 * ϖ; Y 1 0, Y 1 1 * ϖ] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tM, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_tMi (Y : M₂) : Y * tMi q hq = !![Y 0 0, Y 0 1 * ϖ⁻¹; Y 1 0, Y 1 1 * ϖ⁻¹] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [tMi, Matrix.mul_apply, Fin.sum_univ_two]

theorem tMi_mul_mul_tM (Y : M₂) :
    tMi q hq * Y * tM q hq = !![Y 0 0, Y 0 1 * ϖ; ϖ⁻¹ * Y 1 0, Y 1 1] := by
  rw [tMi_mul, mul_tM]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp
  rw [mul_comm, ← mul_assoc, mul_inv_cancel₀ (q_ne_zero' q hq), one_mul]

theorem tM_mul_mul_tMi (Y : M₂) :
    tM q hq * Y * tMi q hq = !![Y 0 0, Y 0 1 * ϖ⁻¹; ϖ * Y 1 0, Y 1 1] := by
  rw [tM_mul, mul_tMi]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp
  rw [mul_comm, ← mul_assoc, inv_mul_cancel₀ (q_ne_zero' q hq), one_mul]

theorem tM_mul_mul_tM (Y : M₂) :
    tM q hq * Y * tM q hq = !![Y 0 0, Y 0 1 * ϖ; ϖ * Y 1 0, ϖ * Y 1 1 * ϖ] := by
  rw [tM_mul, mul_tM]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem mul_E00_mul (A B : M₂) : A * E00 q hq * B = Matrix.of fun i j => A i 0 * B 0 j := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E00, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_E01_mul (A B : M₂) : A * E01 q hq * B = Matrix.of fun i j => A i 0 * B 1 j := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E01, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_E10_mul (A B : M₂) : A * E10 q hq * B = Matrix.of fun i j => A i 1 * B 0 j := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E10, Matrix.mul_apply, Fin.sum_univ_two]

theorem mul_E11_mul (A B : M₂) : A * E11 q hq * B = Matrix.of fun i j => A i 1 * B 1 j := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [E11, Matrix.mul_apply, Fin.sum_univ_two]

theorem E00_mem : E00 q hq ∈ intMat q hq ∧ tMi q hq * E00 q hq * tM q hq ∈ intMat q hq := by
  refine ⟨?_, ?_⟩
  · rw [E00, of_mem_intMat_iff]; exact ⟨one_mem _, zero_mem _, zero_mem _, zero_mem _⟩
  · rw [tMi_mul_mul_tM, of_mem_intMat_iff]; simp [E00, one_mem, zero_mem]

theorem E01_mem : E01 q hq ∈ intMat q hq ∧ tMi q hq * E01 q hq * tM q hq ∈ intMat q hq := by
  refine ⟨?_, ?_⟩
  · rw [E01, of_mem_intMat_iff]; exact ⟨zero_mem _, one_mem _, zero_mem _, zero_mem _⟩
  · rw [tMi_mul_mul_tM, of_mem_intMat_iff]; simp [E01, one_mem, zero_mem, q_mem_integers q hq]

theorem E11_mem : E11 q hq ∈ intMat q hq ∧ tMi q hq * E11 q hq * tM q hq ∈ intMat q hq := by
  refine ⟨?_, ?_⟩
  · rw [E11, of_mem_intMat_iff]; exact ⟨zero_mem _, zero_mem _, zero_mem _, one_mem _⟩
  · rw [tMi_mul_mul_tM, of_mem_intMat_iff]; simp [E11, one_mem, zero_mem]

theorem E10_mem : E10 q hq ∈ intMat q hq := by
  rw [E10, of_mem_intMat_iff]; exact ⟨zero_mem _, zero_mem _, one_mem _, zero_mem _⟩

theorem tMi_E10_tM_notMem : tMi q hq * E10 q hq * tM q hq ∉ intMat q hq := by
  rw [tMi_mul_mul_tM, of_mem_intMat_iff]
  simp only [E10, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Matrix.empty_val', mul_one, mul_zero, zero_mul]
  intro h
  exact inv_q_notMem_integers q hq h.2.2.1

theorem varpi_inv_mul_apply_mem {k ki : M₂} (h1 : k * ki = 1) (hk : k ∈ intMat q hq) (hki : ki ∈ intMat q hq)
    (hN : ∀ Y : M₂, Y ∈ intMat q hq → tMi q hq * Y * tM q hq ∈ intMat q hq →
      tM q hq * (k * Y * ki) * tMi q hq ∈ intMat q hq) :
    ϖ⁻¹ * k 0 0 ∈ 𝓞v := by
  have e1 : k 0 0 * ki 0 1 * ϖ⁻¹ ∈ 𝓞v := by
    have := hN _ (E00_mem q hq).1 (E00_mem q hq).2 0 1
    rw [tM_mul_mul_tMi, mul_E00_mul] at this
    simpa using this
  have e2 : k 0 0 * ki 1 1 * ϖ⁻¹ ∈ 𝓞v := by
    have := hN _ (E01_mem q hq).1 (E01_mem q hq).2 0 1
    rw [tM_mul_mul_tMi, mul_E01_mul] at this
    simpa using this
  have hone : k 1 0 * ki 0 1 + k 1 1 * ki 1 1 = 1 := by
    have := congrFun (congrFun h1 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e : ϖ⁻¹ * k 0 0 = k 1 0 * (k 0 0 * ki 0 1 * ϖ⁻¹) + k 1 1 * (k 0 0 * ki 1 1 * ϖ⁻¹) := by
    calc ϖ⁻¹ * k 0 0 = ϖ⁻¹ * k 0 0 * (k 1 0 * ki 0 1 + k 1 1 * ki 1 1) := by rw [hone, mul_one]
      _ = _ := by ring
  rw [e]
  exact add_mem (mul_mem (hk 1 0) e1) (mul_mem (hk 1 1) e2)

def gM (k : M₂) : M₂ := ϖ⁻¹ • (tM q hq * k * tM q hq)

theorem gM_eq (k : M₂) : gM q hq k = !![ϖ⁻¹ * k 0 0, k 0 1; k 1 0, ϖ * k 1 1] := by
  have hq0 := q_ne_zero' q hq
  rw [gM, tM_mul_mul_tM]
  ext i j : 1; fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply]
  · rw [mul_comm, mul_assoc, mul_inv_cancel₀ hq0, mul_one]
  · rw [← mul_assoc, inv_mul_cancel₀ hq0, one_mul]
  · rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hq0, one_mul, mul_comm]

theorem gM_mem {k : M₂} (hk : k ∈ intMat q hq) (h00 : ϖ⁻¹ * k 0 0 ∈ 𝓞v) : gM q hq k ∈ intMat q hq := by
  rw [gM_eq, of_mem_intMat_iff]
  exact ⟨h00, hk 0 1, hk 1 0, mul_mem (q_mem_integers q hq) (hk 1 1)⟩

theorem det_gM (k : M₂) : (gM q hq k).det = k.det := by
  have hq0 := q_ne_zero' q hq
  rw [gM_eq, Matrix.det_fin_two_of, Matrix.det_fin_two]
  field_simp

theorem gM_mul (k : M₂) : gM q hq k * k = ϖ⁻¹ • (tM q hq * k * (tM q hq * k)) := by
  rw [gM, smul_mul_assoc, mul_assoc]

theorem varpi_inv_mul_apply_one_zero_mem {k ki : M₂} (h2 : ki * k = 1) (hk : k ∈ intMat q hq)
    (hki : ki ∈ intMat q hq)
    (hN : tMi q hq * k * tM q hq * E01 q hq * (tMi q hq * ki * tM q hq) ∈ intMat q hq) :
    ϖ⁻¹ * k 1 0 ∈ 𝓞v := by
  have hq0 := q_ne_zero' q hq
  rw [mul_E01_mul, tMi_mul_mul_tM, tMi_mul_mul_tM] at hN
  have e1 : ϖ⁻¹ * k 1 0 * (ϖ⁻¹ * ki 1 0) ∈ 𝓞v := by
    have := hN 1 0
    simpa using this
  have e2 : ϖ⁻¹ * k 1 0 * ki 1 1 ∈ 𝓞v := by
    have := hN 1 1
    simpa using this
  have hone : ki 1 0 * k 0 1 + ki 1 1 * k 1 1 = 1 := by
    have := congrFun (congrFun h2 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have e : ϖ⁻¹ * k 1 0 =
      ϖ * (ϖ⁻¹ * k 1 0 * (ϖ⁻¹ * ki 1 0)) * k 0 1 + (ϖ⁻¹ * k 1 0 * ki 1 1) * k 1 1 := by
    calc ϖ⁻¹ * k 1 0 = ϖ⁻¹ * k 1 0 * (ki 1 0 * k 0 1 + ki 1 1 * k 1 1) := by rw [hone, mul_one]
      _ = _ := by field_simp
  rw [e]
  exact add_mem (mul_mem (mul_mem (q_mem_integers q hq) e1) (hk 0 1)) (mul_mem e2 (hk 1 1))

theorem tMi_mul_mul_tM_mem {k : M₂} (hk : k ∈ intMat q hq) (h10 : ϖ⁻¹ * k 1 0 ∈ 𝓞v) :
    tMi q hq * k * tM q hq ∈ intMat q hq := by
  rw [tMi_mul_mul_tM, of_mem_intMat_iff]
  exact ⟨hk 0 0, mul_mem (hk 0 1) (q_mem_integers q hq), h10, hk 1 1⟩

end LocalMatrix

section GlobalBox

variable {D : Type*} [Ring D] [Algebra ℚ D]

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

theorem mul_mem_box_of {Λ₁ Λ₂ Λ₃ : Submodule ℤ D}
    (hmul : ∀ x ∈ Λ₁, ∀ y ∈ Λ₂, x * y ∈ Λ₃)
    {x y : D ⊗[ℚ] 𝔸f} (hx : x ∈ Submodule.finiteAdeleBox Λ₁)
    (hy : y ∈ Submodule.finiteAdeleBox Λ₂) :
    x * y ∈ Submodule.finiteAdeleBox Λ₃ := by
  have step : ∀ s ∈ {x : D ⊗[ℚ] 𝔸f | ∃ z ∈ Λ₁, ∃ a : 𝔸f,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), a v ∈ v.adicCompletionIntegers ℚ) ∧ x = z ⊗ₜ[ℚ] a},
      Submodule.finiteAdeleBox Λ₂ ≤
        (Submodule.finiteAdeleBox Λ₃).comap (AddMonoidHom.mulLeft s) := by
    rintro s ⟨z, hz, c, hc, rfl⟩
    unfold Submodule.finiteAdeleBox
    rw [AddSubgroup.closure_le]
    rintro _ ⟨z', hz', c', hc', rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulLeft,
      Algebra.TensorProduct.tmul_mul_tmul]
    exact AddSubgroup.subset_closure
      ⟨z * z', hmul z hz z' hz', c * c', fun v => mul_mem (hc v) (hc' v), rfl⟩
  have key : Submodule.finiteAdeleBox Λ₁ ≤
      (Submodule.finiteAdeleBox Λ₃).comap (AddMonoidHom.mulRight y) := by
    unfold Submodule.finiteAdeleBox
    rw [AddSubgroup.closure_le]
    intro s hs
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, AddMonoidHom.coe_mulRight]
    exact step s hs hy
  exact key hx

theorem one_mem_box {Λ : Submodule ℤ D} (h1 : (1 : D) ∈ Λ) : (1 : D ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ :=
  AddSubgroup.subset_closure ⟨1, h1, 1, fun v =>
    (one_mem _ : (1 : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ), rfl⟩

theorem mem_stabilizer_of_val_mem_box {Λ : Submodule ℤ D}
    (hmul : ∀ x ∈ Λ, ∀ y ∈ Λ, x * y ∈ Λ) (u : (D ⊗[ℚ] 𝔸f)ˣ)
    (hu : (u : D ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ)
    (hu' : ((u⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ) :
    u ∈ Submodule.finiteIdeleStabilizer Λ := by
  rw [Submodule.mem_finiteIdeleStabilizer_iff]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mul_mem_box_of hmul hu hy
  · intro hx
    refine ⟨(u⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) • x, mul_mem_box_of hmul hu' hx, ?_⟩
    show (u : D ⊗[ℚ] 𝔸f) * (((u⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) * x) = x
    rw [← mul_assoc, Units.mul_inv, one_mul]

theorem val_mem_box_of_mem_stabilizer {Λ : Submodule ℤ D} (h1 : (1 : D) ∈ Λ) (u : (D ⊗[ℚ] 𝔸f)ˣ)
    (hu : u ∈ Submodule.finiteIdeleStabilizer Λ) :
    (u : D ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ ∧
      ((u⁻¹ : (D ⊗[ℚ] 𝔸f)ˣ) : D ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ := by
  have key : ∀ w : (D ⊗[ℚ] 𝔸f)ˣ, w ∈ Submodule.finiteIdeleStabilizer Λ →
      (w : D ⊗[ℚ] 𝔸f) ∈ Submodule.finiteAdeleBox Λ := by
    intro w hw
    rw [Submodule.mem_finiteIdeleStabilizer_iff] at hw
    have : (w : D ⊗[ℚ] 𝔸f) ∈ w • ((Submodule.finiteAdeleBox Λ : AddSubgroup (D ⊗[ℚ] 𝔸f)) :
        Set (D ⊗[ℚ] 𝔸f)) := ⟨1, one_mem_box h1, by show (w : D ⊗[ℚ] 𝔸f) * 1 = w; rw [mul_one]⟩
    rw [hw] at this
    exact this
  exact ⟨key u hu, key u⁻¹ (inv_mem hu)⟩

end GlobalBox

section Frame

variable {a b : ℚ}

set_option quotPrecheck false in
local notation "ℍ𝔸" => ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ
local notation "ev" => Submodule.finiteAdeleEvalAt ℍ[ℚ, a, b]

theorem local_facts (q' : ℕ) (hq' : q'.Prime) (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N) (hqq' : q' ≠ q)
    (n : (ℍ𝔸)ˣ) (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    (hnorm : Submodule.conjByFiniteIdele (CerednikDrinfeld.meetOrder R n) n = CerednikDrinfeld.meetOrder R n) :
    (∀ w : HeightOneSpectrum (𝓞 ℚ), w ≠ place q hq →
      ev w ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w ∧
      ev w ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w) ∧
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : (place q hq).adicCompletion ℚ)⁻¹) *
      (ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈
      Submodule.localBox R (place q hq) ∧
    ((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] ((q : ℕ) : (place q hq).adicCompletion ℚ)) *
      (ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈
      Submodule.localBox R (place q hq) ∧
    (∀ u : (ℍ𝔸)ˣ, ev (place q hq) ((u : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R (place q hq) →
      ev (place q hq) ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R (place q hq) →
      (∀ y ∈ Submodule.localBox R (place q hq),
        ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) *
          (ev (place q hq) ((u : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * y *
            (ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) *
          ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R (place q hq)) →
      (∀ y ∈ Submodule.localBox R (place q hq),
        ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) *
          (ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * y * ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) *
          (ev (place q hq) ((u : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈
          Submodule.localBox R (place q hq)) →
      ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((u : (ℍ𝔸)ˣ) : ℍ𝔸) *
          ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R (place q hq) ∧
      ev (place q hq) ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev (place q hq) ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) *
          ev (place q hq) ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R (place q hq)) := by
  classical
  set v : HeightOneSpectrum (𝓞 ℚ) := place q hq with hv

  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder
  have hRno : QuaternionAlgebra.IsOrder (Submodule.conjByFiniteIdele R n) :=
    QuaternionAlgebra.IsOrder.conjByFiniteIdele R hRo n
  have hSo : QuaternionAlgebra.IsOrder (CerednikDrinfeld.meetOrder R n) := by
    unfold CerednikDrinfeld.meetOrder; exact hRo.inf hRno

  have hq'v : (q' : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [hv, natCast_mem_asIdeal_place_iff]
    intro h
    exact hqq' ((Nat.prime_dvd_prime_iff_eq hq hq').1 h).symm
  have hNv : (N : 𝓞 ℚ) ∉ v.asIdeal := by
    rw [hv, natCast_mem_asIdeal_place_iff]; exact hqN
  obtain ⟨hn_away, φ, hφ1, hφR, k₀, k₀i, hk₀, hk₀i, hkk, hkk', hν, hνi⟩ :=
    QuaternionAlgebra.exists_ringEquiv_localBox_iff_evalAt_eq_diagonal_mul_of_mem_primeHeckeSet hdef hR
      q hq v (q_mem_asIdeal q hq) hq'v hNv n hn
  have hφΛ : ∀ x, x ∈ Submodule.localBox R v ↔ φ x ∈ intMat q hq := fun x => hφR x
  have hk₀' : k₀ ∈ intMat q hq := hk₀
  have hk₀i' : k₀i ∈ intMat q hq := hk₀i
  have hν' : φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) = tM q hq * k₀ := hν
  have hνi' : φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) = k₀i * tMi q hq := hνi
  have hφc : ∀ (c : v.adicCompletion ℚ) (x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ),
      φ (((1 : ℍ[ℚ, a, b]) ⊗ₜ[ℚ] c) * x) = c • φ x := fun c x => by
    rw [map_mul, hφ1, smul_mul_assoc, one_mul]
  have hq0 := q_ne_zero' q hq
  have hννi : φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) = 1 := by
    rw [← map_mul, ev_units_mul_inv, map_one]
  have hνiν : φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) = 1 := by
    rw [← map_mul, ev_units_inv_mul, map_one]

  have hS2 : ∀ y, y ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ↔ y ∈ Submodule.localBox R v ∧
      ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * y * ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R v := by
    intro y
    unfold CerednikDrinfeld.meetOrder
    rw [Submodule.localBox_inf R (Submodule.conjByFiniteIdele R n) hRo.fg hRo.spanTop hRno.fg hRno.spanTop v,
      AddSubgroup.mem_inf, mem_localBox_conj_iff R hRo.fg hRo.spanTop n v y]

  have hnS : ∀ y ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v,
      ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * y * ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈
        Submodule.localBox (CerednikDrinfeld.meetOrder R n) v := by
    intro y hy
    have : ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * y * ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈
        Submodule.localBox (Submodule.conjByFiniteIdele (CerednikDrinfeld.meetOrder R n) n) v :=
      (Submodule.mem_localBox_conjByFiniteIdele_iff (CerednikDrinfeld.meetOrder R n) hSo.fg hSo.spanTop n v _).2
        ⟨y, hy, rfl⟩
    rwa [hnorm] at this

  have hSmat : ∀ y, y ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v ↔
      (φ y ∈ intMat q hq ∧ tMi q hq * φ y * tM q hq ∈ intMat q hq) := by
    intro y
    rw [hS2 y, hφΛ, hφΛ, map_mul, map_mul, hν', hνi']
    have e : k₀i * tMi q hq * φ y * (tM q hq * k₀) = k₀i * (tMi q hq * φ y * tM q hq) * k₀ := by noncomm_ring
    rw [e, conj_mem_intMat_iff q hq hk₀' hk₀i' hkk hkk']

  have hNB : ∀ Y, Y ∈ intMat q hq → tMi q hq * Y * tM q hq ∈ intMat q hq →
      tM q hq * (k₀ * Y * k₀i) * tMi q hq ∈ intMat q hq := by
    intro Y hY hYI
    have hyS : φ.symm Y ∈ Submodule.localBox (CerednikDrinfeld.meetOrder R n) v := by
      rw [hSmat, RingEquiv.apply_symm_apply]; exact ⟨hY, hYI⟩
    have h2 := ((hS2 _).1 (hnS _ hyS)).1
    rw [hφΛ, map_mul, map_mul, hν', hνi', RingEquiv.apply_symm_apply] at h2
    have e : tM q hq * k₀ * Y * (k₀i * tMi q hq) = tM q hq * (k₀ * Y * k₀i) * tMi q hq := by noncomm_ring
    rwa [e] at h2
  have h00 := varpi_inv_mul_apply_mem q hq hkk hk₀' hk₀i' hNB
  have hg : gM q hq k₀ ∈ intMat q hq := gM_mem q hq hk₀' h00

  have hH_eq : ((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸))) = gM q hq k₀ * k₀ := by
    rw [hν', gM_mul, mul_assoc]
  have hH : ((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸))) ∈ intMat q hq := by
    rw [hH_eq]; exact (intMat q hq).mul_mem hg hk₀'
  have hHHi : (((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)))) *
      (((q : ℕ) : v.adicCompletion ℚ) •
        (φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)))) = 1 := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hq0, one_smul]
    calc _ = φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) *
        φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by noncomm_ring
      _ = 1 := by rw [hννi, mul_one, hννi]
  have hHiH : (((q : ℕ) : v.adicCompletion ℚ) •
        (φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)))) *
      (((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
        (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)))) = 1 := by
    rw [smul_mul_smul_comm, mul_inv_cancel₀ hq0, one_smul]
    calc _ = φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * (φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) *
        φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸))) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) := by noncomm_ring
      _ = 1 := by rw [hνiν, mul_one, hνiν]
  have hdetH : Valued.v (((q : ℕ) : v.adicCompletion ℚ)⁻¹ •
      (φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)))).det = 1 := by
    rw [hH_eq, Matrix.det_mul, map_mul, det_gM, valued_det_eq_one q hq hk₀' hk₀i' hkk, one_mul]
  have hHi : ((q : ℕ) : v.adicCompletion ℚ) •
      (φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * φ (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) ∈ intMat q hq :=
    inv_mem_intMat_of_valued_det q hq hH hHHi hHiH hdetH
  refine ⟨hn_away, ?_, ?_, ?_⟩
  · rw [hφΛ, hφc, map_mul]; exact hH
  · rw [hφΛ, hφc, map_mul]; exact hHi

  intro u hu hui hA hB
  set k : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := φ (ev v ((u : (ℍ𝔸)ˣ) : ℍ𝔸)) with hk_def
  set ki : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ) := φ (ev v ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) with hki_def
  have hk : k ∈ intMat q hq := (hφΛ _).1 hu
  have hki : ki ∈ intMat q hq := (hφΛ _).1 hui
  have hkki : k * ki = 1 := by rw [hk_def, hki_def, ← map_mul, ev_units_mul_inv, map_one]
  have hkik : ki * k = 1 := by rw [hk_def, hki_def, ← map_mul, ev_units_inv_mul, map_one]

  set y₀ : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ := φ.symm (k₀i * E01 q hq * k₀) with hy₀_def
  have hφy₀ : φ y₀ = k₀i * E01 q hq * k₀ := by rw [hy₀_def, RingEquiv.apply_symm_apply]
  have hyR : y₀ ∈ Submodule.localBox R v := by
    rw [hφΛ, hφy₀]
    exact (intMat q hq).mul_mem ((intMat q hq).mul_mem hk₀i' (E01_mem q hq).1) hk₀'

  have hyk : tMi q hq * k * tM q hq ∈ intMat q hq := by
    have h1 := hA _ hyR
    rw [hφΛ] at h1
    simp only [map_mul] at h1
    rw [hν', hνi', hφy₀] at h1
    have e : k₀i * tMi q hq * (k * (tM q hq * k₀) * (k₀i * E01 q hq * k₀) * (k₀i * tMi q hq * ki)) *
        (tM q hq * k₀) =
        k₀i * (tMi q hq * k * tM q hq * (k₀ * k₀i) * E01 q hq * (k₀ * k₀i) * (tMi q hq * ki * tM q hq)) * k₀ := by
      noncomm_ring
    rw [e, hkk, mul_one, mul_one, conj_mem_intMat_iff q hq hk₀' hk₀i' hkk hkk'] at h1
    exact tMi_mul_mul_tM_mem q hq hk (varpi_inv_mul_apply_one_zero_mem q hq hkik hk hki h1)

  have hyki : tMi q hq * ki * tM q hq ∈ intMat q hq := by
    have h1 := hB _ hyR
    rw [hφΛ] at h1
    simp only [map_mul] at h1
    rw [hν', hνi', hφy₀] at h1
    have e : k₀i * tMi q hq * ki * (tM q hq * k₀ * (k₀i * E01 q hq * k₀) * (k₀i * tMi q hq)) *
        (k * (tM q hq * k₀)) =
        k₀i * (tMi q hq * ki * tM q hq * (k₀ * k₀i) * E01 q hq * (k₀ * k₀i) * (tMi q hq * k * tM q hq)) * k₀ := by
      noncomm_ring
    rw [e, hkk, mul_one, mul_one, conj_mem_intMat_iff q hq hk₀' hk₀i' hkk hkk'] at h1
    exact tMi_mul_mul_tM_mem q hq hki (varpi_inv_mul_apply_one_zero_mem q hq hkki hki hk h1)
  refine ⟨?_, ?_⟩
  · rw [hφΛ, map_mul, map_mul, hν', hνi']
    have e : k₀i * tMi q hq * k * (tM q hq * k₀) = k₀i * (tMi q hq * k * tM q hq) * k₀ := by noncomm_ring
    rw [e, conj_mem_intMat_iff q hq hk₀' hk₀i' hkk hkk']
    exact hyk
  · rw [hφΛ, map_mul, map_mul, hν', hνi']
    have e : k₀i * tMi q hq * ki * (tM q hq * k₀) = k₀i * (tMi q hq * ki * tM q hq) * k₀ := by noncomm_ring
    rw [e, conj_mem_intMat_iff q hq hk₀' hk₀i' hkk hkk']
    exact hyki

theorem main (q' : ℕ) (hq' : q'.Prime) (hdef : QuaternionAlgebra.IsDefiniteRamifiedExactlyAt a b q')
    (R : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) (hR : QuaternionAlgebra.IsEichlerOrder R N)
    (q : ℕ) [hqF : Fact q.Prime] (hqN : ¬ q ∣ N) (hqq' : q' ≠ q)
    (n : (ℍ𝔸)ˣ) (hn : n ∈ QuaternionAlgebra.primeHeckeSet R q)
    (hnorm : Submodule.conjByFiniteIdele (CerednikDrinfeld.meetOrder R n) n = CerednikDrinfeld.meetOrder R n) :
    (∃ u ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n),
        n * n = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) * u) ∧
    (∀ u ∈ Submodule.finiteIdeleStabilizer R,
        Submodule.conjByFiniteIdele R (u * n) = Submodule.conjByFiniteIdele R n →
          u ∈ Submodule.finiteIdeleStabilizer (CerednikDrinfeld.meetOrder R n)) := by
  classical
  have hq : q.Prime := hqF.out
  obtain ⟨hn_away, hL5, hL6, hLoc⟩ := local_facts q' hq' hdef R N hR q hq hqN hqq' n hn hnorm
  set v : HeightOneSpectrum (𝓞 ℚ) := place q hq with hv
  set S : Submodule ℤ ℍ[ℚ, a, b] := CerednikDrinfeld.meetOrder R n with hS
  have hq0 : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero

  have hRo : QuaternionAlgebra.IsOrder R := hR.isOrder
  have hRno : QuaternionAlgebra.IsOrder (Submodule.conjByFiniteIdele R n) :=
    QuaternionAlgebra.IsOrder.conjByFiniteIdele R hRo n
  have hSo : QuaternionAlgebra.IsOrder S := by
    rw [hS]; unfold CerednikDrinfeld.meetOrder; exact hRo.inf hRno
  have hmulR : ∀ (w : HeightOneSpectrum (𝓞 ℚ)) (x y : ℍ[ℚ, a, b] ⊗[ℚ] w.adicCompletion ℚ),
      x ∈ Submodule.localBox R w → y ∈ Submodule.localBox R w → x * y ∈ Submodule.localBox R w :=
    fun w x y hx hy => mul_mem_localBox R w (fun _ _ h1 h2 => hRo.mul_mem h1 h2) hx hy
  have hmulS : ∀ x ∈ S, ∀ y ∈ S, x * y ∈ S := fun x hx y hy => hSo.mul_mem hx hy
  obtain ⟨hn1, hn2, hn3, hn4⟩ := hn
  have hnw : ∀ w, ev w ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w :=
    (mem_finiteAdeleBox_iff R hRo.fg hRo.spanTop _).1 hn1
  have hniw : ∀ w, w ≠ v → ev w ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w :=
    fun w hw => (hn_away w hw).2

  have hboxS : Submodule.finiteAdeleBox S = Submodule.finiteAdeleBox R ⊓
      (Submodule.finiteAdeleBox R).map
        ((AddMonoidHom.mulRight ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)).comp (AddMonoidHom.mulLeft ((n : (ℍ𝔸)ˣ) : ℍ𝔸))) := by
    rw [hS]
    exact (QuaternionAlgebra.IsOrder.finiteAdeleBox_inf_conjByFiniteIdele_eq_and_finiteIdeleStabilizer_le R hRo n).1
  have mem_boxS : ∀ x : ℍ𝔸, x ∈ Submodule.finiteAdeleBox R →
      ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * x * ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox R →
      x ∈ Submodule.finiteAdeleBox S := by
    intro x hx hx'
    rw [hboxS]
    refine ⟨hx, ⟨_, hx', ?_⟩⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.coe_mulLeft, AddMonoidHom.coe_mulRight]
    calc _ = (((n : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) * x * (((n : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
          noncomm_ring
      _ = x := by rw [Units.mul_inv, one_mul, mul_one]
  refine ⟨?_, ?_⟩
  ·
    set c : (ℍ𝔸)ˣ := Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
      (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
        (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) with hc_def
    have hc : ((c : (ℍ𝔸)ˣ) : ℍ𝔸) = (q : ℚ) • (1 : ℍ𝔸) := by
      rw [hc_def, Submodule.val_finiteIdeleDiagonal_apply, Units.coe_map]
      change (algebraMap ℚ ℍ[ℚ, a, b] (q : ℚ)) ⊗ₜ[ℚ] (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) = (q : ℚ) • (1 : ℍ𝔸)
      rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul']
      rfl
    have hci : ((c⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (q : ℚ)⁻¹ • (1 : ℍ𝔸) := by
      have e : ((c⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = ((c⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * (((c : (ℍ𝔸)ˣ) : ℍ𝔸) * ((q : ℚ)⁻¹ • (1 : ℍ𝔸))) := by
        rw [hc, smul_mul_smul_comm, mul_inv_cancel₀ hq0, one_smul, mul_one, mul_one]
      rw [e, ← mul_assoc, Units.inv_mul, one_mul]
    set u : (ℍ𝔸)ˣ := c⁻¹ * (n * n) with hu_def
    have hu : ((u : (ℍ𝔸)ˣ) : ℍ𝔸) = (q : ℚ)⁻¹ • (((n : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
      rw [hu_def, Units.val_mul, Units.val_mul, hci, smul_mul_assoc, one_mul]
    have hui : ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) = (q : ℚ) • (((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
      rw [hu_def, mul_inv_rev, inv_inv, mul_inv_rev, Units.val_mul, Units.val_mul, hc, mul_smul_comm, mul_one]

    have hxR : (q : ℚ)⁻¹ • (((n : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈ Submodule.finiteAdeleBox R := by
      rw [mem_finiteAdeleBox_iff R hRo.fg hRo.spanTop]
      intro w
      rw [ev_smul, map_inv₀, algebraMap_natCast, map_mul]
      by_cases hw : w = v
      · subst hw; exact hL5
      · exact one_tmul_mul_mem_localBox R w (hmulR w _ _ (hnw w) (hnw w)) (inv_q_mem_integers_of_ne q hq w hw)
    have hxiR : (q : ℚ) • (((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈ Submodule.finiteAdeleBox R := by
      rw [mem_finiteAdeleBox_iff R hRo.fg hRo.spanTop]
      intro w
      rw [ev_smul, algebraMap_natCast, map_mul]
      by_cases hw : w = v
      · subst hw; exact hL6
      · exact one_tmul_mul_mem_localBox R w (hmulR w _ _ (hniw w hw) (hniw w hw)) (natCast_mem_integers w q)

    have huS : ((u : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox S := by
      rw [hu]
      refine mem_boxS _ hxR ?_
      have e : ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((q : ℚ)⁻¹ • (((n : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n : (ℍ𝔸)ˣ) : ℍ𝔸))) *
          ((n : (ℍ𝔸)ˣ) : ℍ𝔸) = (q : ℚ)⁻¹ • (((n : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
        rw [mul_smul_comm, smul_mul_assoc, ← mul_assoc, Units.inv_mul, one_mul]
      rw [e]; exact hxR
    have huiS : ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.finiteAdeleBox S := by
      rw [hui]
      refine mem_boxS _ hxiR ?_
      have e : ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((q : ℚ) • (((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) *
          ((n : (ℍ𝔸)ˣ) : ℍ𝔸) = (q : ℚ) • (((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) := by
        rw [mul_smul_comm, smul_mul_assoc, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
      rw [e]; exact hxiR
    refine ⟨u, mem_stabilizer_of_val_mem_box hmulS u huS huiS, ?_⟩
    rw [hu_def, mul_inv_cancel_left]
  ·
    intro u hu hyp
    obtain ⟨huR, huiR⟩ := val_mem_box_of_mem_stabilizer hRo.one_mem u hu
    have huw : ∀ w, ev w ((u : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w :=
      (mem_finiteAdeleBox_iff R hRo.fg hRo.spanTop _).1 huR
    have huiw : ∀ w, ev w ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R w :=
      (mem_finiteAdeleBox_iff R hRo.fg hRo.spanTop _).1 huiR

    have hA : ∀ y ∈ Submodule.localBox R v,
        ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) *
          (ev v ((u : (ℍ𝔸)ˣ) : ℍ𝔸) * ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * y *
            (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev v ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸))) *
          ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈ Submodule.localBox R v := by
      intro y hy
      have h1 : ev v ((u : (ℍ𝔸)ˣ) : ℍ𝔸) * ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * y *
          (ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev v ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈
          Submodule.localBox (Submodule.conjByFiniteIdele R (u * n)) v := by
        refine (Submodule.mem_localBox_conjByFiniteIdele_iff R hRo.fg hRo.spanTop (u * n) v _).2 ⟨y, hy, ?_⟩
        rw [mul_inv_rev, Units.val_mul, Units.val_mul, map_mul, map_mul]
      rw [hyp] at h1
      exact (mem_localBox_conj_iff R hRo.fg hRo.spanTop n v _).1 h1
    have hB : ∀ y ∈ Submodule.localBox R v,
        ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ev v ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) *
          (ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * y * ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸)) *
          (ev v ((u : (ℍ𝔸)ˣ) : ℍ𝔸) * ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸)) ∈ Submodule.localBox R v := by
      intro y hy
      have h1 : ev v ((n : (ℍ𝔸)ˣ) : ℍ𝔸) * y * ev v ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) ∈
          Submodule.localBox (Submodule.conjByFiniteIdele R n) v :=
        (Submodule.mem_localBox_conjByFiniteIdele_iff R hRo.fg hRo.spanTop n v _).2 ⟨y, hy, rfl⟩
      rw [← hyp] at h1
      have h2 := (mem_localBox_conj_iff R hRo.fg hRo.spanTop (u * n) v _).1 h1
      rwa [mul_inv_rev, Units.val_mul, Units.val_mul, map_mul, map_mul] at h2
    obtain ⟨hL7, hL8⟩ := hLoc u (huw v) (huiw v) hA hB

    have hxR : ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((u : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈
        Submodule.finiteAdeleBox R := by
      rw [mem_finiteAdeleBox_iff R hRo.fg hRo.spanTop]
      intro w
      rw [map_mul, map_mul]
      by_cases hw : w = v
      · subst hw; exact hL7
      · exact hmulR w _ _ (hmulR w _ _ (hniw w hw) (huw w)) (hnw w)
    have hxiR : ((n⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((u⁻¹ : (ℍ𝔸)ˣ) : ℍ𝔸) * ((n : (ℍ𝔸)ˣ) : ℍ𝔸) ∈
        Submodule.finiteAdeleBox R := by
      rw [mem_finiteAdeleBox_iff R hRo.fg hRo.spanTop]
      intro w
      rw [map_mul, map_mul]
      by_cases hw : w = v
      · subst hw; exact hL8
      · exact hmulR w _ _ (hmulR w _ _ (hniw w hw) (huiw w)) (hnw w)
    exact mem_stabilizer_of_val_mem_box hmulS u (mem_boxS _ huR hxR) (mem_boxS _ huiR hxiR)

end Frame

end ALSquare

end

open scoped Quaternion TensorProduct NumberField Pointwise
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) {N : ℕ} (q : ℕ) [Fact q.Prime]
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (hR : IsEichlerOrder R N) (hqN : ¬ q ∣ N) {q' : ℕ} [Fact q'.Prime] (hqq' : q' ≠ q)
    (hdef : IsDefiniteRamifiedExactlyAt a b q') (hnH : n ∈ primeHeckeSet R q)
    (hn : IsEichlerOrder (meetOrder R n) (N * q))
    (hnorm : Submodule.conjByFiniteIdele (meetOrder R n) n = meetOrder R n) :
    (∃ u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n),
        n * n = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]
          (Units.map (algebraMap ℚ ℍ[ℚ, a, b]).toMonoidHom
            (Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero))) * u) ∧
    (∀ u ∈ Submodule.finiteIdeleStabilizer R,
        Submodule.conjByFiniteIdele R (u * n) = Submodule.conjByFiniteIdele R n →
          u ∈ Submodule.finiteIdeleStabilizer (meetOrder R n)) :=
  ALSquare.main q' Fact.out hdef R N hR q hqN hqq' n hnH hnorm

end S_CerednikDrinfeld_exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq
end P2MW
export P2MW.S_CerednikDrinfeld_exists_mul_self_eq_finiteIdeleDiagonal_mul_and_mem_finiteIdeleStabilizer_meetOrder_of_conjByFiniteIdele_mul_eq (solution)
