-- Prove2me | solution 1 for BaconThesis.Collective.eq_8_41_8_43
-- status  : ACCEPTED   (prove)
-- author  : @typh
-- created : 2026-11-16T19:58:39.560535+00:00
-- url     : https://prove2.me/submissions/8d9320e8-926c-4f93-82d5-c34fac176e90

import Mathlib
import Definitions.Def_BBPSSW_Distill_pauli
import Definitions.Def_BaconThesis_Collective_onQubit
import Definitions.Def_BaconThesis_Collective_collS
import Definitions.Def_BaconThesis_Collective_BlockIdx
import Definitions.Def_BaconThesis_Collective_degeneracy
import Definitions.Def_BaconThesis_Collective_spinRep
import Definitions.Def_BaconThesis_Collective_blockOp

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace BaconThesis.Collective.Sol841

open scoped InnerProductSpace
open Module

section Ladder

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- Raising `P`, lowering `M = P†` and weight `Z = Z†` with `[P, M] = 2Z`, `[Z, M] = -M`,
`[Z, P] = P`. -/
structure Ladder (P M Z : E →ₗ[ℂ] E) : Prop where
  adj : ∀ x y, ⟪M x, y⟫_ℂ = ⟪x, P y⟫_ℂ
  zsa : ∀ x y, ⟪Z x, y⟫_ℂ = ⟪x, Z y⟫_ℂ
  pm : ∀ x, P (M x) - M (P x) = (2 : ℂ) • Z x
  zm : ∀ x, Z (M x) - M (Z x) = - M x
  zp : ∀ x, Z (P x) - P (Z x) = P x

variable {P M Z : E →ₗ[ℂ] E} (h : Ladder P M Z)
include h

lemma Ladder.adj' (x y : E) : ⟪x, M y⟫_ℂ = ⟪P x, y⟫_ℂ := by
  rw [← inner_conj_symm, h.adj, inner_conj_symm]

lemma Ladder.M_eig {x : E} {μ : ℂ} (hx : Z x = μ • x) : Z (M x) = (μ - 1) • M x := by
  have := h.zm x
  rw [hx, map_smul, sub_eq_iff_eq_add] at this
  rw [this]; module

lemma Ladder.P_eig {x : E} {μ : ℂ} (hx : Z x = μ • x) : Z (P x) = (μ + 1) • P x := by
  have := h.zp x
  rw [hx, map_smul, sub_eq_iff_eq_add] at this
  rw [this]; module

lemma Ladder.z_pow {u : E} {J : ℂ} (hu : Z u = J • u) (k : ℕ) :
    Z ((M ^ k) u) = (J - k) • (M ^ k) u := by
  induction k with
  | zero => simp [hu]
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, h.M_eig ih]
    push_cast; congr 1; ring

lemma Ladder.p_pow {u : E} {d : ℕ} (hu0 : P u = 0) (hu : Z u = ((d : ℂ) / 2) • u) (k : ℕ) :
    P ((M ^ (k + 1)) u) = (((k : ℂ) + 1) * ((d : ℂ) - k)) • (M ^ k) u := by
  induction k with
  | zero =>
    have := h.pm u
    rw [hu0, map_zero, sub_zero, hu] at this
    simp only [pow_one, pow_zero, Module.End.one_apply, CharP.cast_eq_zero, zero_add, one_mul,
      sub_zero]
    rw [this]; module
  | succ k ih =>
    have := h.pm ((M ^ (k + 1)) u)
    rw [ih, map_smul, h.z_pow hu, sub_eq_iff_eq_add] at this
    rw [pow_succ' M (k + 1), Module.End.mul_apply, this, ← Module.End.mul_apply, ← pow_succ']
    push_cast
    module

/-- `∏_{j<k} (j+1)(d-j)`, the squared norm of `M^k u` for a unit highest-weight vector `u`. -/
def F (d k : ℕ) : ℂ := ∏ j ∈ Finset.range k, (((j : ℂ) + 1) * ((d : ℂ) - j))

lemma Ladder.inner_pow {u u' : E} {d : ℕ} (hu0 : P u = 0) (hu : Z u = ((d : ℂ) / 2) • u)
    (hu0' : P u' = 0) (l : ℕ) : ∀ k : ℕ,
    ⟪(M ^ k) u, (M ^ l) u'⟫_ℂ = if k = l then F d k * ⟪u, u'⟫_ℂ else 0 := by
  induction l with
  | zero =>
    intro k
    rcases k with _ | k
    · simp [F]
    · rw [pow_succ', Module.End.mul_apply, h.adj, pow_zero, Module.End.one_apply, hu0',
        inner_zero_right]
      simp
  | succ l ih =>
    intro k
    rw [pow_succ', Module.End.mul_apply, h.adj']
    rcases k with _ | k
    · rw [pow_zero, Module.End.one_apply, hu0, inner_zero_left]; simp
    · rw [h.p_pow hu0 hu, inner_smul_left, ih k]
      have hc : (starRingEnd ℂ) (((k : ℂ) + 1) * ((d : ℂ) - k)) = ((k : ℂ) + 1) * ((d : ℂ) - k) := by
        simp [map_mul, map_sub, map_add]
      rw [hc]
      by_cases hk : k = l
      · subst hk; rw [if_pos rfl, if_pos rfl, F, F, Finset.prod_range_succ]; ring
      · rw [if_neg hk, if_neg (fun e => hk (Nat.succ_injective e)), mul_zero]

lemma Ladder.M_top {u : E} {d : ℕ} (hu0 : P u = 0) (hu : Z u = ((d : ℂ) / 2) • u) :
    (M ^ (d + 1)) u = 0 := by
  have := h.inner_pow hu0 hu hu0 (d + 1) (d + 1)
  rw [if_pos rfl] at this
  have hF : F d (d + 1) = 0 :=
    Finset.prod_eq_zero (Finset.self_mem_range_succ d) (by simp)
  rw [hF, zero_mul] at this
  exact inner_self_eq_zero.1 this

lemma Ladder.normM (x : E) {ν : ℂ} (hx : Z x = ν • x) :
    ⟪M x, M x⟫_ℂ = ⟪P x, P x⟫_ℂ + 2 * ν * ⟪x, x⟫_ℂ := by
  rw [h.adj]
  have := h.pm x
  rw [sub_eq_iff_eq_add] at this
  rw [this, inner_add_right, ← h.adj', hx, inner_smul_right, inner_smul_right]
  ring

lemma Ladder.M_inj {x : E} {ν : ℝ} (hν : 0 < ν) (hx : Z x = (ν : ℂ) • x) (h0 : M x = 0) :
    x = 0 := by
  have := h.normM x hx
  rw [h0, inner_zero_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
  have h2 : ((‖P x‖ ^ 2 + 2 * ν * ‖x‖ ^ 2 : ℝ) : ℂ) = 0 := by
    push_cast; linear_combination -this
  have h3 : ‖P x‖ ^ 2 + 2 * ν * ‖x‖ ^ 2 = 0 := by exact_mod_cast h2
  have h4 : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖P x‖, sq_nonneg ‖x‖]
  exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4)

lemma Ladder.P_inj {x : E} {ν : ℝ} (hν : ν < 0) (hx : Z x = (ν : ℂ) • x) (h0 : P x = 0) :
    x = 0 := by
  have := h.normM x hx
  rw [h0, inner_zero_left, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at this
  have h2 : ((‖M x‖ ^ 2 - 2 * ν * ‖x‖ ^ 2 : ℝ) : ℂ) = 0 := by
    push_cast; linear_combination this
  have h3 : ‖M x‖ ^ 2 - 2 * ν * ‖x‖ ^ 2 = 0 := by exact_mod_cast h2
  have h4 : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖M x‖, sq_nonneg ‖x‖]
  exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h4)

omit h

variable (M Z) in
/-- The image of the next-higher weight space under lowering. -/
noncomputable def Rg (μ : ℂ) : Submodule ℂ E := (Module.End.eigenspace Z (μ + 1)).map M

variable (M Z) in
/-- Highest-weight vectors of weight `μ`: the part of the weight space orthogonal to `Rg μ`. -/
noncomputable def Kh (μ : ℂ) : Submodule ℂ E := (Rg M Z μ)ᗮ ⊓ Module.End.eigenspace Z μ

include h

lemma Ladder.Rg_le (μ : ℂ) : Rg M Z μ ≤ Module.End.eigenspace Z μ := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx
  rw [Module.End.mem_eigenspace_iff, h.M_eig hx, add_sub_cancel_right]

lemma Ladder.Kh_P {μ : ℂ} {x : E} (hx : x ∈ Kh M Z μ) : P x = 0 := by
  have hx1 := hx.1
  have hx2 : Z x = μ • x := Module.End.mem_eigenspace_iff.1 hx.2
  have hm : M (P x) ∈ Rg M Z μ :=
    ⟨P x, Module.End.mem_eigenspace_iff.2 (h.P_eig hx2), rfl⟩
  have h0 := (Submodule.mem_orthogonal _ _).1 hx1 _ hm
  rw [← inner_conj_symm, h.adj', map_eq_zero_iff _ (RingHom.injective _)] at h0
  exact inner_self_eq_zero.1 h0

lemma Ladder.Kh_eig {μ : ℂ} {x : E} (hx : x ∈ Kh M Z μ) : Z x = μ • x :=
  Module.End.mem_eigenspace_iff.1 hx.2

lemma Ladder.finrank_Rg {μ : ℂ} {ν : ℝ} (hν : 0 < ν) (he : μ + 1 = ν) :
    finrank ℂ (Rg M Z μ) = finrank ℂ (Module.End.eigenspace Z (μ + 1)) := by
  have hr : Rg M Z μ = LinearMap.range (M ∘ₗ (Module.End.eigenspace Z (μ + 1)).subtype) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]; rfl
  rw [hr, LinearMap.finrank_range_of_inj]
  intro x y hxy
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at hxy
  have hm : M ((x : E) - y) = 0 := by rw [map_sub, hxy, sub_self]
  have hz : Z ((x : E) - y) = (ν : ℂ) • ((x : E) - y) := by
    rw [← he]; exact Module.End.mem_eigenspace_iff.1 (sub_mem x.2 y.2)
  exact Subtype.ext (sub_eq_zero.1 (h.M_inj hν hz hm))

lemma Ladder.finrank_Kh {μ : ℂ} {ν : ℝ} (hν : 0 < ν) (he : μ + 1 = ν) :
    finrank ℂ (Kh M Z μ) + finrank ℂ (Module.End.eigenspace Z (μ + 1)) = finrank ℂ (Module.End.eigenspace Z μ) := by
  rw [← h.finrank_Rg hν he, add_comm]
  exact Submodule.finrank_add_inf_finrank_orthogonal (h.Rg_le μ)

lemma Ladder.Kh_neg {μ : ℂ} {ν : ℝ} (hν : ν < 0) (he : μ = ν) {x : E} (hx : x ∈ Kh M Z μ) :
    x = 0 :=
  h.P_inj hν (he ▸ h.Kh_eig hx) (h.Kh_P hx)

lemma Ladder.span_step {S : Submodule ℂ E} (hS : ∀ x ∈ S, M x ∈ S) (μ : ℂ)
    (h1 : Module.End.eigenspace Z (μ + 1) ≤ S) (h2 : Kh M Z μ ≤ S) : Module.End.eigenspace Z μ ≤ S := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := (Rg M Z μ).exists_add_mem_mem_orthogonal x
  have hzV : z ∈ Module.End.eigenspace Z μ := by
    have := sub_mem hx (h.Rg_le μ hy)
    rwa [add_sub_cancel_left] at this
  refine S.add_mem ?_ (h2 ⟨hz, hzV⟩)
  obtain ⟨w, hw, rfl⟩ := hy
  exact hS w (h1 hw)

end Ladder

end BaconThesis.Collective.Sol841

namespace BaconThesis.Collective.Sol841

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective BBPSSW.Distill

section Qubit

variable {n : ℕ}

abbrev St (n : ℕ) := Fin n → Fin 2

lemma sum_agr (i : Fin n) (x : St n) (g : St n → ℂ) :
    ∑ y, (if ∀ k, k ≠ i → x k = y k then g y else 0) = ∑ t, g (Function.update x i t) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun t _ => Function.update x i t)
  · intro t _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro k hk
    rw [Function.update_of_ne hk]
  · intro t _ t' _ h
    have := congrFun h i
    simpa using this
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    refine ⟨y i, Finset.mem_univ _, ?_⟩
    funext k
    by_cases hk : k = i
    · subst hk; simp
    · rw [Function.update_of_ne hk, hy k hk]
  · intro t _; rfl

lemma onQubit_add (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i (A + B) = onQubit i A + onQubit i B := by
  ext x y; simp only [onQubit, Matrix.add_apply]; split_ifs <;> simp

lemma onQubit_smul (i : Fin n) (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i (c • A) = c • onQubit i A := by
  ext x y; simp only [onQubit, Matrix.smul_apply]; split_ifs <;> simp

lemma onQubit_star (i : Fin n) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (onQubit i A)ᴴ = onQubit i Aᴴ := by
  ext x y
  simp only [onQubit, conjTranspose_apply]
  by_cases h : ∀ k, k ≠ i → x k = y k
  · rw [if_pos h, if_pos (fun k hk => (h k hk).symm)]
  · rw [if_neg h, if_neg (fun h' => h (fun k hk => (h' k hk).symm)), star_zero]

lemma onQubit_mul_same (i : Fin n) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i A * onQubit i B = onQubit i (A * B) := by
  ext x z
  rw [Matrix.mul_apply]
  have : ∀ y, onQubit i A x y * onQubit i B y z
      = if ∀ k, k ≠ i → x k = y k then A (x i) (y i) * onQubit i B y z else 0 := by
    intro y; simp only [onQubit]; split_ifs <;> simp
  simp only [this]
  rw [sum_agr]
  simp only [onQubit, Function.update_self, Matrix.mul_apply]
  by_cases h : ∀ k, k ≠ i → x k = z k
  · rw [if_pos h]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [if_pos (fun k hk => by rw [Function.update_of_ne hk]; exact h k hk)]
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun t _ => ?_
    rw [if_neg (fun h' => h (fun k hk => by have := h' k hk; rwa [Function.update_of_ne hk] at this)),
      mul_zero]

lemma onQubit_mul_ne (i j : Fin n) (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) ℂ) (x z : St n) :
    (onQubit i A * onQubit j B) x z
      = if ∀ k, k ≠ i → k ≠ j → x k = z k then A (x i) (z i) * B (x j) (z j) else 0 := by
  rw [Matrix.mul_apply]
  have : ∀ y, onQubit i A x y * onQubit j B y z
      = if ∀ k, k ≠ i → x k = y k then A (x i) (y i) * onQubit j B y z else 0 := by
    intro y; simp only [onQubit]; split_ifs <;> simp
  simp only [this]
  rw [sum_agr]
  simp only [onQubit, Function.update_self, Function.update_of_ne hij.symm]
  rw [Finset.sum_eq_single (z i)]
  · by_cases h : ∀ k, k ≠ i → k ≠ j → x k = z k
    · rw [if_pos h, if_pos]
      intro k hk
      by_cases hki : k = i
      · subst hki; simp
      · rw [Function.update_of_ne hki]; exact h k hki hk
    · rw [if_neg h, if_neg, mul_zero]
      intro h'
      apply h
      intro k hki hkj
      have := h' k hkj
      rwa [Function.update_of_ne hki] at this
  · intro t _ ht
    rw [if_neg, mul_zero]
    intro h'
    have := h' i hij
    rw [Function.update_self] at this
    exact ht this
  · simp

lemma onQubit_comm (i j : Fin n) (hij : i ≠ j) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    onQubit i A * onQubit j B = onQubit j B * onQubit i A := by
  ext x z
  rw [onQubit_mul_ne i j hij, onQubit_mul_ne j i hij.symm]
  by_cases h : ∀ k, k ≠ i → k ≠ j → x k = z k
  · rw [if_pos h, if_pos (fun k h1 h2 => h k h2 h1), mul_comm]
  · rw [if_neg h, if_neg (fun h' => h (fun k h1 h2 => h' k h2 h1))]

variable (n) in
/-- `Σ_i O^(i)`. -/
noncomputable def coll (O : Matrix (Fin 2) (Fin 2) ℂ) : Matrix (St n) (St n) ℂ :=
  ∑ i : Fin n, onQubit i O

lemma coll_add (A B : Matrix (Fin 2) (Fin 2) ℂ) : coll n (A + B) = coll n A + coll n B := by
  simp [coll, onQubit_add, Finset.sum_add_distrib]

lemma coll_smul (c : ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) : coll n (c • A) = c • coll n A := by
  simp [coll, onQubit_smul, Finset.smul_sum]

lemma coll_sub (A B : Matrix (Fin 2) (Fin 2) ℂ) : coll n (A - B) = coll n A - coll n B := by
  rw [sub_eq_add_neg, coll_add, ← neg_one_smul ℂ B, coll_smul]; module

lemma coll_star (A : Matrix (Fin 2) (Fin 2) ℂ) : (coll n A)ᴴ = coll n Aᴴ := by
  simp [coll, conjTranspose_sum, onQubit_star]

lemma coll_comm (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    coll n A * coll n B - coll n B * coll n A = coll n (A * B - B * A) := by
  simp only [coll, Finset.sum_mul_sum]
  rw [Finset.sum_comm (f := fun i j => onQubit i B * onQubit j A), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · rw [onQubit_mul_same, onQubit_mul_same, sub_eq_add_neg (A * B), ← neg_one_smul ℂ (B * A),
      onQubit_add, onQubit_smul, neg_one_smul, ← sub_eq_add_neg]
  · intro j _ hj
    rw [onQubit_comm i j (Ne.symm hj), sub_self]
  · simp

lemma collS_eq (α : Axis) : collS n α = coll n ((1 / 2 : ℂ) • pauli α) := by
  simp [collS, coll, onQubit_smul]

def sp : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 0, 0]
def sm : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 1, 0]
noncomputable def sz : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 0; 0, -1 / 2]

variable (n) in
noncomputable def Sp : Matrix (St n) (St n) ℂ := coll n sp
variable (n) in
noncomputable def Sm : Matrix (St n) (St n) ℂ := coll n sm
variable (n) in
noncomputable def Sz : Matrix (St n) (St n) ℂ := coll n sz

lemma collS_x : collS n .x = (1 / 2 : ℂ) • (Sp n + Sm n) := by
  rw [collS_eq, Sp, Sm, ← coll_add, ← coll_smul]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, sp, sm]

lemma collS_y : collS n .y = (-(Complex.I / 2)) • (Sp n - Sm n) := by
  rw [collS_eq, Sp, Sm, ← coll_sub, ← coll_smul]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, sp, sm] <;> ring

lemma collS_z : collS n .z = Sz n := by
  rw [collS_eq, Sz]
  congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [pauli, sz] <;> norm_num

lemma Sm_star : (Sm n)ᴴ = Sp n := by
  rw [Sm, Sp, coll_star]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [sp, sm]

lemma Sz_star : (Sz n)ᴴ = Sz n := by
  rw [Sz, coll_star]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;> simp [sz]

lemma comm_pm : Sp n * Sm n - Sm n * Sp n = (2 : ℂ) • Sz n := by
  rw [Sp, Sm, Sz, coll_comm, ← coll_smul]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sp, sm, sz, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma comm_zm : Sz n * Sm n - Sm n * Sz n = -Sm n := by
  rw [Sz, Sm, coll_comm, ← neg_one_smul ℂ (coll n sm), ← coll_smul]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sm, sz, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

lemma comm_zp : Sz n * Sp n - Sp n * Sz n = Sp n := by
  rw [Sz, Sp, coll_comm]; congr 1
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sp, sz, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- Hamming weight: the number of qubits in state `1`. -/
def wt (x : St n) : ℕ := (Finset.univ.filter fun i => x i = 1).card

lemma Sz_eq : Sz n = Matrix.diagonal fun x => (n : ℂ) / 2 - wt x := by
  ext x y
  rw [Sz, coll, Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have : ∀ i, onQubit i sz x x = 1 / 2 - (if x i = 1 then 1 else 0) := by
      intro i
      simp only [onQubit, if_pos (fun _ _ => rfl : ∀ k, k ≠ i → x k = x k)]
      rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h | h <;> simp [h, sz] <;> norm_num
    simp only [this, Finset.sum_sub_distrib, Finset.sum_boole, wt]
    simp
    ring
  · rw [if_neg hxy]
    refine Finset.sum_eq_zero fun i _ => ?_
    simp only [onQubit]
    split_ifs with h
    · have hi : x i ≠ y i := fun e => hxy (funext fun k => by
        by_cases hk : k = i
        · subst hk; exact e
        · exact h k hk)
      rcases Fin.exists_fin_two.1 ⟨x i, rfl⟩ with h1 | h1 <;>
        rcases Fin.exists_fin_two.1 ⟨y i, rfl⟩ with h2 | h2 <;>
        simp_all [sz]
    · rfl

lemma card_wt (w : ℕ) : (Finset.univ.filter fun y : St n => wt y = w).card = n.choose w := by
  have hc : n.choose w = (Finset.powersetCard w (Finset.univ : Finset (Fin n))).card := by
    rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rw [hc]
  refine Finset.card_bij' (fun y _ => Finset.univ.filter fun i => y i = 1)
    (fun s _ => fun i => if i ∈ s then 1 else 0) ?_ ?_ ?_ ?_
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, hy⟩
  · intro s hs
    rw [Finset.mem_powersetCard] at hs
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    unfold wt
    have : (Finset.univ.filter fun i => (if i ∈ s then (1 : Fin 2) else 0) = 1) = s := by
      ext i; by_cases h : i ∈ s <;> simp [h]
    rw [this]; exact hs.2
  · intro y _
    funext i
    rcases Fin.exists_fin_two.1 ⟨y i, rfl⟩ with h | h <;> simp [h]
  · intro s _
    ext i; simp

end Qubit

end BaconThesis.Collective.Sol841

namespace BaconThesis.Collective.Sol841

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective BBPSSW.Distill

section Eucl

variable {n : ℕ}

abbrev E (n : ℕ) := EuclideanSpace ℂ (St n)

noncomputable abbrev Lop (A : Matrix (St n) (St n) ℂ) : E n →ₗ[ℂ] E n := Matrix.toEuclideanLin A

lemma Lop_apply (A : Matrix (St n) (St n) ℂ) (v : E n) (x : St n) :
    Lop A v x = ∑ y, A x y * v y := by
  simp [Lop, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct]

lemma Lop_comp (A B : Matrix (St n) (St n) ℂ) (v : E n) : Lop A (Lop B v) = Lop (A * B) v := by
  simp [Lop, Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec]

lemma Lop_adj (A : Matrix (St n) (St n) ℂ) (v w : E n) : ⟪Lop A v, w⟫_ℂ = ⟪v, Lop Aᴴ w⟫_ℂ := by
  rw [Lop, Lop, Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_inner_right]

lemma Lop_sub (A B : Matrix (St n) (St n) ℂ) (v : E n) : Lop (A - B) v = Lop A v - Lop B v := by
  rw [Lop, map_sub]; rfl

lemma Lop_smul (c : ℂ) (A : Matrix (St n) (St n) ℂ) (v : E n) : Lop (c • A) v = c • Lop A v := by
  rw [Lop, map_smul]; rfl

lemma ladder : Ladder (Lop (Sp n)) (Lop (Sm n)) (Lop (Sz n)) where
  adj x y := by rw [Lop_adj, Sm_star]
  zsa x y := by rw [Lop_adj, Sz_star]
  pm x := by rw [Lop_comp, Lop_comp, ← Lop_sub, comm_pm, Lop_smul]
  zm x := by rw [Lop_comp, Lop_comp, ← Lop_sub, comm_zm, ← neg_one_smul ℂ (Sm n), Lop_smul,
    neg_one_smul]
  zp x := by rw [Lop_comp, Lop_comp, ← Lop_sub, comm_zp]

/-- The basis vector `|y⟩`. -/
noncomputable abbrev ket (y : St n) : E n := EuclideanSpace.single y 1

lemma Sz_ket (y : St n) : Lop (Sz n) (ket y) = ((n : ℂ) / 2 - wt y) • ket y := by
  ext x
  rw [Lop_apply, Sz_eq]
  simp [Matrix.diagonal_apply, EuclideanSpace.single_apply]
  by_cases h : x = y
  · subst h; simp
  · simp [h]

/-- Basis strings whose weight-space eigenvalue is `μ`. -/
noncomputable def Tw (n : ℕ) (μ : ℂ) : Finset (St n) :=
  Finset.univ.filter fun y => (n : ℂ) / 2 - wt y = μ

lemma eig_eq (μ : ℂ) : Module.End.eigenspace (Lop (Sz n)) μ
    = Submodule.span ℂ (Set.range fun y : Tw n μ => ket (y : St n)) := by
  apply le_antisymm
  · intro v hv
    rw [Module.End.mem_eigenspace_iff] at hv
    have hc : ∀ y, y ∉ Tw n μ → v y = 0 := by
      intro y hy
      have := congrArg (fun w : E n => w y) hv
      simp only [Lop_apply, Sz_eq, Matrix.diagonal_apply, ite_mul, zero_mul,
        Finset.sum_ite_eq, Finset.mem_univ, if_true, PiLp.smul_apply, smul_eq_mul] at this
      have hne : (n : ℂ) / 2 - wt y ≠ μ := by simpa [Tw] using hy
      have : ((n : ℂ) / 2 - wt y - μ) * v y = 0 := by rw [sub_mul, this, sub_self]
      exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
    have hv' : v = ∑ y, v y • ket y := by
      ext x
      simp [EuclideanSpace.single_apply, Pi.single_apply]
    rw [hv']
    refine Submodule.sum_mem _ fun y _ => ?_
    by_cases hy : y ∈ Tw n μ
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩)
    · rw [hc y hy, zero_smul]; exact Submodule.zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff, Sz_ket]
    congr 1
    simpa [Tw] using hy

lemma finrank_eig (μ : ℂ) :
    finrank ℂ (Module.End.eigenspace (Lop (Sz n)) μ) = (Tw n μ).card := by
  rw [eig_eq, finrank_span_eq_card, Fintype.card_coe]
  have := (EuclideanSpace.basisFun (St n) ℂ).toBasis.linearIndependent.comp
    (Subtype.val : Tw n μ → St n) Subtype.val_injective
  have e : (fun y : Tw n μ => ket (y : St n))
      = ⇑(EuclideanSpace.basisFun (St n) ℂ).toBasis ∘ Subtype.val := by
    funext y; simp
  rw [e]; exact this

lemma Tw_w (w : ℕ) : Tw n ((n : ℂ) / 2 - w) = Finset.univ.filter fun y : St n => wt y = w := by
  ext y
  simp only [Tw, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact_mod_cast (sub_right_injective h)
  · intro h; rw [h]

lemma finrank_eig_w (w : ℕ) :
    finrank ℂ (Module.End.eigenspace (Lop (Sz n)) ((n : ℂ) / 2 - w)) = n.choose w := by
  rw [finrank_eig, Tw_w, card_wt]

lemma eig_top : Module.End.eigenspace (Lop (Sz n)) ((n : ℂ) / 2 + 1) = ⊥ := by
  rw [eig_eq]
  have : Tw n ((n : ℂ) / 2 + 1) = ∅ := by
    ext y
    simp only [Tw, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    intro h
    have : (wt y : ℂ) + 1 = 0 := by linear_combination -h
    exact_mod_cast (Nat.cast_add_one_ne_zero (wt y)) this
  rw [Submodule.span_eq_bot]
  rintro _ ⟨⟨y, hy⟩, rfl⟩
  rw [this] at hy
  exact absurd hy (Finset.notMem_empty y)

lemma ket_mem (y : St n) : ket y ∈ Module.End.eigenspace (Lop (Sz n)) ((n : ℂ) / 2 - wt y) := by
  rw [Module.End.mem_eigenspace_iff, Sz_ket]

end Eucl

end BaconThesis.Collective.Sol841

namespace BaconThesis.Collective.Sol841

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective BBPSSW.Distill

section Build

variable (n : ℕ)

noncomputable def μr (r : ℕ) : ℂ := (n : ℂ) / 2 - r

noncomputable def Kr (r : ℕ) : Submodule ℂ (E n) := Kh (Lop (Sm n)) (Lop (Sz n)) (μr n r)

noncomputable def mult (r : Fin (n / 2 + 1)) : ℕ := finrank ℂ (Kr n r)

noncomputable def hw (r : Fin (n / 2 + 1)) (l : Fin (mult n r)) : E n :=
  ((stdOrthonormalBasis ℂ (Kr n r)) l : E n)

def Fr (d k : ℕ) : ℝ := ∏ j ∈ Finset.range k, (((j : ℝ) + 1) * ((d : ℝ) - j))

noncomputable def cf (d k : ℕ) : ℂ := (((Real.sqrt (Fr d k))⁻¹ : ℝ) : ℂ)

/-- The basis vector `|J, λ, m⟩` with `J = n/2 - r`, `m = J - k`. -/
noncomputable def ev (a : BlockIdx n (mult n)) : E n :=
  cf (n - 2 * a.1.val) a.2.2 • (Lop (Sm n) ^ (a.2.2 : ℕ)) (hw n a.1 a.2.1)

variable {n}

lemma two_r_le (r : Fin (n / 2 + 1)) : 2 * r.val ≤ n := by have := r.isLt; omega

lemma F_eq (d k : ℕ) : F d k = (Fr d k : ℂ) := by
  simp [F, Fr]

lemma Fr_pos {d k : ℕ} (hk : k ≤ d) : 0 < Fr d k := by
  apply Finset.prod_pos
  intro j hj
  rw [Finset.mem_range] at hj
  have : (j : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le hj hk)
  positivity

lemma Fr_succ (d k : ℕ) : Fr d (k + 1) = Fr d k * (((k : ℝ) + 1) * ((d : ℝ) - k)) := by
  rw [Fr, Finset.prod_range_succ]; rfl

lemma cf_star (d k : ℕ) : star (cf d k) = cf d k := by simp [cf]

lemma cf_zero (d : ℕ) : cf d 0 = 1 := by simp [cf, Fr]

lemma cf_sq {d k : ℕ} (hk : k ≤ d) : cf d k * cf d k * F d k = 1 := by
  rw [cf, F_eq, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  have hp := Fr_pos hk
  have : (Real.sqrt (Fr d k))⁻¹ * (Real.sqrt (Fr d k))⁻¹ * Fr d k = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hp.le, inv_mul_cancel₀ hp.ne']
  rw [this, Complex.ofReal_one]

lemma μr_eq (r : Fin (n / 2 + 1)) : μr n r = (((n - 2 * r.val : ℕ) : ℂ) / 2) := by
  rw [μr, Nat.cast_sub (two_r_le r)]; push_cast; ring

lemma hw_mem (r : Fin (n / 2 + 1)) (l : Fin (mult n r)) : hw n r l ∈ Kr n r :=
  ((stdOrthonormalBasis ℂ (Kr n r)) l).2

lemma hw_P (r : Fin (n / 2 + 1)) (l : Fin (mult n r)) : Lop (Sp n) (hw n r l) = 0 :=
  ladder.Kh_P (hw_mem r l)

lemma hw_Z (r : Fin (n / 2 + 1)) (l : Fin (mult n r)) :
    Lop (Sz n) (hw n r l) = (((n - 2 * r.val : ℕ) : ℂ) / 2) • hw n r l := by
  rw [← μr_eq]; exact ladder.Kh_eig (hw_mem r l)

lemma hw_inner_same (r : Fin (n / 2 + 1)) (l l' : Fin (mult n r)) :
    ⟪hw n r l, hw n r l'⟫_ℂ = if l = l' then 1 else 0 := by
  have := orthonormal_iff_ite.1 (stdOrthonormalBasis ℂ (Kr n r)).orthonormal l l'
  rw [Submodule.coe_inner] at this
  exact this

lemma hw_inner_ne {r r' : Fin (n / 2 + 1)} (hr : r ≠ r') (l : Fin (mult n r))
    (l' : Fin (mult n r')) : ⟪hw n r l, hw n r' l'⟫_ℂ = 0 := by
  have h1 := (ladder (n := n)).zsa (hw n r l) (hw n r' l')
  rw [ladder.Kh_eig (hw_mem r l), ladder.Kh_eig (hw_mem r' l'), inner_smul_left,
    inner_smul_right] at h1
  have hc : (starRingEnd ℂ) (μr n r) = μr n r := by
    simp only [μr, map_sub, map_div₀, map_natCast, map_ofNat]
  rw [hc] at h1
  have hne : μr n r - μr n r' ≠ 0 := by
    rw [μr, μr, sub_sub_sub_cancel_left, sub_ne_zero]
    intro e
    exact hr (Fin.ext (by exact_mod_cast e.symm))
  have : (μr n r - μr n r') * ⟪hw n r l, hw n r' l'⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
  exact (mul_eq_zero.1 this).resolve_left hne

lemma pow_inner (r r' : Fin (n / 2 + 1)) (l : Fin (mult n r)) (l' : Fin (mult n r')) (k k' : ℕ) :
    ⟪(Lop (Sm n) ^ k) (hw n r l), (Lop (Sm n) ^ k') (hw n r' l')⟫_ℂ
      = if k = k' then F (n - 2 * r.val) k * ⟪hw n r l, hw n r' l'⟫_ℂ else 0 :=
  ladder.inner_pow (hw_P r l) (hw_Z r l) (hw_P r' l') k' k

lemma ev_inner (a b : BlockIdx n (mult n)) :
    ⟪ev n a, ev n b⟫_ℂ = cf (n - 2 * a.1.val) a.2.2 * cf (n - 2 * b.1.val) b.2.2 *
      (if (a.2.2 : ℕ) = b.2.2 then F (n - 2 * a.1.val) a.2.2 * ⟪hw n a.1 a.2.1, hw n b.1 b.2.1⟫_ℂ
        else 0) := by
  rw [ev, ev, inner_smul_left, inner_smul_right, pow_inner]
  have : (starRingEnd ℂ) (cf (n - 2 * a.1.val) a.2.2) = cf (n - 2 * a.1.val) a.2.2 :=
    cf_star _ _
  rw [this, mul_assoc]

lemma ev_orth : Orthonormal ℂ (ev n) := by
  rw [orthonormal_iff_ite]
  rintro ⟨r, l, k⟩ ⟨r', l', k'⟩
  rw [ev_inner]
  dsimp only
  by_cases hr : r = r'
  · subst hr
    rw [hw_inner_same]
    by_cases hl : l = l'
    · subst hl
      by_cases hk : k = k'
      · subst hk
        rw [if_pos rfl, if_pos rfl, if_pos rfl, mul_one]
        exact cf_sq (Nat.lt_succ_iff.1 k.isLt)
      · rw [if_neg (fun e => hk (Fin.ext e)), mul_zero, if_neg]
        intro e; exact hk (Prod.ext_iff.1 (eq_of_heq (Sigma.mk.inj_iff.1 e).2)).2
    · rw [if_neg hl]
      simp only [mul_zero, ite_self]
      rw [if_neg]
      intro e; exact hl (Prod.ext_iff.1 (eq_of_heq (Sigma.mk.inj_iff.1 e).2)).1
  · rw [hw_inner_ne hr]
    simp only [mul_zero, ite_self]
    rw [if_neg]
    intro e; exact hr (Sigma.mk.inj_iff.1 e).1

lemma ev_zero (r : Fin (n / 2 + 1)) (l : Fin (mult n r)) : ev n ⟨r, (l, 0)⟩ = hw n r l := by
  simp [ev, cf_zero]

lemma M_ev (r : Fin (n / 2 + 1)) (l : Fin (mult n r)) (k : Fin (n - 2 * r.val + 1)) :
    Lop (Sm n) (ev n ⟨r, (l, k)⟩) ∈ Submodule.span ℂ (Set.range (ev n)) := by
  simp only [ev]
  rw [map_smul, ← Module.End.mul_apply, ← pow_succ']
  by_cases hk : (k : ℕ) + 1 ≤ n - 2 * r.val
  · let k1 : Fin (n - 2 * r.val + 1) := ⟨k + 1, by omega⟩
    have hcf : cf (n - 2 * r.val) (k + 1) ≠ 0 := by
      simp only [cf, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
      exact (Real.sqrt_pos.2 (Fr_pos hk)).ne'
    have : cf (n - 2 * r.val) k • (Lop (Sm n) ^ ((k : ℕ) + 1)) (hw n r l)
        = (cf (n - 2 * r.val) k * (cf (n - 2 * r.val) (k + 1))⁻¹) • ev n ⟨r, (l, k1)⟩ := by
      simp only [ev, k1, smul_smul]
      rw [mul_assoc, inv_mul_cancel₀ hcf, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · have hk' : (k : ℕ) = n - 2 * r.val := by have := k.isLt; omega
    rw [hk', ladder.M_top (hw_P r l) (hw_Z r l), smul_zero]
    exact Submodule.zero_mem _

lemma span_M (x : E n) (hx : x ∈ Submodule.span ℂ (Set.range (ev n))) :
    Lop (Sm n) x ∈ Submodule.span ℂ (Set.range (ev n)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨r, l, k⟩, rfl⟩ := hy
    exact M_ev r l k
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

lemma Kr_le (r : Fin (n / 2 + 1)) : Kr n r ≤ Submodule.span ℂ (Set.range (ev n)) := by
  intro x hx
  have h := (stdOrthonormalBasis ℂ (Kr n r)).sum_repr ⟨x, hx⟩
  rw [show x = ((⟨x, hx⟩ : Kr n r) : E n) from rfl, ← h, Submodule.coe_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [Submodule.coe_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨r, (l, 0)⟩, ev_zero r l⟩)

lemma eig_le (w : ℕ) : Module.End.eigenspace (Lop (Sz n)) ((n : ℂ) / 2 - w)
    ≤ Submodule.span ℂ (Set.range (ev n)) := by
  induction w with
  | zero =>
    apply ladder.span_step span_M
    · rw [Nat.cast_zero, sub_zero, eig_top]; exact bot_le
    · have := Kr_le (n := n) 0
      simpa [Kr, μr] using this
  | succ w ih =>
    apply ladder.span_step span_M
    · have e : (n : ℂ) / 2 - ((w + 1 : ℕ) : ℂ) + 1 = (n : ℂ) / 2 - w := by push_cast; ring
      rw [e]; exact ih
    · by_cases hw : 2 * (w + 1) ≤ n
      · have := Kr_le (n := n) ⟨w + 1, by omega⟩
        simpa [Kr, μr] using this
      · intro x hx
        have hneg : ((n : ℝ) / 2 - ((w + 1 : ℕ) : ℝ)) < 0 := by
          have : (n : ℝ) < 2 * ((w + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : n < 2 * (w + 1))
          linarith
        rw [ladder.Kh_neg hneg (by push_cast; ring) hx]
        exact Submodule.zero_mem _

lemma ev_span : ⊤ ≤ Submodule.span ℂ (Set.range (ev n)) := by
  intro v _
  have hv : v = ∑ y, v y • ket y := by
    ext x
    simp [EuclideanSpace.single_apply, Pi.single_apply]
  rw [hv]
  exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (eig_le (wt y) (ket_mem y))

lemma card_idx : Fintype.card (BlockIdx n (mult n)) = Fintype.card (St n) := by
  have b := OrthonormalBasis.mk (ev_orth (n := n)) ev_span
  rw [← finrank_eq_card_basis b.toBasis, finrank_euclideanSpace]

lemma mult_add (r : Fin (n / 2 + 1)) :
    mult n r + (if r.val = 0 then 0 else n.choose (r.val - 1)) = n.choose r.val := by
  have hν : (0 : ℝ) < (n : ℝ) / 2 - r.val + 1 := by
    have : (2 * r.val : ℝ) ≤ n := by exact_mod_cast two_r_le r
    linarith
  have h := (ladder (n := n)).finrank_Kh hν (μ := μr n r) (by simp [μr])
  rw [μr, finrank_eig_w] at h
  rw [mult, Kr, μr, ← h]
  congr 1
  by_cases h0 : r.val = 0
  · rw [if_pos h0, h0, Nat.cast_zero, sub_zero, eig_top]; simp
  · rw [if_neg h0, ← finrank_eig_w]
    have e : (n : ℂ) / 2 - ((r.val - 1 : ℕ) : ℂ) = (n : ℂ) / 2 - r.val + 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 h0)]; push_cast; ring
    rw [e]

lemma degeneracy_eq (r : Fin (n / 2 + 1)) :
    degeneracy n r.val = (n.choose r.val : ℚ) - (if r.val = 0 then 0 else n.choose (r.val - 1)) := by
  have h2 := two_r_le r
  by_cases h0 : r.val = 0
  · rw [if_pos h0, h0, degeneracy]
    simp [Nat.factorial_succ]
    field_simp
    exact ⟨by positivity, Nat.factorial_ne_zero n⟩
  · obtain ⟨s, hs⟩ : ∃ s, r.val = s + 1 := ⟨r.val - 1, by omega⟩
    rw [if_neg h0, hs, Nat.add_sub_cancel]
    rw [hs] at h2
    obtain ⟨a, ha⟩ : ∃ a, a = n - (s + 1) := ⟨_, rfl⟩
    have e1 : n - 2 * (s + 1) + 1 = a - s := by omega
    have e2 : n - (s + 1) + 1 = a + 1 := by omega
    have e3 : n - s = a + 1 := by omega
    have hA := Nat.choose_mul_factorial_mul_factorial (n := n) (k := s + 1) (by omega)
    rw [← ha, Nat.factorial_succ s] at hA
    have hB := Nat.choose_mul_factorial_mul_factorial (n := n) (k := s) (by omega)
    rw [e3, Nat.factorial_succ a] at hB
    have hAq : (n.choose (s + 1) : ℚ) * (((s : ℚ) + 1) * s.factorial) * a.factorial
        = n.factorial := by exact_mod_cast hA
    have hBq : (n.choose s : ℚ) * s.factorial * (((a : ℚ) + 1) * a.factorial)
        = n.factorial := by exact_mod_cast hB
    have hc : ((a - s : ℕ) : ℚ) = a - s := Nat.cast_sub (by omega)
    rw [degeneracy, e1, e2, Nat.factorial_succ a, Nat.factorial_succ s]
    rw [div_eq_iff (by positivity)]
    push_cast [hc]
    linear_combination (-((a : ℚ) + 1)) * hAq + ((s : ℚ) + 1) * hBq

lemma mult_eq (r : Fin (n / 2 + 1)) : (mult n r : ℚ) = degeneracy n r.val := by
  rw [degeneracy_eq, ← mult_add r]
  push_cast
  ring

end Build

end BaconThesis.Collective.Sol841

namespace BaconThesis.Collective.Sol841

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective BBPSSW.Distill

section Rep

variable (n : ℕ)

noncomputable def W : Matrix (BlockIdx n (mult n)) (St n) ℂ := fun a x => star (ev n a x)

variable {n}

lemma W_mul_star : W n * (W n)ᴴ = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply, ← orthonormal_iff_ite.1 ev_orth a b, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp [W, conjTranspose_apply, mul_comm]

lemma star_mul_W : (W n)ᴴ * W n = 1 := by
  have e : BlockIdx n (mult n) ≃ St n := Fintype.equivOfCardEq card_idx
  exact (Matrix.mul_eq_one_comm_of_equiv e).1 W_mul_star

lemma conj_apply (A : Matrix (St n) (St n) ℂ) (a b : BlockIdx n (mult n)) :
    (W n * A * (W n)ᴴ) a b = ⟪ev n a, Lop A (ev n b)⟫_ℂ := by
  rw [PiLp.inner_apply]
  simp only [Matrix.mul_apply, W, conjTranspose_apply, star_star, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [RCLike.inner_apply, show (Lop A (ev n b)).ofLp x = Lop A (ev n b) x from rfl, Lop_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [starRingEnd_apply]
  ring

lemma cf_conj (d k : ℕ) : (starRingEnd ℂ) (cf d k) = cf d k := cf_star d k

lemma coef (d k : ℕ) (hk : k + 1 ≤ d) :
    cf d (k + 1) * cf d k * F d (k + 1)
      = ((Real.sqrt (((k + 1 : ℕ) : ℝ) * ((d : ℝ) - ((k + 1 : ℕ) : ℝ) + 1)) : ℝ) : ℂ) := by
  rw [cf, cf, F_eq, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  have ha := Fr_pos (d := d) (k := k) (by omega)
  have hq : 0 < ((k : ℝ) + 1) * ((d : ℝ) - k) := by
    have : (k : ℝ) + 1 ≤ d := by exact_mod_cast hk
    nlinarith
  rw [Fr_succ]
  have e : ((k + 1 : ℕ) : ℝ) * ((d : ℝ) - ((k + 1 : ℕ) : ℝ) + 1) = ((k : ℝ) + 1) * ((d : ℝ) - k) := by
    push_cast; ring
  rw [e, Real.sqrt_mul ha.le]
  have hsa := Real.sqrt_pos.2 ha
  have hsq := Real.sqrt_pos.2 hq
  have h1 := Real.mul_self_sqrt ha.le
  have h2 := Real.mul_self_sqrt hq.le
  field_simp
  nlinarith [h1, h2]

lemma Sm_ev (a b : BlockIdx n (mult n)) :
    ⟪ev n a, Lop (Sm n) (ev n b)⟫_ℂ = cf (n - 2 * a.1.val) a.2.2 * cf (n - 2 * b.1.val) b.2.2 *
      (if (a.2.2 : ℕ) = b.2.2 + 1 then F (n - 2 * a.1.val) a.2.2 * ⟪hw n a.1 a.2.1, hw n b.1 b.2.1⟫_ℂ
        else 0) := by
  rw [ev, ev, map_smul, ← Module.End.mul_apply, ← pow_succ', inner_smul_left, inner_smul_right,
    pow_inner, cf_conj, mul_assoc]

lemma Sp_ev (a b : BlockIdx n (mult n)) :
    ⟪ev n a, Lop (Sp n) (ev n b)⟫_ℂ = cf (n - 2 * a.1.val) a.2.2 * cf (n - 2 * b.1.val) b.2.2 *
      (if (a.2.2 : ℕ) + 1 = b.2.2 then F (n - 2 * a.1.val) (a.2.2 + 1) *
        ⟪hw n a.1 a.2.1, hw n b.1 b.2.1⟫_ℂ else 0) := by
  rw [← ladder.adj, ev, ev, map_smul, ← Module.End.mul_apply, ← pow_succ', inner_smul_left,
    inner_smul_right, pow_inner, cf_conj, mul_assoc]

lemma Sz_ev (a b : BlockIdx n (mult n)) :
    ⟪ev n a, Lop (Sz n) (ev n b)⟫_ℂ
      = ((((n - 2 * b.1.val : ℕ) : ℂ) / 2 - (b.2.2 : ℕ)) * ⟪ev n a, ev n b⟫_ℂ) := by
  have hb : Lop (Sz n) (ev n b)
      = ((((n - 2 * b.1.val : ℕ) : ℂ) / 2 - (b.2.2 : ℕ))) • ev n b := by
    simp only [ev]
    rw [map_smul, ladder.z_pow (hw_Z b.1 b.2.1), smul_comm]
  rw [hb, inner_smul_right]

lemma Sm_same (r : Fin (n / 2 + 1)) (l l' : Fin (mult n r)) (k k' : Fin (n - 2 * r.val + 1)) :
    ⟪ev n ⟨r, (l, k)⟩, Lop (Sm n) (ev n ⟨r, (l', k')⟩)⟫_ℂ
      = if l = l' then (if (k' : ℕ) + 1 = k then
          ((Real.sqrt ((k : ℝ) * (((n - 2 * r.val : ℕ) : ℝ) - k + 1)) : ℝ) : ℂ) else 0) else 0 := by
  rw [Sm_ev]
  dsimp only
  rw [hw_inner_same]
  by_cases hl : l = l'
  · subst hl
    simp only [eq_self_iff_true, if_true, mul_one]
    by_cases hk : (k' : ℕ) + 1 = k
    · rw [if_pos hk.symm, if_pos hk]
      have hk2 : (k' : ℕ) + 1 ≤ n - 2 * r.val := by have := k.isLt; omega
      rw [← hk, coef _ _ hk2]
    · rw [if_neg (fun e => hk e.symm), if_neg hk, mul_zero]
  · simp [hl]

lemma Sp_same (r : Fin (n / 2 + 1)) (l l' : Fin (mult n r)) (k k' : Fin (n - 2 * r.val + 1)) :
    ⟪ev n ⟨r, (l, k)⟩, Lop (Sp n) (ev n ⟨r, (l', k')⟩)⟫_ℂ
      = if l = l' then (if (k : ℕ) + 1 = k' then
          ((Real.sqrt ((k' : ℝ) * (((n - 2 * r.val : ℕ) : ℝ) - k' + 1)) : ℝ) : ℂ) else 0) else 0 := by
  rw [Sp_ev]
  dsimp only
  rw [hw_inner_same]
  by_cases hl : l = l'
  · subst hl
    simp only [eq_self_iff_true, if_true, mul_one]
    by_cases hk : (k : ℕ) + 1 = k'
    · rw [if_pos hk, if_pos hk]
      have hk2 : (k : ℕ) + 1 ≤ n - 2 * r.val := by have := k'.isLt; omega
      rw [← hk, mul_comm (cf _ k) (cf _ (k + 1)), coef _ _ hk2]
    · rw [if_neg hk, if_neg hk, mul_zero]
  · simp [hl]

lemma Sz_same (r : Fin (n / 2 + 1)) (l l' : Fin (mult n r)) (k k' : Fin (n - 2 * r.val + 1)) :
    ⟪ev n ⟨r, (l, k)⟩, Lop (Sz n) (ev n ⟨r, (l', k')⟩)⟫_ℂ
      = if l = l' then (if k = k' then ((((n - 2 * r.val : ℕ) : ℂ) / 2 - (k : ℕ))) else 0)
        else 0 := by
  rw [Sz_ev, orthonormal_iff_ite.1 ev_orth]
  dsimp only
  by_cases hl : l = l'
  · subst hl
    by_cases hk : k = k'
    · subst hk; simp
    · rw [if_neg, if_pos rfl, if_neg hk, mul_zero]
      intro e; exact hk (Prod.ext_iff.1 (eq_of_heq (Sigma.mk.inj_iff.1 e).2)).2
  · rw [if_neg, if_neg hl, mul_zero]
    intro e; exact hl (Prod.ext_iff.1 (eq_of_heq (Sigma.mk.inj_iff.1 e).2)).1

lemma ne_zero_of (A : Matrix (St n) (St n) ℂ) (hA : A = Sp n ∨ A = Sm n ∨ A = Sz n)
    (a b : BlockIdx n (mult n)) (h : a.1 ≠ b.1) : ⟪ev n a, Lop A (ev n b)⟫_ℂ = 0 := by
  rcases hA with rfl | rfl | rfl
  · rw [Sp_ev, hw_inner_ne h]; simp
  · rw [Sm_ev, hw_inner_ne h]; simp
  · rw [Sz_ev, orthonormal_iff_ite.1 ev_orth, if_neg (fun e => h (congrArg Sigma.fst e)),
      mul_zero]

end Rep

end BaconThesis.Collective.Sol841

namespace BaconThesis.Collective.Sol841

open BaconThesis.Collective BBPSSW.Distill Matrix

section Alg

/-- The raising matrix of `spinRep d`. -/
noncomputable def spP (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  Matrix.of fun j k =>
    if j.val + 1 = k.val then ((Real.sqrt ((k.val : ℝ) * ((d : ℝ) - k.val + 1)) : ℝ) : ℂ) else 0

lemma spinRep_x (d : ℕ) : spinRep d .x = (1 / 2 : ℂ) • (spP d + (spP d)ᴴ) := rfl

lemma spinRep_y (d : ℕ) : spinRep d .y = (-(Complex.I / 2)) • (spP d - (spP d)ᴴ) := rfl

lemma spinRep_z (d : ℕ) :
    spinRep d .z = Matrix.diagonal fun k => ((d : ℂ) / 2 - (k.val : ℂ)) := rfl

lemma spP_eq (d : ℕ) : spP d = spinRep d .x + Complex.I • spinRep d .y := by
  rw [spinRep_x, spinRep_y, smul_smul]
  have : Complex.I * -(Complex.I / 2) = (1 / 2 : ℂ) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [this]; module

lemma spPt_eq (d : ℕ) : (spP d)ᴴ = spinRep d .x - Complex.I • spinRep d .y := by
  rw [spinRep_x, spinRep_y, smul_smul]
  have : Complex.I * -(Complex.I / 2) = (1 / 2 : ℂ) := by
    ring_nf; rw [Complex.I_sq]; ring
  rw [this]; module

lemma spP_ne {d : ℕ} (j k : Fin (d + 1)) (h : j.val + 1 = k.val) : spP d j k ≠ 0 := by
  simp only [spP, Matrix.of_apply, if_pos h, ne_eq, Complex.ofReal_eq_zero]
  have hk := k.isLt
  have h1 : (0 : ℝ) < (k.val : ℝ) * ((d : ℝ) - k.val + 1) := by
    have : (k.val : ℝ) ≤ d := by exact_mod_cast (by omega : k.val ≤ d)
    have : (1 : ℝ) ≤ k.val := by exact_mod_cast (by omega : 1 ≤ k.val)
    nlinarith
  exact (Real.sqrt_pos.2 h1).ne'

lemma spP_real {d : ℕ} (j k : Fin (d + 1)) : star (spP d j k) = spP d j k := by
  simp only [spP, Matrix.of_apply]
  split_ifs <;> simp

lemma single_in {d : ℕ} {S : Subalgebra ℂ (Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)}
    (A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (hA : A ∈ S) (j k : Fin (d + 1))
    (hj : Matrix.single j j (1 : ℂ) ∈ S) (hk : Matrix.single k k (1 : ℂ) ∈ S) (hne : A j k ≠ 0) :
    Matrix.single j k (1 : ℂ) ∈ S := by
  have := S.mul_mem (S.mul_mem hj hA) hk
  rw [single_mul_mul_single, one_mul, mul_one] at this
  have e : Matrix.single j k (1 : ℂ) = (A j k)⁻¹ • Matrix.single j k (A j k) := by
    rw [Matrix.smul_single, smul_eq_mul, inv_mul_cancel₀ hne]
  rw [e]; exact S.smul_mem this _

theorem adjoin_spinRep (d : ℕ) : Algebra.adjoin ℂ (Set.range (spinRep d)) = ⊤ := by
  set S := Algebra.adjoin ℂ (Set.range (spinRep d)) with hS
  have hgen : ∀ α, spinRep d α ∈ S := fun α => Algebra.subset_adjoin ⟨α, rfl⟩
  have hP : spP d ∈ S := by
    rw [spP_eq]; exact S.add_mem (hgen _) (S.smul_mem (hgen _) _)
  have hPt : (spP d)ᴴ ∈ S := by
    rw [spPt_eq]; exact S.sub_mem (hgen _) (S.smul_mem (hgen _) _)
  -- diagonal projectors
  have hdiag : ∀ k : Fin (d + 1), Matrix.single k k (1 : ℂ) ∈ S := by
    intro k
    have hmem : Matrix.diagonal (fun j => ∏ l ∈ Finset.univ.erase k, ((l.val : ℂ) - j.val)) ∈ S := by
      have hfac : ∀ l : Fin (d + 1),
          Matrix.diagonal (fun j : Fin (d + 1) => (l.val : ℂ) - j.val) ∈ S := by
        intro l
        have e : Matrix.diagonal (fun j : Fin (d + 1) => (l.val : ℂ) - j.val)
            = spinRep d .z - algebraMap ℂ _ ((d : ℂ) / 2 - (l.val : ℂ)) := by
          rw [spinRep_z, Matrix.algebraMap_eq_diagonal]
          ext a b
          simp only [Matrix.sub_apply, Matrix.diagonal_apply, Pi.algebraMap_apply,
            Algebra.algebraMap_self, RingHom.id_apply]
          split_ifs
          · ring
          · simp
        rw [e]; exact S.sub_mem (hgen _) (S.algebraMap_mem _)
      have e : (fun j : Fin (d + 1) => ∏ l ∈ Finset.univ.erase k, ((l.val : ℂ) - j.val))
          = ∏ l ∈ Finset.univ.erase k, (fun j : Fin (d + 1) => (l.val : ℂ) - j.val) := by
        funext j; rw [Finset.prod_apply]
      rw [e]
      refine Finset.prod_induction _ (fun g => Matrix.diagonal g ∈ S) ?_ ?_ ?_
      · intro a b ha hb
        rw [show a * b = fun j => a j * b j from rfl, ← Matrix.diagonal_mul_diagonal]
        exact S.mul_mem ha hb
      · rw [show (1 : Fin (d + 1) → ℂ) = fun _ => 1 from rfl, Matrix.diagonal_one]
        exact S.one_mem
      · intro l _; exact hfac l
    have hD : ∏ l ∈ Finset.univ.erase k, ((l.val : ℂ) - k.val) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro l hl
      rw [sub_ne_zero]
      intro e
      exact (Finset.mem_erase.1 hl).1 (Fin.ext (by exact_mod_cast e))
    have e2 : Matrix.diagonal (fun j => ∏ l ∈ Finset.univ.erase k, ((l.val : ℂ) - j.val))
        = (∏ l ∈ Finset.univ.erase k, ((l.val : ℂ) - k.val)) • Matrix.single k k (1 : ℂ) := by
      ext i j
      rw [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.single_apply]
      by_cases hij : i = j
      · subst hij
        by_cases hik : i = k
        · subst hik; simp
        · rw [if_pos rfl, if_neg (fun h => hik h.1.symm), smul_zero]
          exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hik, Finset.mem_univ _⟩) (sub_self _)
      · rw [if_neg hij, if_neg (fun h => hij (h.1.symm.trans h.2)), smul_zero]
    rw [e2] at hmem
    have := S.smul_mem hmem (∏ l ∈ Finset.univ.erase k, ((l.val : ℂ) - k.val))⁻¹
    rwa [smul_smul, inv_mul_cancel₀ hD, one_smul] at this
  -- chain
  have hchain : ∀ l : Fin (d + 1),
      Matrix.single 0 l (1 : ℂ) ∈ S ∧ Matrix.single l 0 (1 : ℂ) ∈ S := by
    intro l
    induction l using Fin.induction with
    | zero => exact ⟨hdiag 0, hdiag 0⟩
    | succ i ih =>
      have hv : (Fin.castSucc i).val + 1 = (Fin.succ i).val := by simp
      have hup := single_in (spP d) hP _ _ (hdiag i.castSucc) (hdiag i.succ) (spP_ne _ _ hv)
      have hdn := single_in (spP d)ᴴ hPt i.succ i.castSucc (hdiag i.succ) (hdiag i.castSucc)
        (by rw [conjTranspose_apply, spP_real]; exact spP_ne _ _ hv)
      refine ⟨?_, ?_⟩
      · have := S.mul_mem ih.1 hup
        rwa [single_mul_single_same, one_mul] at this
      · have := S.mul_mem hdn ih.2
        rwa [single_mul_single_same, one_mul] at this
  have hall : ∀ k l : Fin (d + 1), Matrix.single k l (1 : ℂ) ∈ S := by
    intro k l
    have := S.mul_mem (hchain k).2 (hchain l).1
    rwa [single_mul_single_same, one_mul] at this
  rw [eq_top_iff]
  intro Y _
  rw [Matrix.matrix_eq_sum_single Y]
  refine Subalgebra.sum_mem _ fun k _ => Subalgebra.sum_mem _ fun l _ => ?_
  have e : Matrix.single k l (Y k l) = Y k l • Matrix.single k l (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]; exact S.smul_mem (hall k l) _

lemma spP_spPt (d : ℕ) :
    spP d * (spP d)ᴴ = Matrix.diagonal fun i => ((i.val : ℂ) + 1) * ((d : ℂ) - i.val) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [conjTranspose_apply, spP_real]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : i.val + 1 ≤ d
    · let k0 : Fin (d + 1) := ⟨i.val + 1, by omega⟩
      have hk0 : k0.val = i.val + 1 := rfl
      rw [Finset.sum_eq_single k0]
      · simp only [spP, Matrix.of_apply]
        rw [if_pos hk0.symm, ← Complex.ofReal_mul, Real.mul_self_sqrt]
        · rw [hk0]; push_cast; ring
        · have : (i.val : ℝ) + 1 ≤ d := by exact_mod_cast hi
          rw [hk0]; push_cast; nlinarith
      · intro k _ hk
        simp only [spP, Matrix.of_apply]
        rw [if_neg (fun h => hk (Fin.ext (by omega))), zero_mul]
      · simp
    · have hid : i.val = d := by have := i.isLt; omega
      rw [Finset.sum_eq_zero]
      · rw [hid]; ring
      · intro k _
        simp only [spP, Matrix.of_apply]
        rw [if_neg (fun h => by have := k.isLt; omega), zero_mul]
  · rw [Matrix.diagonal_apply_ne _ hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [spP, Matrix.of_apply]
    by_cases h1 : i.val + 1 = k.val
    · rw [if_neg (show ¬ (j.val + 1 = k.val) from fun h2 => hij (Fin.ext (by omega))), mul_zero]
    · rw [if_neg h1, zero_mul]

lemma spPt_spP (d : ℕ) :
    (spP d)ᴴ * spP d = Matrix.diagonal fun i => (i.val : ℂ) * ((d : ℂ) - i.val + 1) := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [conjTranspose_apply, spP_real]
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    by_cases hi : 1 ≤ i.val
    · let k0 : Fin (d + 1) := ⟨i.val - 1, by omega⟩
      have hk0 : k0.val = i.val - 1 := rfl
      rw [Finset.sum_eq_single k0]
      · simp only [spP, Matrix.of_apply]
        rw [if_pos (by omega), ← Complex.ofReal_mul, Real.mul_self_sqrt]
        · push_cast; ring
        · have : (i.val : ℝ) ≤ d := by exact_mod_cast (by have := i.isLt; omega : i.val ≤ d)
          have : (0 : ℝ) ≤ i.val := by positivity
          nlinarith
      · intro k _ hk
        simp only [spP, Matrix.of_apply]
        rw [if_neg (fun h => hk (Fin.ext (by omega))), zero_mul]
      · simp
    · have hid : i.val = 0 := by omega
      rw [Finset.sum_eq_zero]
      · rw [hid]; simp
      · intro k _
        simp only [spP, Matrix.of_apply]
        rw [if_neg (fun h => by omega), zero_mul]
  · rw [Matrix.diagonal_apply_ne _ hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [spP, Matrix.of_apply]
    by_cases h1 : k.val + 1 = i.val
    · rw [if_neg (show ¬ (k.val + 1 = j.val) from fun h2 => hij (Fin.ext (by omega))), mul_zero]
    · rw [if_neg h1, zero_mul]

lemma casimir (d : ℕ) :
    spinRep d .x * spinRep d .x + spinRep d .y * spinRep d .y + spinRep d .z * spinRep d .z
      = algebraMap ℂ _ (((d * (d + 2) : ℕ) : ℂ) / 4) := by
  have hxy : spinRep d .x * spinRep d .x + spinRep d .y * spinRep d .y
      = (1 / 2 : ℂ) • (spP d * (spP d)ᴴ + (spP d)ᴴ * spP d) := by
    rw [spinRep_x, spinRep_y, smul_mul_smul_comm, smul_mul_smul_comm]
    have : -(Complex.I / 2) * -(Complex.I / 2) = -(1 / 4 : ℂ) := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [this]
    simp only [add_mul, mul_add, sub_mul, mul_sub]
    module
  rw [hxy, spP_spPt, spPt_spP, spinRep_z, Matrix.diagonal_mul_diagonal,
    Matrix.algebraMap_eq_diagonal]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_apply, Pi.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul]
  split_ifs
  · push_cast; ring
  · simp

/-- The product algebra `∏_r M_{d_r + 1}`, `d_r = n - 2r`. -/
abbrev PA (n : ℕ) := (r : Fin (n / 2 + 1)) → Matrix (Fin (n - 2 * r.val + 1)) (Fin (n - 2 * r.val + 1)) ℂ

lemma cas_inj (n : ℕ) (r r' : Fin (n / 2 + 1))
    (h : (((n - 2 * r.val) * (n - 2 * r.val + 2) : ℕ) : ℂ) / 4
      = (((n - 2 * r'.val) * (n - 2 * r'.val + 2) : ℕ) : ℂ) / 4) : r = r' := by
  have h1 : (n - 2 * r.val) * (n - 2 * r.val + 2) = (n - 2 * r'.val) * (n - 2 * r'.val + 2) := by
    have : (((n - 2 * r.val) * (n - 2 * r.val + 2) : ℕ) : ℂ)
        = (((n - 2 * r'.val) * (n - 2 * r'.val + 2) : ℕ) : ℂ) := by
      linear_combination 4 * h
    exact_mod_cast this
  have h2 : n - 2 * r.val = n - 2 * r'.val := by
    rcases lt_trichotomy (n - 2 * r.val) (n - 2 * r'.val) with hl | hl | hl
    · exfalso
      have := Nat.mul_lt_mul'' hl (Nat.add_lt_add_right hl 2)
      omega
    · exact hl
    · exfalso
      have := Nat.mul_lt_mul'' hl (Nat.add_lt_add_right hl 2)
      omega
  have := r.isLt
  have := r'.isLt
  exact Fin.ext (by omega)

/-- The generators `(spinRep (n - 2r) α)_r` of the product algebra. -/
noncomputable def sgen (n : ℕ) (α : Axis) : PA n := fun r => spinRep (n - 2 * r.val) α

/-- The scalar family `(c_r • 1)_r`. -/
noncomputable def scal (n : ℕ) (g : Fin (n / 2 + 1) → ℂ) : PA n := fun r => algebraMap ℂ _ (g r)

lemma scal_mul (n : ℕ) (g h : Fin (n / 2 + 1) → ℂ) : scal n (g * h) = scal n g * scal n h := by
  funext r; simp [scal, Pi.mul_apply, map_mul]

lemma scal_one (n : ℕ) : scal n 1 = 1 := by
  funext r; simp [scal]

theorem adjoin_prod (n : ℕ) :
    Algebra.adjoin ℂ (Set.range (fun α : Axis =>
      (fun r : Fin (n / 2 + 1) => spinRep (n - 2 * r.val) α))) = ⊤ := by
  change Algebra.adjoin ℂ (Set.range (sgen n)) = ⊤
  have hgen : ∀ α, sgen n α ∈ Algebra.adjoin ℂ (Set.range (sgen n)) :=
    fun α => Algebra.subset_adjoin ⟨α, rfl⟩
  generalize hS : Algebra.adjoin ℂ (Set.range (sgen n)) = S at hgen ⊢
  let c : Fin (n / 2 + 1) → ℂ :=
    fun r => (((n - 2 * r.val) * (n - 2 * r.val + 2) : ℕ) : ℂ) / 4
  have hCm : scal n c ∈ S := by
    have hC : sgen n .x * sgen n .x + sgen n .y * sgen n .y + sgen n .z * sgen n .z
        = scal n c := by
      funext r
      simp only [Pi.add_apply, Pi.mul_apply, sgen, scal]
      exact casimir (n - 2 * r.val)
    rw [← hC]
    exact S.add_mem (S.add_mem (S.mul_mem (hgen _) (hgen _)) (S.mul_mem (hgen _) (hgen _)))
      (S.mul_mem (hgen _) (hgen _))
  have hone : ∀ r : Fin (n / 2 + 1), (Pi.single r 1 : PA n) ∈ S := by
    intro r
    have hfac : ∀ t, scal n (fun r' => c r' - c t) ∈ S := by
      intro t
      have e : scal n (fun r' => c r' - c t) = scal n c - algebraMap ℂ (PA n) (c t) := by
        funext r'; simp [scal, map_sub]
      rw [e]; exact S.sub_mem hCm (S.algebraMap_mem _)
    have hmem : scal n (∏ t ∈ Finset.univ.erase r, fun r' => c r' - c t) ∈ S := by
      refine Finset.prod_induction _ (fun g => scal n g ∈ S) ?_ ?_ ?_
      · intro a b ha hb; rw [scal_mul]; exact S.mul_mem ha hb
      · rw [scal_one]; exact S.one_mem
      · intro t _; exact hfac t
    have hD : ∏ t ∈ Finset.univ.erase r, (c r - c t) ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro t ht
      rw [sub_ne_zero]
      intro e
      exact (Finset.mem_erase.1 ht).1 (cas_inj n r t e).symm
    have e : (Pi.single r 1 : PA n)
        = (∏ t ∈ Finset.univ.erase r, (c r - c t))⁻¹ •
          scal n (∏ t ∈ Finset.univ.erase r, fun r' => c r' - c t) := by
      funext r'
      rw [Pi.smul_apply]
      simp only [scal, Finset.prod_apply]
      rw [Algebra.algebraMap_eq_smul_one, smul_smul]
      by_cases hr : r' = r
      · subst hr
        rw [Pi.single_eq_same, inv_mul_cancel₀ hD, one_smul]
      · have hz : ∏ t ∈ Finset.univ.erase r, (c r' - c t) = 0 :=
          Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hr, Finset.mem_univ _⟩) (sub_self _)
        rw [Pi.single_eq_of_ne hr, hz, mul_zero, zero_smul]
    rw [e]; exact S.smul_mem hmem _
  have hsingle : ∀ (r : Fin (n / 2 + 1)) (Y : Matrix (Fin (n - 2 * r.val + 1))
      (Fin (n - 2 * r.val + 1)) ℂ), (Pi.single r Y : PA n) ∈ S := by
    intro r Y
    have hY : Y ∈ Algebra.adjoin ℂ (Set.range (spinRep (n - 2 * r.val))) := by
      rw [adjoin_spinRep]; trivial
    induction hY using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨α, rfl⟩ := hx
      have e : (Pi.single r (spinRep (n - 2 * r.val) α) : PA n) = Pi.single r 1 * sgen n α := by
        funext r'
        rw [Pi.mul_apply]
        by_cases hr : r' = r
        · subst hr
          rw [Pi.single_eq_same, Pi.single_eq_same, one_mul]; rfl
        · rw [Pi.single_eq_of_ne hr, Pi.single_eq_of_ne hr, zero_mul]
      rw [e]; exact S.mul_mem (hone r) (hgen α)
    | algebraMap a =>
      have e : (Pi.single r (algebraMap ℂ _ a) : PA n) = a • Pi.single r 1 := by
        funext r'
        rw [Pi.smul_apply]
        by_cases hr : r' = r
        · subst hr
          rw [Pi.single_eq_same, Pi.single_eq_same, Algebra.algebraMap_eq_smul_one]
        · rw [Pi.single_eq_of_ne hr, Pi.single_eq_of_ne hr, smul_zero]
      rw [e]; exact S.smul_mem (hone r) a
    | add x y _ _ hx hy =>
      rw [Pi.single_add]; exact S.add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [Pi.single_mul]; exact S.mul_mem hx hy
  rw [eq_top_iff]
  intro X _
  rw [← Finset.univ_sum_single X]
  exact Subalgebra.sum_mem _ fun r _ => hsingle r (X r)

lemma blockOp_one (n : ℕ) (m : Fin (n / 2 + 1) → ℕ) : blockOp n m 1 = 1 := by
  unfold blockOp
  rw [← Matrix.blockDiagonal'_one]
  congr 1; funext r
  exact Matrix.one_kronecker_one

lemma blockOp_smul (n : ℕ) (m : Fin (n / 2 + 1) → ℕ) (a : ℂ) (X : PA n) :
    blockOp n m (a • X) = a • blockOp n m X := by
  unfold blockOp
  rw [← Matrix.blockDiagonal'_smul]
  congr 1; funext r
  rw [Pi.smul_apply, Pi.smul_apply]
  unfold Matrix.kronecker
  exact Matrix.kronecker_smul a _ _

lemma blockOp_add (n : ℕ) (m : Fin (n / 2 + 1) → ℕ) (X Y : PA n) :
    blockOp n m (X + Y) = blockOp n m X + blockOp n m Y := by
  unfold blockOp
  rw [← Matrix.blockDiagonal'_add]
  congr 1; funext r
  rw [Pi.add_apply, Pi.add_apply]
  unfold Matrix.kronecker
  exact Matrix.kronecker_add _ _ _

lemma blockOp_mul (n : ℕ) (m : Fin (n / 2 + 1) → ℕ) (X Y : PA n) :
    blockOp n m (X * Y) = blockOp n m X * blockOp n m Y := by
  unfold blockOp
  rw [← Matrix.blockDiagonal'_mul]
  congr 1; funext r
  rw [Pi.mul_apply]
  unfold Matrix.kronecker
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- `blockOp` as an algebra homomorphism. -/
noncomputable def blockHom (n : ℕ) (m : Fin (n / 2 + 1) → ℕ) :
    PA n →ₐ[ℂ] Matrix (BlockIdx n m) (BlockIdx n m) ℂ where
  toFun := blockOp n m
  map_one' := blockOp_one n m
  map_mul' := blockOp_mul n m
  map_zero' := by
    have := blockOp_smul n m 0 0
    rwa [zero_smul, zero_smul] at this
  map_add' := blockOp_add n m
  commutes' a := by
    simp only [Algebra.algebraMap_eq_smul_one]
    rw [blockOp_smul, blockOp_one]

lemma blockHom_apply (n : ℕ) (m : Fin (n / 2 + 1) → ℕ) (X : PA n) :
    blockHom n m X = blockOp n m X := rfl

lemma blockOp_apply_same (n : ℕ) (m : Fin (n / 2 + 1) → ℕ) (X : PA n) (r : Fin (n / 2 + 1))
    (l : Fin (m r)) (k : Fin (n - 2 * r.val + 1)) (l' : Fin (m r)) (k' : Fin (n - 2 * r.val + 1)) :
    blockOp n m X ⟨r, (l, k)⟩ ⟨r, (l', k')⟩ = if l = l' then X r k k' else 0 := by
  unfold blockOp
  rw [Matrix.blockDiagonal'_apply_eq]
  unfold Matrix.kronecker
  rw [Matrix.kronecker_apply, Matrix.one_apply]
  split_ifs <;> simp

lemma blockOp_apply_ne (n : ℕ) (m : Fin (n / 2 + 1) → ℕ) (X : PA n) (a b : BlockIdx n m)
    (h : a.1 ≠ b.1) : blockOp n m X a b = 0 := by
  unfold blockOp
  obtain ⟨r, i⟩ := a
  obtain ⟨r', j⟩ := b
  exact Matrix.blockDiagonal'_apply_ne (m' := fun r => Fin (m r) × Fin (n - 2 * r.val + 1))
    (n' := fun r => Fin (m r) × Fin (n - 2 * r.val + 1)) _ i j h

end Alg

end BaconThesis.Collective.Sol841

namespace BaconThesis.Collective.Sol841

open scoped InnerProductSpace
open Module Matrix BaconThesis.Collective BBPSSW.Distill

section Main

variable {n : ℕ}

lemma conj_eq_blockOp (A : Matrix (St n) (St n) ℂ)
    (X : (r : Fin (n / 2 + 1)) → Matrix (Fin (n - 2 * r.val + 1)) (Fin (n - 2 * r.val + 1)) ℂ)
    (hsame : ∀ r l l' k k', ⟪ev n ⟨r, (l, k)⟩, Lop A (ev n ⟨r, (l', k')⟩)⟫_ℂ
      = if l = l' then X r k k' else 0)
    (hne : ∀ a b : BlockIdx n (mult n), a.1 ≠ b.1 → ⟪ev n a, Lop A (ev n b)⟫_ℂ = 0) :
    W n * A * (W n)ᴴ = blockOp n (mult n) X := by
  refine Matrix.ext fun a b => ?_
  rw [conj_apply]
  obtain ⟨r, l, k⟩ := a
  obtain ⟨r', l', k'⟩ := b
  by_cases hr : r = r'
  · subst hr
    rw [blockOp_apply_same, hsame]
  · rw [blockOp_apply_ne _ _ _ ⟨r, (l, k)⟩ ⟨r', (l', k')⟩ hr]
    exact hne _ _ hr

lemma rep_Sp : W n * Sp n * (W n)ᴴ = blockOp n (mult n) fun r => spP (n - 2 * r.val) := by
  refine conj_eq_blockOp _ _ (fun r l l' k k' => ?_) (ne_zero_of _ (Or.inl rfl))
  rw [Sp_same]
  simp [spP]

lemma rep_Sm : W n * Sm n * (W n)ᴴ = blockOp n (mult n) fun r => (spP (n - 2 * r.val))ᴴ := by
  refine conj_eq_blockOp _ _ (fun r l l' k k' => ?_) (ne_zero_of _ (Or.inr (Or.inl rfl)))
  rw [Sm_same]
  simp only [conjTranspose_apply, spP, Matrix.of_apply]
  by_cases hl : l = l'
  · by_cases hk : (k' : ℕ) + 1 = k
    · simp [hl, hk, Complex.conj_ofReal]
    · simp [hl, hk]
  · simp [hl]

lemma rep_Sz : W n * Sz n * (W n)ᴴ = blockOp n (mult n) fun r => spinRep (n - 2 * r.val) .z := by
  refine conj_eq_blockOp _ _ (fun r l l' k k' => ?_) (ne_zero_of _ (Or.inr (Or.inr rfl)))
  rw [Sz_same, spinRep_z]
  simp [Matrix.diagonal_apply]

lemma conj_lin (c : ℂ) (A B : Matrix (St n) (St n) ℂ) :
    W n * (c • (A + B)) * (W n)ᴴ = c • (W n * A * (W n)ᴴ + W n * B * (W n)ᴴ) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul]

lemma conj_lin' (c : ℂ) (A B : Matrix (St n) (St n) ℂ) :
    W n * (c • (A - B)) * (W n)ᴴ = c • (W n * A * (W n)ᴴ - W n * B * (W n)ᴴ) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul]

lemma rep (α : Axis) :
    W n * collS n α * (W n)ᴴ = blockOp n (mult n) (fun r => spinRep (n - 2 * r.val) α) := by
  cases α with
  | x =>
    rw [collS_x, conj_lin, rep_Sp, rep_Sm, ← blockHom_apply, ← blockHom_apply, ← map_add,
      ← map_smul, blockHom_apply]
    congr 1
  | y =>
    rw [collS_y, conj_lin', rep_Sp, rep_Sm, ← blockHom_apply, ← blockHom_apply, ← map_sub,
      ← map_smul, blockHom_apply]
    congr 1
  | z => rw [collS_z, rep_Sz]

variable (n) in
/-- Conjugation by `W`, an algebra isomorphism onto its image. -/
noncomputable def Φ : Matrix (St n) (St n) ℂ →ₐ[ℂ] Matrix (BlockIdx n (mult n)) (BlockIdx n (mult n)) ℂ where
  toFun A := W n * A * (W n)ᴴ
  map_one' := by rw [Matrix.mul_one, W_mul_star]
  map_mul' A B := by
    rw [show W n * A * (W n)ᴴ * (W n * B * (W n)ᴴ) = W n * A * ((W n)ᴴ * W n) * B * (W n)ᴴ by
      simp only [Matrix.mul_assoc], star_mul_W, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  map_zero' := by simp
  map_add' A B := by simp [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      W_mul_star]

lemma Φ_apply (A : Matrix (St n) (St n) ℂ) : Φ n A = W n * A * (W n)ᴴ := rfl

lemma Φ_inj {A B : Matrix (St n) (St n) ℂ} (h : Φ n A = Φ n B) : A = B := by
  have e : ∀ C : Matrix (St n) (St n) ℂ, C = (W n)ᴴ * Φ n C * W n := by
    intro C
    rw [Φ_apply, show (W n)ᴴ * (W n * C * (W n)ᴴ) * W n
      = ((W n)ᴴ * W n) * C * ((W n)ᴴ * W n) by simp only [Matrix.mul_assoc], star_mul_W,
      Matrix.one_mul, Matrix.mul_one]
  rw [e A, e B, h]

lemma alg (A : Matrix (St n) (St n) ℂ) :
    A ∈ Algebra.adjoin ℂ (Set.range (collS n)) ↔
      ∃ X : (r : Fin (n / 2 + 1)) →
          Matrix (Fin (n - 2 * r.val + 1)) (Fin (n - 2 * r.val + 1)) ℂ,
        W n * A * (W n)ᴴ = blockOp n (mult n) X := by
  constructor
  · intro hA
    have hle : Algebra.adjoin ℂ (Set.range (collS n))
        ≤ ((blockHom n (mult n)).range).comap (Φ n) := by
      rw [Algebra.adjoin_le_iff]
      rintro _ ⟨α, rfl⟩
      exact ⟨_, (blockHom_apply _ _ _).trans (rep α).symm⟩
    obtain ⟨X, hX⟩ := hle hA
    exact ⟨X, ((blockHom_apply _ _ _).symm.trans hX).symm⟩
  · rintro ⟨X, hX⟩
    have hX' : blockHom n (mult n) X ∈ (Algebra.adjoin ℂ (Set.range (collS n))).map (Φ n) := by
      rw [AlgHom.map_adjoin]
      have hs : Φ n '' Set.range (collS n) = blockHom n (mult n) '' Set.range
          (fun α : Axis => (fun r : Fin (n / 2 + 1) => spinRep (n - 2 * r.val) α)) := by
        rw [← Set.range_comp, ← Set.range_comp]
        congr 1
        funext α
        simp only [Function.comp_apply, Φ_apply, rep, blockHom_apply]
      rw [hs, ← AlgHom.map_adjoin, adjoin_prod]
      exact ⟨X, trivial, rfl⟩
    obtain ⟨A', hA', he⟩ := hX'
    rw [blockHom_apply, ← hX] at he
    rw [← Φ_inj he]
    exact hA'

end Main

end BaconThesis.Collective.Sol841

open Matrix BaconThesis.Collective BaconThesis.Collective.Sol841 in
theorem solution (n : ℕ) :
    ∃ (m : Fin (n / 2 + 1) → ℕ) (W : Matrix (BlockIdx n m) (Fin n → Fin 2) ℂ),
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧
      (∀ α : BBPSSW.Distill.Axis, W * collS n α * Wᴴ = blockOp n m (fun r => spinRep (n - 2 * r.val) α)) ∧
      (∀ r : Fin (n / 2 + 1), (m r : ℚ) = degeneracy n r.val) ∧
      (∀ A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ,
        A ∈ Algebra.adjoin ℂ (Set.range (collS n)) ↔
          ∃ X : (r : Fin (n / 2 + 1)) →
              Matrix (Fin (n - 2 * r.val + 1)) (Fin (n - 2 * r.val + 1)) ℂ,
            W * A * Wᴴ = blockOp n m X) :=
  ⟨mult n, W n, star_mul_W, W_mul_star, rep, mult_eq, alg⟩
