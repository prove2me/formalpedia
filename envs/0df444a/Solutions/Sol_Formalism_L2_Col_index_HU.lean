-- Prove2me | solution 1 for Formalism.L2.Col.index_HU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:08:12.97323+00:00
-- url     : https://prove2.me/submissions/a2a75f3e-d970-4c2f-b21a-80b3893cb437

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
namespace Formalism.L2.Col
section
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
end
section Uni
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
end Uni
private theorem prod_one_sub_lemma {ι : Type} (s : Finset ι) (f : ι → ℝ) (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) ∧ ∏ i ∈ s, (1 - f i) ≤ 1 ∧ 0 ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    obtain ⟨i1, i2, i3⟩ := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have fa0 := h0 a (Finset.mem_insert_self a s)
    have fa1 := h1 a (Finset.mem_insert_self a s)
    refine ⟨?_, ?_, ?_⟩
    · nlinarith [mul_nonneg fa0 (sub_nonneg.mpr i2)]
    · nlinarith [mul_nonneg fa0 i3]
    · exact mul_nonneg (by linarith) i3
private theorem card_GL_eq_card_pow_mul_theta (F : Type) [Field F] [Fintype F] (n : ℕ) (h3 : 3 ≤ Fintype.card F) :
    ∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧
      (Nat.card (GL (Fin n) F) : ℝ) = (Fintype.card F : ℝ) ^ (n * n) * θ := by
  have hq3 : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h3
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by linarith
  have hqn : (0 : ℝ) < (Fintype.card F : ℝ) ^ n := pow_pos hqpos n
  have hx0 : ∀ i : Fin n, 0 ≤ (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n := fun i => by positivity
  have hx1 : ∀ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤ 1 := by
    intro i
    rw [div_le_one hqn]
    have : Fintype.card F ^ (i : ℕ) ≤ Fintype.card F ^ n := Nat.pow_le_pow_right (by omega) i.2.le
    exact_mod_cast this
  have hsum : ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤ 1 / 2 := by
    have hgs : ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) = ∑ i ∈ Finset.range n, (Fintype.card F : ℝ) ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => (Fintype.card F : ℝ) ^ i) n
    rw [← Finset.sum_div, hgs, geom_sum_eq (by linarith), div_div, div_le_iff₀ (by nlinarith)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hq3) hqn.le]
  have hb := prod_one_sub_lemma Finset.univ (fun i : Fin n => (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n)
    (fun i _ => hx0 i) (fun i _ => hx1 i)
  have b1 : 1 - ∑ i : Fin n, (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n ≤
      ∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) := hb.1
  have b2 : ∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) ≤ 1 := hb.2.1
  refine ⟨∏ i : Fin n, (1 - (Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n), by linarith, b2, ?_⟩
  have hrhs : (Fintype.card F : ℝ) ^ (n * n) = ∏ _i : Fin n, (Fintype.card F : ℝ) ^ n := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [Matrix.card_GL_field, Nat.cast_prod, hrhs, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hle : Fintype.card F ^ (i : ℕ) ≤ Fintype.card F ^ n := Nat.pow_le_pow_right (by omega) i.2.le
  have hcan : (Fintype.card F : ℝ) ^ n * ((Fintype.card F : ℝ) ^ (i : ℕ) / (Fintype.card F : ℝ) ^ n) =
      (Fintype.card F : ℝ) ^ (i : ℕ) := by
    field_simp
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_pow, mul_sub, mul_one, hcan]
section Diag
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
end Diag
example : Nat.card ↥(HU (ZMod 3) 2) = 3 := by rw [card_HU]; simp
example : Nat.card ↥(HU (ZMod 5) 4) = 5 ^ 6 := by rw [card_HU]; simp
example : lamX (ZMod.stdAddChar (N := 3)) (fun _ => 1) 8 3 2 4 1 ≠ 1 :=
  lamX_ne_one stdAddChar_ne_one _ 2 4 1 (by norm_num) (by norm_num)
section DiagChar
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]
end DiagChar
section Sym
variable {n : ℕ} {κ : Type} [CommRing κ]
end Sym
section More
variable {κ : Type} [CommRing κ] {K : Type} [Field K]
end More
section Res
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
end Res
section ParId
variable {n : ℕ} {κ : Type} [CommRing κ]
end ParId
end Formalism.L2.Col
end
end

set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
namespace Formalism.L2.Col
theorem _root_.solution (F : Type) [Field F] [Fintype F] [DecidableEq F] (k : ℕ) (h3 : 3 ≤ Fintype.card F) :
    ∃ θ : ℝ, 1 / 2 ≤ θ ∧ θ ≤ 1 ∧ ((HU F k).index : ℝ) = (Fintype.card F : ℝ) ^ (k * (k + 1) / 2) * θ := by
  obtain ⟨θ, h1, h2, hc⟩ := card_GL_eq_card_pow_mul_theta F k h3
  refine ⟨θ, h1, h2, ?_⟩
  have hH : Nat.card ↥(HU F k) = Fintype.card F ^ (k * (k - 1) / 2) := by
    rw [card_HU, Nat.card_eq_fintype_card (α := F)]
  have hmul := Subgroup.card_mul_index (HU F k)
  rw [hH] at hmul
  have hexp : k * k = k * (k - 1) / 2 + k * (k + 1) / 2 := by
    cases k with
    | zero => rfl
    | succ k =>
      have hA : (k + 1) * (k + 1 - 1) = (k + 1) * k := by simp
      have hB : (k + 1) * (k + 1 + 1) = (k + 1) * k + 2 * (k + 1) := by ring
      have hC : (k + 1) * (k + 1) = (k + 1) * k + (k + 1) := by ring
      have hE : (k + 1) * k % 2 = 0 := by
        rcases Nat.even_mul_succ_self k with ⟨t, ht⟩
        rw [Nat.mul_comm, ht]
        omega
      rw [hA, hB, hC, Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
      generalize (k + 1) * k = A at hE ⊢
      omega
  have hpos : (0 : ℝ) < (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) := by
    have : (0 : ℝ) < (Fintype.card F : ℝ) := by
      have : (3 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast h3
      linarith
    positivity
  have hR : (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) * ((HU F k).index : ℝ) =
      (Fintype.card F : ℝ) ^ (k * (k - 1) / 2) * ((Fintype.card F : ℝ) ^ (k * (k + 1) / 2) * θ) := by
    have hm := congrArg (fun x : ℕ => (x : ℝ)) hmul
    push_cast at hm
    rw [hm, hc, hexp, pow_add, mul_assoc]
  exact mul_left_cancel₀ hpos.ne' hR
end Formalism.L2.Col
