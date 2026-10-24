-- Prove2me | solution 1 for BellDetEff.TwoParty.lhv_bound
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:10:11.19553+00:00
-- url     : https://prove2.me/submissions/f08b1ab3-2e32-4d40-a060-a9f7ba39ae7a

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_BellInequality
import Theorems.Thm_BellDetEff_TwoParty_eqs_8_11_inconsistent

open scoped BigOperators
open Finset

namespace BellDetEff.TwoParty.RectangleProof

noncomputable def joint {P MA MB : ℕ} (F : Fin MA → Option (Fin P))
    (G : Fin MB → Option (Fin P)) (x : Fin MA) (y : Fin MB) : ℝ :=
  (F x).elim 0 fun a => (G y).elim 0 fun b => bellF P a b x y

noncomputable def penalty {P M : ℕ} (F : Fin M → Option (Fin P)) (x : Fin M) : ℝ :=
  (F x).elim 0 fun _ => bellG x

lemma marginalA_det {P MA MB : ℕ} (hB : 0 < MB)
    (F : Fin MA → Option (Fin P)) (G : Fin MB → Option (Fin P))
    (a : Option (Fin P)) (x : Fin MA) :
    marginalA (deterministic F G) a x = if F x = a then 1 else 0 := by
  classical
  simp only [marginalA, deterministic]
  by_cases h : F x = a
  · simp [h, ne_of_gt hB]
  · simp [h]

lemma marginalB_det {P MA MB : ℕ} (hA : 0 < MA)
    (F : Fin MA → Option (Fin P)) (G : Fin MB → Option (Fin P))
    (b : Option (Fin P)) (y : Fin MB) :
    marginalB (deterministic F G) b y = if G y = b then 1 else 0 := by
  classical
  simp only [marginalB, deterministic]
  by_cases h : G y = b
  · simp [h, ne_of_gt hA]
  · simp [h]

lemma bellValue_det {P MA MB : ℕ} (hA : 0 < MA) (hB : 0 < MB)
    (F : Fin MA → Option (Fin P)) (G : Fin MB → Option (Fin P)) :
    bellValue P (deterministic F G) =
      (∑ x, ∑ y, joint F G x y) + (∑ x, penalty F x) + ∑ y, penalty G y := by
  classical
  unfold bellValue
  apply congrArg₂ (fun u v : ℝ => u + v)
  · apply congrArg₂ (fun u v : ℝ => u + v)
    · conv_lhs => enter [2, a]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      conv_lhs => enter [2, a]; rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y hy
      cases hFx : F x <;> cases hGy : G y <;>
        simp [joint, deterministic, hFx, hGy, ite_and]
    · rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      simp_rw [marginalA_det hB]
      cases hFx : F x <;> simp [penalty, hFx]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y hy
    simp_rw [marginalB_det hA]
    cases hGy : G y <;> simp [penalty, hGy, bellH, bellG]

lemma penalty_nonpos {P M : ℕ} (F : Fin M → Option (Fin P)) (x : Fin M) :
    penalty F x ≤ 0 := by
  cases h : F x <;> simp [penalty, h, bellG]
  split_ifs <;> norm_num

lemma joint_le_one {P MA MB : ℕ} (F : Fin MA → Option (Fin P))
    (G : Fin MB → Option (Fin P)) (x : Fin MA) (y : Fin MB) : joint F G x y ≤ 1 := by
  cases hF : F x <;> cases hG : G y <;> simp [joint, hF, hG]
  unfold bellF
  split_ifs <;> nlinarith [sq_nonneg ((P : ℝ) ^ 2)]

lemma joint_swap {P MA MB : ℕ} (F : Fin MA → Option (Fin P))
    (G : Fin MB → Option (Fin P)) (x : Fin MA) (y : Fin MB) :
    joint F G x y = joint G F y x := by
  cases hF : F x <;> cases hG : G y <;>
    simp [joint, hF, hG, bellF, bellCong, add_comm, mul_comm, or_comm,
      and_left_comm]

lemma single_row_bound {P MA MB : ℕ} (hB : 0 < MB)
    (F : Fin MA → Option (Fin P)) (G : Fin MB → Option (Fin P))
    (hu : ∀ x₁ x₂, F x₁ ≠ none → F x₂ ≠ none → x₁ = x₂) :
    (∑ x, ∑ y, joint F G x y) + (∑ x, penalty F x) + ∑ y, penalty G y ≤ 0 := by
  classical
  by_cases he : ∀ x, F x = none
  · simp only [joint, he, Option.elim_none, sum_const_zero, penalty, zero_add]
    exact Finset.sum_nonpos fun y _ => penalty_nonpos G y
  push Not at he
  obtain ⟨x₀, hx₀⟩ := he
  have hn : ∀ x, x ≠ x₀ → F x = none := by
    intro x hx
    by_contra h
    exact hx (hu x x₀ h hx₀)
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.mp hx₀
  have hj : (∑ x, ∑ y, joint F G x y) = ∑ y, joint F G x₀ y := by
    apply Finset.sum_eq_single x₀
    · intro x hx hne
      simp [joint, hn x hne]
    · simp
  have hp : (∑ x, penalty F x) = penalty F x₀ := by
    apply Finset.sum_eq_single x₀
    · intro x hx hne
      simp [penalty, hn x hne]
    · simp
  have hb : ∀ y : Fin MB, joint F G x₀ y + penalty G y ≤
      if y.val = 0 then -penalty F x₀ else 0 := by
    intro y
    cases hG : G y <;>
      simp only [joint, penalty, ha, hG, Option.elim_some, Option.elim_none]
    · unfold bellG
      split_ifs <;> norm_num
    · unfold bellF bellG
      split_ifs <;> simp_all only [not_true_eq_false, false_or, not_false_eq_true,
        true_or, true_and, and_true] <;> nlinarith [sq_nonneg ((P : ℝ) ^ 2)]
  let y₀ : Fin MB := ⟨0, hB⟩
  have hsum : (∑ y : Fin MB, if y.val = 0 then -penalty F x₀ else 0) = -penalty F x₀ := by
    have heq : ∀ y : Fin MB, y.val = 0 ↔ y = y₀ := by
      intro y
      change y.val = y₀.val ↔ y = y₀
      exact Fin.ext_iff.symm
    simp_rw [heq]
    simp
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun y _ => hb y)
  rw [Finset.sum_add_distrib, hsum] at hh
  rw [hj, hp]
  linarith

lemma bad_pair_bound {P MA MB : ℕ} [Fact P.Prime] (hAP : MA ≤ P) (hBP : MB ≤ P)
    (F : Fin MA → Option (Fin P)) (G : Fin MB → Option (Fin P))
    (x₀ : Fin MA) (y₀ : Fin MB) (a b : Fin P)
    (hF : F x₀ = some a) (hG : G y₀ = some b) (hc : ¬ bellCong P a b x₀ y₀) :
    (∑ x, ∑ y, joint F G x y) + (∑ x, penalty F x) + ∑ y, penalty G y ≤ 0 := by
  classical
  have hj : joint F G x₀ y₀ = -((P : ℝ) ^ 4) := by simp [joint, hF, hG, bellF, hc]
  have hb : ∀ x y, joint F G x y ≤ 1 - (if x = x₀ ∧ y = y₀ then (P : ℝ) ^ 4 else 0) := by
    intro x y
    by_cases h : x = x₀ ∧ y = y₀
    · rcases h with ⟨rfl, rfl⟩
      simp only [hj, and_self, if_true]
      linarith
    · simpa only [h, if_false, sub_zero] using joint_le_one F G x y
  have hs := Finset.sum_le_sum (s := Finset.univ) fun x _ =>
    Finset.sum_le_sum (s := Finset.univ) fun y _ => hb x y
  simp only [Finset.sum_sub_distrib] at hs
  simp [ite_and] at hs
  have hP : (1 : ℝ) ≤ P := by exact_mod_cast (Nat.Prime.one_lt (Fact.out : P.Prime)).le
  have hAP' : (MA : ℝ) ≤ P := by exact_mod_cast hAP
  have hBP' : (MB : ℝ) ≤ P := by exact_mod_cast hBP
  have hmul : (MA : ℝ) * MB ≤ (P : ℝ) ^ 2 := by
    calc
      _ ≤ (P : ℝ) * P := mul_le_mul hAP' hBP' (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hp4 : (P : ℝ) ^ 2 ≤ (P : ℝ) ^ 4 := pow_le_pow_right₀ hP (by decide)
  have hpa : (∑ x, penalty F x) ≤ 0 := Finset.sum_nonpos fun x _ => penalty_nonpos F x
  have hpb : (∑ y, penalty G y) ≤ 0 := Finset.sum_nonpos fun y _ => penalty_nonpos G y
  nlinarith

lemma thin_of_all_congruent {P MA MB : ℕ} [Fact P.Prime] (hAP : MA ≤ P) (hBP : MB ≤ P)
    (F : Fin MA → Option (Fin P)) (G : Fin MB → Option (Fin P))
    (hc : ∀ x y a b, F x = some a → G y = some b → bellCong P a b x y) :
    (∀ x₁ x₂, F x₁ ≠ none → F x₂ ≠ none → x₁ = x₂) ∨
      (∀ y₁ y₂, G y₁ ≠ none → G y₂ ≠ none → y₁ = y₂) := by
  classical
  by_cases hF : ∀ x₁ x₂, F x₁ ≠ none → F x₂ ≠ none → x₁ = x₂
  · exact Or.inl hF
  right
  push Not at hF
  obtain ⟨x₁, x₂, hx₁, hx₂, hx⟩ := hF
  obtain ⟨a₁, ha₁⟩ := Option.ne_none_iff_exists'.mp hx₁
  obtain ⟨a₂, ha₂⟩ := Option.ne_none_iff_exists'.mp hx₂
  intro y₁ y₂ hy₁ hy₂
  by_contra hy
  obtain ⟨b₁, hb₁⟩ := Option.ne_none_iff_exists'.mp hy₁
  obtain ⟨b₂, hb₂⟩ := Option.ne_none_iff_exists'.mp hy₂
  have hh := eqs_8_11_inconsistent P (x₁.val + 1) (x₂.val + 1) (y₁.val + 1) (y₂.val + 1)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by intro h; apply hx; apply Fin.ext; omega)
    (by intro h; apply hy; apply Fin.ext; omega)
    (a₁.val : ZMod P) (a₂.val : ZMod P) (b₁.val : ZMod P) (b₂.val : ZMod P)
  exact hh ⟨hc x₁ y₁ a₁ b₁ ha₁ hb₁, hc x₁ y₂ a₁ b₂ ha₁ hb₂,
    hc x₂ y₁ a₂ b₁ ha₂ hb₁, hc x₂ y₂ a₂ b₂ ha₂ hb₂⟩

end BellDetEff.TwoParty.RectangleProof

open BellDetEff.TwoParty BellDetEff.TwoParty.RectangleProof

theorem rectangle_deterministic_bound (P MA MB : ℕ) [Fact P.Prime] (hAP : MA ≤ P) (hBP : MB ≤ P)
    (F : Fin MA → Option (Fin P)) (G : Fin MB → Option (Fin P)) :
    bellValue P (deterministic F G) ≤ 0 := by
  classical
  by_cases hA : MA = 0
  · subst MA
    simp [bellValue, marginalA, marginalB]
  by_cases hB : MB = 0
  · subst MB
    simp [bellValue, marginalA, marginalB]
  have hAp : 0 < MA := Nat.pos_of_ne_zero hA
  have hBp : 0 < MB := Nat.pos_of_ne_zero hB
  rw [bellValue_det hAp hBp]
  by_cases hc : ∀ x y a b, F x = some a → G y = some b → bellCong P a b x y
  · rcases thin_of_all_congruent hAP hBP F G hc with hF | hG
    · exact single_row_bound hBp F G hF
    · have hh := single_row_bound hAp G F hG
      have hs : (∑ y, ∑ x, joint G F y x) = ∑ x, ∑ y, joint F G x y := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        exact joint_swap G F y x
      rw [hs] at hh
      linarith
  · push Not at hc
    obtain ⟨x, y, a, b, hF, hG, hbad⟩ := hc
    exact bad_pair_bound hAP hBP F G x y a b hF hG hbad


noncomputable section

open MeasureTheory
open scoped BigOperators

namespace BellDetEff.TwoParty.LHVProof

lemma policy_marginal {I O : Type*} [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (p : I → O → ℝ)
    (hp : ∀ i, ∑ a, p i a = 1) (i : I) (a : O) :
    (∑ F : I → O, (∏ j, p j (F j)) * (if F i = a then 1 else 0)) = p i a := by
  have hprod : ∀ F : I → O,
      (∏ j, p j (F j) * (if j = i then (if F j = a then 1 else 0) else 1)) =
        (∏ j, p j (F j)) * (if F i = a then 1 else 0) := by
    intro F
    rw [Finset.prod_mul_distrib]
    simp
  rw [← Finset.sum_congr rfl (fun F _ => hprod F),
    ← Fintype.prod_sum (fun j b => p j b *
      (if j = i then (if b = a then 1 else 0) else 1))]
  have hs : ∀ j : I,
      (∑ b : O, p j b * (if j = i then (if b = a then 1 else 0) else 1)) =
        if j = i then p i a else 1 := by
    intro j
    by_cases h : j = i
    · subst j; simp
    · simp [h, hp]
  simp_rw [hs]
  simp

lemma product_mixture {OA OB : Type} [Fintype OA] [DecidableEq OA]
    [Fintype OB] [DecidableEq OB] {MA MB : ℕ}
    (pA : Fin MA → OA → ℝ) (pB : Fin MB → OB → ℝ)
    (hA : ∀ x, ∑ a, pA x a = 1) (hB : ∀ y, ∑ b, pB y b = 1) :
    (fun a b x y => pA x a * pB y b) =
      ∑ F : Fin MA → OA, ∑ G : Fin MB → OB,
        ((∏ x, pA x (F x)) * (∏ y, pB y (G y))) • deterministic F G := by
  funext a b x y
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hd : ∀ F : Fin MA → OA, ∀ G : Fin MB → OB,
      ((∏ x, pA x (F x)) * (∏ y, pB y (G y))) * deterministic F G a b x y =
        ((∏ x, pA x (F x)) * (if F x = a then 1 else 0)) *
          ((∏ y, pB y (G y)) * (if G y = b then 1 else 0)) := by
    intro F G
    by_cases hx : F x = a <;> by_cases hy : G y = b <;>
      simp [deterministic, hx, hy]
  simp_rw [hd, ← Finset.mul_sum]
  rw [← Finset.sum_mul, policy_marginal pA hA, policy_marginal pB hB]

lemma linear_nonpos_of_product {OA OB : Type} [Fintype OA] [DecidableEq OA]
    [Fintype OB] [DecidableEq OB] {MA MB : ℕ}
    (L : (OA → OB → Fin MA → Fin MB → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ (F : Fin MA → OA) (G : Fin MB → OB), L (deterministic F G) ≤ 0)
    (pA : Fin MA → OA → ℝ) (pB : Fin MB → OB → ℝ)
    (hA0 : ∀ x a, 0 ≤ pA x a) (hB0 : ∀ y b, 0 ≤ pB y b)
    (hA : ∀ x, ∑ a, pA x a = 1) (hB : ∀ y, ∑ b, pB y b = 1) :
    L (fun a b x y => pA x a * pB y b) ≤ 0 := by
  rw [product_mixture pA pB hA hB]
  simp only [map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_nonpos
  intro F _
  apply Finset.sum_nonpos
  intro G _
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg (Finset.prod_nonneg (fun x _ => hA0 x (F x)))
      (Finset.prod_nonneg (fun y _ => hB0 y (G y)))) (hL F G)

lemma response_integrable {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (M : LHVModel OA OB MA MB) (a : OA) (b : OB) (x : Fin MA) (y : Fin MB) :
    Integrable (fun l => M.pA x l a * M.pB y l b) M.μ := by
  have hA1 : ∀ l, M.pA x l a ≤ 1 := by
    intro l
    rw [← M.pA_sum x l]
    exact Finset.single_le_sum (fun c _ => M.pA_nonneg x l c) (Finset.mem_univ a)
  have hB1 : ∀ l, M.pB y l b ≤ 1 := by
    intro l
    rw [← M.pB_sum y l]
    exact Finset.single_le_sum (fun c _ => M.pB_nonneg y l c) (Finset.mem_univ b)
  apply (integrable_const (1 : ℝ)).mono'
    ((M.measurable_pA x a).mul (M.measurable_pB y b)).aestronglyMeasurable
  filter_upwards [] with l
  change ‖M.pA x l a * M.pB y l b‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (M.pA_nonneg x l a) (M.pB_nonneg y l b))]
  exact mul_le_one₀ (hA1 l) (M.pB_nonneg y l b) (hB1 l)

lemma linear_nonpos_of_lhv {OA OB : Type} [Fintype OA] [DecidableEq OA]
    [Fintype OB] [DecidableEq OB] {MA MB : ℕ}
    (L : (OA → OB → Fin MA → Fin MB → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ (F : Fin MA → OA) (G : Fin MB → OB), L (deterministic F G) ≤ 0)
    (p : OA → OB → Fin MA → Fin MB → ℝ) (hp : LHVSimulable p) : L p ≤ 0 := by
  rcases hp with ⟨M, hM⟩
  let q : M.Λ → OA → OB → Fin MA → Fin MB → ℝ :=
    fun l a b x y => M.pA x l a * M.pB y l b
  have hq : Integrable q M.μ := by
    apply Integrable.of_eval
    intro a
    apply Integrable.of_eval
    intro b
    apply Integrable.of_eval
    intro x
    apply Integrable.of_eval
    intro y
    exact response_integrable M a b x y
  have hpi : p = ∫ l, q l ∂M.μ := by
    funext a b x y
    rw [eval_integral (fun a => hq.eval a),
      eval_integral (fun b => (hq.eval a).eval b),
      eval_integral (fun x => ((hq.eval a).eval b).eval x),
      eval_integral (fun y => (((hq.eval a).eval b).eval x).eval y)]
    exact hM a b x y
  rw [hpi]
  change L.toContinuousLinearMap (∫ l, q l ∂M.μ) ≤ 0
  rw [← ContinuousLinearMap.integral_comp_comm _ hq]
  apply integral_nonpos
  intro l
  exact linear_nonpos_of_product L hL (fun x => M.pA x l) (fun y => M.pB y l)
    (fun x a => M.pA_nonneg x l a) (fun y b => M.pB_nonneg y l b)
    (fun x => M.pA_sum x l) (fun y => M.pB_sum y l)

def bellLinear (P MA MB : ℕ) :
    (Option (Fin P) → Option (Fin P) → Fin MA → Fin MB → ℝ) →ₗ[ℝ] ℝ where
  toFun := bellValue P
  map_add' p q := by
    simp only [bellValue, marginalA, marginalB, Pi.add_apply, mul_add,
      Finset.sum_add_distrib]
    ring
  map_smul' c p := by
    simp only [bellValue, marginalA, marginalB, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    simp only [Finset.mul_sum, mul_add, mul_assoc, mul_left_comm, mul_comm]

lemma bell_nonpos_of_lhv (P MA MB : ℕ)
    (hdet : ∀ (F : Fin MA → Option (Fin P)) (G : Fin MB → Option (Fin P)),
      bellValue P (deterministic F G) ≤ 0)
    (p : Option (Fin P) → Option (Fin P) → Fin MA → Fin MB → ℝ)
    (hp : LHVSimulable p) : bellValue P p ≤ 0 :=
  linear_nonpos_of_lhv (bellLinear P MA MB) hdet p hp

end BellDetEff.TwoParty.LHVProof

open BellDetEff.TwoParty

theorem solution (P MA MB : ℕ) [Fact P.Prime] (hAP : MA ≤ P) (hBP : MB ≤ P)
    (p : Option (Fin P) → Option (Fin P) → Fin MA → Fin MB → ℝ)
    (hp : LHVSimulable p) : bellValue P p ≤ 0 :=
  LHVProof.bell_nonpos_of_lhv P MA MB
    (rectangle_deterministic_bound P MA MB hAP hBP) p hp
