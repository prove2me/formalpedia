-- Prove2me | solution 1 for BellDetEff.TwoParty.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @xwh
-- created : 2026-10-23T08:22:44.265305+00:00
-- url     : https://prove2.me/submissions/4b6b3382-f644-4a3c-b9ba-5ebd4e603907

import Mathlib
import Definitions.Def_BellDetEff_TwoParty_Efficiency

open MeasureTheory
open scoped BigOperators

namespace BellDetEff.TwoParty.ThinningProof

noncomputable def thinResponse {O : Type} (q : ℝ) (v : Option O → ℝ)
    (a : Option O) : ℝ := q * v a + a.elim (1 - q) (fun _ => 0)

lemma thinResponse_nonneg {O : Type} (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (v : Option O → ℝ) (hv : ∀ a, 0 ≤ v a) (a : Option O) :
    0 ≤ thinResponse q v a := by
  cases a <;> simp only [thinResponse, Option.elim_none, Option.elim_some, add_zero]
  · exact add_nonneg (mul_nonneg hq (hv none)) (sub_nonneg.mpr hq1)
  · exact mul_nonneg hq (hv _)

lemma thinResponse_sum {O : Type} [Fintype O] (q : ℝ) (v : Option O → ℝ)
    (hv : ∑ a, v a = 1) : ∑ a, thinResponse q v a = 1 := by
  simp only [thinResponse, Finset.sum_add_distrib, ← Finset.mul_sum, hv,
    Fintype.sum_option, Option.elim_none, Option.elim_some, Finset.sum_const_zero, add_zero]
  ring

noncomputable def thinModel {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (M : LHVModel (Option OA) (Option OB) MA MB) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    LHVModel (Option OA) (Option OB) MA MB where
  Λ := M.Λ
  μ := M.μ
  pA x l := thinResponse q (M.pA x l)
  pB y l := thinResponse q (M.pB y l)
  measurable_pA x a := ((M.measurable_pA x a).const_mul q).add measurable_const
  measurable_pB y b := ((M.measurable_pB y b).const_mul q).add measurable_const
  pA_nonneg x l a := thinResponse_nonneg q hq hq1 _ (M.pA_nonneg x l) a
  pB_nonneg y l b := thinResponse_nonneg q hq hq1 _ (M.pB_nonneg y l) b
  pA_sum x l := thinResponse_sum q _ (M.pA_sum x l)
  pB_sum y l := thinResponse_sum q _ (M.pB_sum y l)

lemma response_integrable {Ω O : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [Fintype O] (v : Ω → O → ℝ)
    (hm : ∀ a, Measurable fun l => v l a) (hn : ∀ l a, 0 ≤ v l a)
    (hs : ∀ l, ∑ a, v l a = 1) (a : O) : Integrable (fun l => v l a) μ := by
  apply (integrable_const (1 : ℝ)).mono' (hm a).aestronglyMeasurable
  filter_upwards [] with l
  rw [Real.norm_eq_abs, abs_of_nonneg (hn l a)]
  rw [← hs l]
  exact Finset.single_le_sum (fun b _ => hn l b) (Finset.mem_univ _)

lemma product_integrable {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
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

lemma integral_responseA {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (M : LHVModel OA OB MA MB) (a : OA) (x : Fin MA) (y : Fin MB) :
    (∫ l, M.pA x l a ∂M.μ) = ∑ b, M.behaviour a b x y := by
  unfold LHVModel.behaviour
  rw [← integral_finsetSum _ (fun b _ => product_integrable M a b x y)]
  apply integral_congr_ae
  filter_upwards [] with l
  rw [← Finset.mul_sum, M.pB_sum, mul_one]

lemma integral_responseB {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (M : LHVModel OA OB MA MB) (b : OB) (x : Fin MA) (y : Fin MB) :
    (∫ l, M.pB y l b ∂M.μ) = ∑ a, M.behaviour a b x y := by
  unfold LHVModel.behaviour
  rw [← integral_finsetSum _ (fun a _ => product_integrable M a b x y)]
  apply integral_congr_ae
  filter_upwards [] with l
  rw [← Finset.sum_mul, M.pA_sum, one_mul]

lemma thinModel_behaviour {OA OB : Type} [Fintype OA] [Fintype OB] {MA MB : ℕ}
    (M : LHVModel (Option OA) (Option OB) MA MB) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (a : Option OA) (b : Option OB) (x : Fin MA) (y : Fin MB) :
    (thinModel M q hq hq1).behaviour a b x y =
      q ^ 2 * M.behaviour a b x y +
      (q * b.elim (1 - q) (fun _ => 0)) * (∑ b', M.behaviour a b' x y) +
      (q * a.elim (1 - q) (fun _ => 0)) * (∑ a', M.behaviour a' b x y) +
      a.elim (1 - q) (fun _ => 0) * b.elim (1 - q) (fun _ => 0) := by
  have hA := response_integrable (μ := M.μ) (M.pA x) (M.measurable_pA x) (M.pA_nonneg x) (M.pA_sum x) a
  have hB := response_integrable (μ := M.μ) (M.pB y) (M.measurable_pB y) (M.pB_nonneg y) (M.pB_sum y) b
  have hAB := product_integrable M a b x y
  rw [← integral_responseA M a x y, ← integral_responseB M b x y]
  change (∫ l, thinResponse q (M.pA x l) a * thinResponse q (M.pB y l) b ∂M.μ) = _
  have hi : (fun l => thinResponse q (M.pA x l) a * thinResponse q (M.pB y l) b) =
      fun l => q ^ 2 * (M.pA x l a * M.pB y l b) +
        (q * b.elim (1 - q) (fun _ => 0)) * M.pA x l a +
        (q * a.elim (1 - q) (fun _ => 0)) * M.pB y l b +
        a.elim (1 - q) (fun _ => 0) * b.elim (1 - q) (fun _ => 0) := by
    funext l
    unfold thinResponse
    ring
  have hiA := hA.const_mul (q * b.elim (1 - q) (fun _ => 0))
  have hiB := hB.const_mul (q * a.elim (1 - q) (fun _ => 0))
  have hiAB := hAB.const_mul (q ^ 2)
  have hiC := integrable_const (μ := M.μ)
    (a.elim (1 - q) (fun _ => 0) * b.elim (1 - q) (fun _ => 0))
  have hi12 : Integrable (fun l => q ^ 2 * (M.pA x l a * M.pB y l b) +
      (q * b.elim (1 - q) (fun _ => 0)) * M.pA x l a) M.μ := by
    exact hiAB.fun_add hiA
  have hi123 : Integrable (fun l => q ^ 2 * (M.pA x l a * M.pB y l b) +
      (q * b.elim (1 - q) (fun _ => 0)) * M.pA x l a +
      (q * a.elim (1 - q) (fun _ => 0)) * M.pB y l b) M.μ := by
    exact hi12.fun_add hiB
  rw [hi, integral_add hi123 hiC, integral_add hi12 hiB, integral_add hiAB hiA]
  simp [integral_const_mul, integral_const, LHVModel.behaviour]

lemma sum_withEff_right {KA KB MA MB : ℕ} (p : Fin KA → Fin KB → Fin MA → Fin MB → ℝ)
    (hp : IsBehaviour p) (η : ℝ) (a : Option (Fin KA)) (x : Fin MA) (y : Fin MB) :
    (∑ b, withEff p η a b x y) =
      a.elim (1 - η) (fun a => η * ∑ b, p a b x y) := by
  cases a with
  | none =>
    simp only [Fintype.sum_option, withEff, Option.elim_none, ← Finset.mul_sum]
    rw [Finset.sum_comm, hp.2 x y]
    ring
  | some a =>
    simp only [Fintype.sum_option, withEff, Option.elim_some, ← Finset.mul_sum]
    ring

lemma sum_withEff_left {KA KB MA MB : ℕ} (p : Fin KA → Fin KB → Fin MA → Fin MB → ℝ)
    (hp : IsBehaviour p) (η : ℝ) (b : Option (Fin KB)) (x : Fin MA) (y : Fin MB) :
    (∑ a, withEff p η a b x y) =
      b.elim (1 - η) (fun b => η * ∑ a, p a b x y) := by
  cases b with
  | none =>
    simp only [Fintype.sum_option, withEff, Option.elim_none, ← Finset.mul_sum]
    rw [hp.2 x y]
    ring
  | some b =>
    simp only [Fintype.sum_option, withEff, Option.elim_some, ← Finset.mul_sum]
    ring

lemma thin_withEff {KA KB MA MB : ℕ} (p : Fin KA → Fin KB → Fin MA → Fin MB → ℝ)
    (hp : IsBehaviour p) (q η : ℝ) (a : Option (Fin KA)) (b : Option (Fin KB))
    (x : Fin MA) (y : Fin MB) :
      q ^ 2 * withEff p η a b x y +
      (q * b.elim (1 - q) (fun _ => 0)) * (∑ b', withEff p η a b' x y) +
      (q * a.elim (1 - q) (fun _ => 0)) * (∑ a', withEff p η a' b x y) +
      a.elim (1 - q) (fun _ => 0) * b.elim (1 - q) (fun _ => 0) =
        withEff p (q * η) a b x y := by
  rw [sum_withEff_right p hp, sum_withEff_left p hp]
  cases a <;> cases b <;> simp only [withEff, Option.elim_none, Option.elim_some] <;> ring

end BellDetEff.TwoParty.ThinningProof

open BellDetEff.TwoParty BellDetEff.TwoParty.ThinningProof

theorem solution {KA KB MA MB : ℕ} (p : Fin KA → Fin KB → Fin MA → Fin MB → ℝ)
    (hp : IsBehaviour p) (_hns : NoSignaling p) (η₁ η₂ : ℝ) (h₁ : 0 ≤ η₁) (h₁₂ : η₁ < η₂)
    (_h₂ : η₂ ≤ 1) (hsim : LHVSimulable (withEff p η₂)) :
    LHVSimulable (withEff p η₁) := by
  have hη₂ : 0 < η₂ := lt_of_le_of_lt h₁ h₁₂
  let q := η₁ / η₂
  have hq : 0 ≤ q := div_nonneg h₁ hη₂.le
  have hq1 : q ≤ 1 := (div_le_one hη₂).mpr h₁₂.le
  have hqη : q * η₂ = η₁ := div_mul_cancel₀ _ hη₂.ne'
  obtain ⟨M, hM⟩ := hsim
  refine ⟨thinModel M q hq hq1, ?_⟩
  intro a b x y
  rw [thinModel_behaviour]
  simp_rw [← hM]
  rw [thin_withEff p hp, hqη]

