-- Prove2me | solution 1 for DavisGallegoTopaloglu2014.theorem_1_v0pos_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:27:14.076302+00:00
-- url     : https://prove2.me/submissions/1b04815f-f8be-440c-98c9-4ddb1ab4fb99

import Mathlib
import Definitions.Def_NestedLogitVariants_LP_Model

open NestedLogitVariants.LP

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (I : NestedLogitVariants.LP.Instance ι n)
    (hv0 : 0 < I.v0) (hvnp : ∀ i, 0 ≤ I.vnp i) (hv : ∀ i j, 0 ≤ I.v i j)
    (hr : ∀ i j, 0 ≤ I.r i j) (hγ0 : ∀ i, 0 ≤ I.γ i) (hγv : ∀ i, I.γ i = 0 → 0 < I.vnp i)
    (hanti : ∀ i, Antitone (I.r i))
    (A : ι → Set (Finset (Fin n))) (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I A xh yh)
    (Sh : ι → Finset (Fin n)) (hSmem : ∀ i, Sh i ∈ A i)
    (hSmax : ∀ i, ∀ S ∈ A i,
      nestWeight I i S * (R I i S - xh) ≤ nestWeight I i (Sh i) * (R I i (Sh i) - xh))
    (α β : ℝ) (hfeas : LP3Feasible I (α * xh) (β • yh)) :
    ∀ Sstar, IsOptimal I Sstar →
      revenue I Sstar ≤ α * revenue I Sh ∧ revenue I Sh ≤ revenue I Sstar := by
  intro Sstar hSopt
  have hV : ∀ i S, 0 ≤ V I i S := fun i S =>
    add_nonneg (hvnp i) (Finset.sum_nonneg fun j _ => hv i j)
  have hnw : ∀ i S, 0 ≤ nestWeight I i S := fun i S => Real.rpow_nonneg (hV i S) _
  have hR : ∀ i S, 0 ≤ R I i S := fun i S =>
    div_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hr i j) (hv i j)) (hV i S)
  have hD : ∀ S : ι → Finset (Fin n), 0 < I.v0 + ∑ i, nestWeight I i (S i) := fun S =>
    add_pos_of_pos_of_nonneg hv0 (Finset.sum_nonneg fun i _ => hnw i (S i))
  have hrev0 : ∀ S, 0 ≤ revenue I S := fun S =>
    div_nonneg (Finset.sum_nonneg fun i _ => mul_nonneg (hnw i _) (hR i _)) (hD S).le
  -- revenue ≤ z  ⇐  Σ nw (R - z) ≤ v0 z
  have hle_of : ∀ (S : ι → Finset (Fin n)) (z : ℝ),
      ∑ i, nestWeight I i (S i) * (R I i (S i) - z) ≤ I.v0 * z → revenue I S ≤ z := by
    intro S z h
    unfold revenue
    rw [div_le_iff₀ (hD S)]
    have : ∑ i, nestWeight I i (S i) * (R I i (S i) - z) =
        ∑ i, nestWeight I i (S i) * R I i (S i) - z * ∑ i, nestWeight I i (S i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this] at h; nlinarith
  have hge_of : ∀ (S : ι → Finset (Fin n)) (z : ℝ),
      I.v0 * z ≤ ∑ i, nestWeight I i (S i) * (R I i (S i) - z) → z ≤ revenue I S := by
    intro S z h
    unfold revenue
    rw [le_div_iff₀ (hD S)]
    have : ∑ i, nestWeight I i (S i) * (R I i (S i) - z) =
        ∑ i, nestWeight I i (S i) * R I i (S i) - z * ∑ i, nestWeight I i (S i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [this] at h; nlinarith
  -- upper bound on the optimum
  have hup : revenue I Sstar ≤ α * xh := by
    apply hle_of
    calc ∑ i, nestWeight I i (Sstar i) * (R I i (Sstar i) - α * xh)
        ≤ ∑ i, (β • yh) i := Finset.sum_le_sum fun i _ => hfeas.2 i (Sstar i)
      _ ≤ I.v0 * (α * xh) := hfeas.1
  -- xh ≥ 0
  obtain ⟨⟨hf1, hf2⟩, hmin⟩ := hopt
  have hx0 : 0 ≤ xh := by
    by_contra h
    push_neg at h
    have : 0 ≤ ∑ i, yh i := Finset.sum_nonneg fun i _ =>
      le_trans (mul_nonneg (hnw i _) (by linarith [hR i (Sh i)])) (hf2 i (Sh i) (hSmem i))
    nlinarith
  -- lower bound: xh ≤ revenue Sh
  have hlow : xh ≤ revenue I Sh := by
    apply hge_of
    by_contra hcon
    push_neg at hcon
    set g := I.v0 * xh - ∑ i, nestWeight I i (Sh i) * (R I i (Sh i) - xh)
    have hg : 0 < g := by simp only [g]; linarith
    let W : ι → ℝ := fun i => ∑ S : Finset (Fin n), nestWeight I i S
    have hW : ∀ i S, nestWeight I i S ≤ W i := fun i S =>
      Finset.single_le_sum (f := fun S => nestWeight I i S) (fun S _ => hnw i S) (Finset.mem_univ S)
    have hW0 : 0 ≤ ∑ i, W i := Finset.sum_nonneg fun i _ => (hnw i ∅).trans (hW i ∅)
    set δ := g / (∑ i, W i + I.v0 + 1)
    have hden : 0 < ∑ i, W i + I.v0 + 1 := by linarith
    have hδ : 0 < δ := div_pos hg hden
    have hδg : δ * (∑ i, W i + I.v0) ≤ g := by
      have : δ * (∑ i, W i + I.v0 + 1) = g := by simp only [δ]; field_simp
      nlinarith
    have hfeas' : LP4Feasible I A (xh - δ)
        (fun i => nestWeight I i (Sh i) * (R I i (Sh i) - xh) + W i * δ) := by
      constructor
      · rw [Finset.sum_add_distrib, ← Finset.sum_mul]
        simp only [g] at hδg; nlinarith
      · intro i S hS
        have h1 := hSmax i S hS
        have h2 := mul_le_mul_of_nonneg_right (hW i S) hδ.le
        nlinarith
    have := hmin _ _ hfeas'
    linarith
  have hopt' := hSopt Sh
  refine ⟨?_, hopt'⟩
  rcases le_or_gt 0 α with hα | hα
  · nlinarith
  · have h1 : revenue I Sstar ≤ 0 := hup.trans (by nlinarith)
    have h2 := hrev0 Sh
    have h3 : revenue I Sh = 0 := by linarith
    rw [h3]; linarith
