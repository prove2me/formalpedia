-- Prove2me | solution 1 for ForkJoinCtrl.Tracking.lemma_1_part_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T11:32:19.260988+00:00
-- url     : https://prove2.me/submissions/2fb45be0-06ec-4e2a-b216-4832d9449a09

import Mathlib
import Definitions.Def_ForkJoinCtrl_Tracking_LP

open ForkJoinCtrl.Tracking

namespace FJL12

theorem obj_nonneg (N : Network) (b : LPParam N) (x : LPVar N) (hf : LPFeasible N b x) :
    0 ≤ LPObj N x := by
  unfold LPObj
  apply Finset.sum_nonneg
  intro j _
  obtain ⟨i, hi⟩ := N.exists_server j
  have h1 := hf.2.1 i j hi
  have h2 := hf.2.2.2.1 i j hi
  exact mul_nonneg (N.h_nonneg j) (by linarith)

theorem feas_nonempty (N : Network) (b : LPParam N) (hb : b.Nonneg) :
    ∃ x, LPFeasible N b x := by
  classical
  let q : Fin N.I → Fin N.J → ℝ := fun i j =>
    if N.P i j = true then N.mu i j * b.2 i / ((N.Ji i).card : ℝ) else 0
  refine ⟨⟨fun j => ∑ k, b.1 k + ∑ i, q i j, q⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    have hq : ∀ i, 0 ≤ q i (N.own k) := by
      intro i; simp only [q]; split_ifs with h
      · exact div_nonneg (mul_nonneg (N.mu_pos _ _ h).le (hb.2 i)) (Nat.cast_nonneg _)
      · exact le_refl _
    have h1 : b.1 k ≤ ∑ k, b.1 k :=
      Finset.single_le_sum (fun k _ => hb.1 k) (Finset.mem_univ k)
    have h2 : 0 ≤ ∑ i, q i (N.own k) := Finset.sum_nonneg (fun i _ => hq i)
    show b.1 k ≤ ∑ k, b.1 k + ∑ i, q i (N.own k)
    linarith
  · intro i j hij
    have hq : ∀ i, 0 ≤ q i j := by
      intro i; simp only [q]; split_ifs with h
      · exact div_nonneg (mul_nonneg (N.mu_pos _ _ h).le (hb.2 i)) (Nat.cast_nonneg _)
      · exact le_refl _
    have h1 : q i j ≤ ∑ i, q i j := Finset.single_le_sum (fun i _ => hq i) (Finset.mem_univ i)
    have h2 : 0 ≤ ∑ k, b.1 k := Finset.sum_nonneg (fun k _ => hb.1 k)
    show 0 ≤ ∑ k, b.1 k + ∑ i, q i j - q i j
    linarith
  · intro i
    have hc : (0 : ℝ) < ((N.Ji i).card : ℝ) := by
      have := N.two_le_card_types i
      have : 2 ≤ (N.Ji i).card := this
      exact_mod_cast (by omega : 0 < (N.Ji i).card)
    have : ∀ j ∈ N.Ji i, q i j / N.mu i j = b.2 i / ((N.Ji i).card : ℝ) := by
      intro j hj
      have hij : N.P i j = true := by simpa [Network.Ji] using hj
      have hmu := N.mu_pos i j hij
      simp only [q, hij, if_true]
      field_simp
    show ∑ j ∈ N.Ji i, q i j / N.mu i j = b.2 i
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]
    field_simp
  · intro i j hij
    show 0 ≤ q i j
    simp only [q, hij, if_true]
    exact div_nonneg (mul_nonneg (N.mu_pos _ _ hij).le (hb.2 i)) (Nat.cast_nonneg _)
  · intro i j hij
    show q i j = 0
    simp [q, hij]

/-- The perturbation step: from a feasible point at `b2` build a feasible point at `b1`. -/
theorem perturb (N : Network) (b1 b2 : LPParam N) (hb1 : b1.Nonneg) (hb2 : b2.Nonneg)
    (x : LPVar N) (hx : LPFeasible N b2 x) :
    ∃ x' : LPVar N, LPFeasible N b1 x' ∧
      LPObj N x' ≤ LPObj N x +
        ((1 + ∑ i, ∑ j, |N.mu i j|) * ∑ j, N.h j) * ‖b1 - b2‖ := by
  classical
  set d := ‖b1 - b2‖ with hd
  set D := 1 + ∑ i, ∑ j, |N.mu i j| with hD
  have hd0 : 0 ≤ d := norm_nonneg _
  have hk : ∀ k, |b1.1 k - b2.1 k| ≤ d := by
    intro k
    have h1 : ‖(b1 - b2).1 k‖ ≤ ‖(b1 - b2).1‖ := norm_le_pi_norm _ k
    have h2 : ‖(b1 - b2).1‖ ≤ ‖b1 - b2‖ := norm_fst_le _
    have : ‖(b1 - b2).1 k‖ = |b1.1 k - b2.1 k| := by simp [Real.norm_eq_abs]
    linarith
  have hw : ∀ i, |b1.2 i - b2.2 i| ≤ d := by
    intro i
    have h1 : ‖(b1 - b2).2 i‖ ≤ ‖(b1 - b2).2‖ := norm_le_pi_norm _ i
    have h2 : ‖(b1 - b2).2‖ ≤ ‖b1 - b2‖ := norm_snd_le _
    have : ‖(b1 - b2).2 i‖ = |b1.2 i - b2.2 i| := by simp [Real.norm_eq_abs]
    linarith
  have hmuD : ∀ i j, N.mu i j ≤ D := by
    intro i j
    have h1 : |N.mu i j| ≤ ∑ j, |N.mu i j| :=
      Finset.single_le_sum (f := fun j => |N.mu i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    have h2 : ∑ j, |N.mu i j| ≤ ∑ i, ∑ j, |N.mu i j| :=
      Finset.single_le_sum (f := fun i => ∑ j, |N.mu i j|)
        (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)) (Finset.mem_univ i)
    have := le_abs_self (N.mu i j)
    linarith
  let q' : Fin N.I → Fin N.J → ℝ := fun i j =>
    if N.P i j = true then
      (if b2.2 i ≤ b1.2 i then x.q i j + N.mu i j * (b1.2 i - b2.2 i) / ((N.Ji i).card : ℝ)
       else x.q i j * (b1.2 i / b2.2 i))
    else 0
  have hcard : ∀ i, (1 : ℝ) ≤ ((N.Ji i).card : ℝ) := by
    intro i
    have : 2 ≤ (N.Ji i).card := N.two_le_card_types i
    exact_mod_cast (by omega : 1 ≤ (N.Ji i).card)
  have hq'bd : ∀ i j, N.P i j = true → 0 ≤ q' i j ∧ q' i j ≤ x.q i j + D * d := by
    intro i j hij
    have hq0 := hx.2.2.2.1 i j hij
    have hmu := N.mu_pos i j hij
    simp only [q', hij, if_true]
    split_ifs with hle
    · have hc := hcard i
      have hδ : b1.2 i - b2.2 i ≤ d := (abs_le.1 (hw i)).2
      have e1 : N.mu i j * (b1.2 i - b2.2 i) / ((N.Ji i).card : ℝ) ≤ N.mu i j * (b1.2 i - b2.2 i) :=
        div_le_self (mul_nonneg hmu.le (by linarith)) hc
      have e2 : N.mu i j * (b1.2 i - b2.2 i) ≤ D * d :=
        mul_le_mul (hmuD i j) hδ (by linarith) (by linarith [hmuD i j])
      have e3 : 0 ≤ N.mu i j * (b1.2 i - b2.2 i) / ((N.Ji i).card : ℝ) :=
        div_nonneg (mul_nonneg hmu.le (by linarith)) (by linarith)
      constructor <;> nlinarith
    · push Not at hle
      have hw1 := hb1.2 i
      have hpos : 0 < b2.2 i := lt_of_le_of_lt hw1 hle
      have r0 : 0 ≤ b1.2 i / b2.2 i := div_nonneg hw1 hpos.le
      have r1 : b1.2 i / b2.2 i ≤ 1 := (div_le_one hpos).2 hle.le
      have hDd : 0 ≤ D * d := mul_nonneg (by linarith [hmuD i j]) hd0
      constructor
      · exact mul_nonneg hq0 r0
      · nlinarith
  refine ⟨⟨fun j => x.y j + D * d, q'⟩, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro k
    have h1 := hx.1 k
    have h2 := (abs_le.1 (hk k)).2
    have hD1 : 1 ≤ D := by
      have : 0 ≤ ∑ i, ∑ j, |N.mu i j| :=
        Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
      linarith
    show b1.1 k ≤ x.y (N.own k) + D * d
    nlinarith
  · intro i j hij
    have h1 := hx.2.1 i j hij
    have h2 := (hq'bd i j hij).2
    show 0 ≤ x.y j + D * d - q' i j
    linarith
  · intro i
    show ∑ j ∈ N.Ji i, q' i j / N.mu i j = b1.2 i
    have hsum := hx.2.2.1 i
    by_cases hle : b2.2 i ≤ b1.2 i
    · have hc : (0 : ℝ) < ((N.Ji i).card : ℝ) := by linarith [hcard i]
      have : ∀ j ∈ N.Ji i, q' i j / N.mu i j =
          x.q i j / N.mu i j + (b1.2 i - b2.2 i) / ((N.Ji i).card : ℝ) := by
        intro j hj
        have hij : N.P i j = true := by simpa [Network.Ji] using hj
        have hmu := N.mu_pos i j hij
        simp only [q', hij, hle, if_true]
        field_simp
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, hsum, Finset.sum_const,
        nsmul_eq_mul]
      field_simp
      ring
    · push Not at hle
      have hpos : 0 < b2.2 i := lt_of_le_of_lt (hb1.2 i) hle
      have : ∀ j ∈ N.Ji i, q' i j / N.mu i j = (b1.2 i / b2.2 i) * (x.q i j / N.mu i j) := by
        intro j hj
        have hij : N.P i j = true := by simpa [Network.Ji] using hj
        simp only [q', hij, if_true, not_le.2 hle, if_false]
        ring
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hsum]
      field_simp
  · intro i j hij
    exact (hq'bd i j hij).1
  · intro i j hij
    show q' i j = 0
    simp [q', hij]
  · show ∑ j, N.h j * (x.y j + D * d) ≤ ∑ j, N.h j * x.y j + (D * ∑ j, N.h j) * d
    have : ∑ j, N.h j * (x.y j + D * d) = ∑ j, N.h j * x.y j + (D * ∑ j, N.h j) * d := by
      rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [this]

theorem z_le (N : Network) (b1 b2 : LPParam N) (hb1 : b1.Nonneg) (hb2 : b2.Nonneg) :
    z N b1 ≤ z N b2 + ((1 + ∑ i, ∑ j, |N.mu i j|) * ∑ j, N.h j) * ‖b1 - b2‖ := by
  have hbdd : BddBelow (LPObj N '' {x | LPFeasible N b1 x}) := by
    refine ⟨0, ?_⟩
    rintro v ⟨x, hx, rfl⟩
    exact obj_nonneg N b1 x hx
  obtain ⟨x0, hx0⟩ := feas_nonempty N b2 hb2
  have hne : (LPObj N '' {x | LPFeasible N b2 x}).Nonempty := ⟨_, x0, hx0, rfl⟩
  have : z N b1 - ((1 + ∑ i, ∑ j, |N.mu i j|) * ∑ j, N.h j) * ‖b1 - b2‖ ≤ z N b2 := by
    apply le_csInf hne
    rintro v ⟨x, hx, rfl⟩
    obtain ⟨x', hx', hle⟩ := perturb N b1 b2 hb1 hb2 x hx
    have : z N b1 ≤ LPObj N x' := csInf_le hbdd ⟨x', hx', rfl⟩
    linarith
  linarith

end FJL12

theorem solution (N : Network) :
    (∀ b : LPParam N, b.Nonneg → 0 ≤ z N b) ∧
    ∃ C1 : ℝ, 0 < C1 ∧ ∀ b1 b2 : LPParam N, b1.Nonneg → b2.Nonneg →
      |z N b1 - z N b2| ≤ C1 * ‖b1 - b2‖ := by
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨x0, hx0⟩ := FJL12.feas_nonempty N b hb
    unfold z
    have hne : (LPObj N '' {x | LPFeasible N b x}).Nonempty := ⟨LPObj N x0, x0, hx0, rfl⟩
    apply le_csInf hne
    rintro v ⟨x, hx, rfl⟩
    exact FJL12.obj_nonneg N b x hx
  · set C := (1 + ∑ i, ∑ j, |N.mu i j|) * ∑ j, N.h j
    have hC : 0 ≤ C := by
      apply mul_nonneg
      · have : 0 ≤ ∑ i, ∑ j, |N.mu i j| :=
          Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
        linarith
      · exact Finset.sum_nonneg (fun j _ => N.h_nonneg j)
    refine ⟨C + 1, by linarith, ?_⟩
    intro b1 b2 hb1 hb2
    have h1 := FJL12.z_le N b1 b2 hb1 hb2
    have h2 := FJL12.z_le N b2 b1 hb2 hb1
    rw [norm_sub_rev] at h2
    have hn : 0 ≤ ‖b1 - b2‖ := norm_nonneg _
    rw [abs_le]
    constructor <;> nlinarith
