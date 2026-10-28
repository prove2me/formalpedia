-- Prove2me | solution 2 for BudgetedAffine.NetworkGap.lemma_7_1
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T14:24:29.079877+00:00
-- url     : https://prove2.me/submissions/c092beb0-e6bf-41da-a828-7f64d0a81d7a

import Mathlib
import Definitions.Def_BudgetedAffine_NetworkGap_LotSizing
import Definitions.Def_BudgetedAffine_NetworkGap_Instance
import Theorems.Thm_BudgetedAffine_NetworkGap_adjustable_cost_zero
import Theorems.Thm_BudgetedAffine_NetworkGap_affine_solution

-- carved verbatim out of submission a7ea55f5-4439-4dd5-baac-dc0f83a6695c, lines 283-295

section
open BudgetedAffine.NetworkGap
open scoped BigOperators

private lemma in_left {k : ℕ} (y : Arc k → ℝ) (i : Fin k) :
    (lotSizingFamily k).inflow y (Sum.inl i) = 0 := by
  simp [LotSizing.inflow, lotSizingFamily]

private lemma out_right {k : ℕ} (y : Arc k → ℝ) (j : Fin k) :
    (lotSizingFamily k).outflow y (Sum.inr j) = 0 := by
  simp [LotSizing.outflow, lotSizingFamily]

private lemma in_right {k : ℕ} (y : Arc k → ℝ) (j : Fin k) :
    (lotSizingFamily k).inflow y (Sum.inr j) = ∑ i, y (i,j) := by
  classical
  simp [LotSizing.inflow, lotSizingFamily, Finset.sum_filter, Fintype.sum_prod_type]

private lemma out_left {k : ℕ} (y : Arc k → ℝ) (i : Fin k) :
    (lotSizingFamily k).outflow y (Sum.inl i) = ∑ j, y (i,j) := by
  classical
  simp [LotSizing.outflow, lotSizingFamily, Finset.sum_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  simp

private lemma cost_eq {k : ℕ} (x : Node k → ℝ) (y : Arc k → ℝ) :
    (lotSizingFamily k).cost x y = ∑ j, x (Sum.inr j) := by
  simp [LotSizing.cost, lotSizingFamily, Fintype.sum_sum_type]

private lemma feasible_iff {k : ℕ} (x : Node k → ℝ) (y : (Node k → ℝ) → Arc k → ℝ) :
    (lotSizingFamily k).Feasible x y ↔
      (∀ v, 0 ≤ x v ∧ x v ≤ 1) ∧
      ∀ h ∈ budgetSet k, (∀ i j, 0 ≤ y h (i,j)) ∧
        (∀ i, h (Sum.inl i) + ∑ j, y h (i,j) ≤ x (Sum.inl i)) ∧
        (∀ j, h (Sum.inr j) ≤ x (Sum.inr j) + ∑ i, y h (i,j)) := by
  constructor
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    intro h hh
    obtain ⟨hn, hf⟩ := hy h hh
    refine ⟨fun i j => hn (i,j), ?_, ?_⟩
    · intro i
      have hi := hf (Sum.inl i)
      rw [in_left, out_left] at hi
      linarith
    · intro j
      have hj := hf (Sum.inr j)
      simpa only [in_right, out_right, sub_zero] using hj
  · rintro ⟨hx, hy⟩
    refine ⟨hx, ?_⟩
    intro h hh
    obtain ⟨hn, hl, hr⟩ := hy h hh
    refine ⟨fun a => hn a.1 a.2, ?_⟩
    intro v
    cases v with
    | inl i => rw [in_left, out_left]; have hi := hl i; linarith
    | inr j => simpa only [in_right, out_right, sub_zero] using hr j

private def basis {k : ℕ} (v : Node k) : Node k → ℝ := fun w => if w = v then 1 else 0

private lemma basis_mem {k : ℕ} (hk : 1 ≤ k) (v : Node k) : basis v ∈ budgetSet k := by
  classical
  constructor
  · intro w; dsimp [basis]; split_ifs <;> norm_num
  · simp [basis]; exact_mod_cast hk

private lemma basis_pair_mem {k : ℕ} (hk : 2 ≤ k) (u v : Node k) (huv : u ≠ v) :
    basis u + basis v ∈ budgetSet k := by
  classical
  constructor
  · intro w
    simp only [Pi.add_apply, basis]
    split_ifs <;> try norm_num
    exact False.elim (huv (by aesop))
  · simp [Pi.add_apply, Finset.sum_add_distrib, basis]
    exact_mod_cast hk

private lemma affine_basis {k : ℕ} (P : Matrix (Arc k) (Node k) ℝ) (q : Arc k → ℝ)
    (v : Node k) (a : Arc k) : LotSizing.affinePolicy P q (basis v) a = P a v + q a := by
  classical
  simp [LotSizing.affinePolicy, Matrix.mulVec, dotProduct, basis]

private lemma affine_pair {k : ℕ} (P : Matrix (Arc k) (Node k) ℝ) (q : Arc k → ℝ)
    (u v : Node k) (a : Arc k) :
    LotSizing.affinePolicy P q (basis u + basis v) a = P a u + P a v + q a := by
  classical
  simp [LotSizing.affinePolicy, Matrix.mulVec, dotProduct, Pi.add_apply, mul_add,
    Finset.sum_add_distrib, basis]

private lemma row_zero {k : ℕ} (x : Node k → ℝ) (y : (Node k → ℝ) → Arc k → ℝ)
    (hf : (lotSizingFamily k).Feasible x y) (h : Node k → ℝ) (hh : h ∈ budgetSet k)
    (i : Fin k) (hi : h (Sum.inl i) = 1) : x (Sum.inl i) = 1 ∧ ∀ j, y h (i,j) = 0 := by
  obtain ⟨hx, hf'⟩ := (feasible_iff x y).1 hf
  obtain ⟨hn, hl, hr⟩ := hf' h hh
  have hs : 0 ≤ ∑ j, y h (i,j) := Finset.sum_nonneg (fun j _ => hn i j)
  have hc := hl i
  rw [hi] at hc
  have hxi := (hx (Sum.inl i)).2
  refine ⟨by linarith, ?_⟩
  intro j
  have hj : y h (i,j) ≤ ∑ j, y h (i,j) :=
    Finset.single_le_sum (fun j _ => hn i j) (Finset.mem_univ j)
  linarith [hn i j]

private lemma coefficients (k : ℕ) (hk : 2 ≤ k) (x : Node k → ℝ)
    (P : Matrix (Arc k) (Node k) ℝ) (q : Arc k → ℝ)
    (hf : (lotSizingFamily k).Feasible x (LotSizing.affinePolicy P q)) :
    (∀ i, x (Sum.inl i) = 1) ∧
      ∀ i j, P (i,j) (Sum.inl i) + q (i,j) = 0 ∧ ∀ v, v ≠ Sum.inl i → P (i,j) v = 0 := by
  have hrow (i : Fin k) := row_zero x (LotSizing.affinePolicy P q) hf
    (basis (Sum.inl i)) (basis_mem (by omega) _) i (by simp [basis])
  refine ⟨fun i => (hrow i).1, ?_⟩
  intro i j
  have h0 := (hrow i).2 j
  rw [affine_basis] at h0
  refine ⟨h0, ?_⟩
  intro v hv
  have h1 := (row_zero x (LotSizing.affinePolicy P q) hf
    (basis (Sum.inl i) + basis v) (basis_pair_mem hk _ _ hv.symm) i
    (by simp [basis, Ne.symm hv])).2 j
  rw [affine_pair] at h1
  linarith

private lemma policy_form {k : ℕ} (hk : 2 ≤ k) (x : Node k → ℝ)
    (P : Matrix (Arc k) (Node k) ℝ) (q : Arc k → ℝ)
    (hf : (lotSizingFamily k).Feasible x (LotSizing.affinePolicy P q))
    (h : Node k → ℝ) (i j : Fin k) :
    LotSizing.affinePolicy P q h (i,j) = q (i,j) * (1 - h (Sum.inl i)) := by
  classical
  obtain ⟨hz, he⟩ := (coefficients k hk x P q hf).2 i j
  change (∑ v, P (i,j) v * h v) + q (i,j) = _
  rw [Finset.sum_eq_single (Sum.inl i)]
  · have hz' : P (i,j) (Sum.inl i) = -q (i,j) := by linarith
    rw [hz']
    ring
  · intro b hb hbi
    rw [he b hbi, zero_mul]
  · simp

private def coverDemand {k : ℕ} (i j : Fin k) : Node k → ℝ :=
  Sum.elim (fun l => 1 - if l = i then 1 else 0) (fun l => if l = j then 1 else 0)

private lemma cover_mem {k : ℕ} (i j : Fin k) : coverDemand i j ∈ budgetSet k := by
  classical
  constructor
  · intro v
    cases v with
    | inl l => simp only [coverDemand, Sum.elim_inl]; split_ifs <;> norm_num
    | inr l => simp only [coverDemand, Sum.elim_inr]; split_ifs <;> norm_num
  · simp [coverDemand, Fintype.sum_sum_type, Finset.sum_sub_distrib]

private lemma cover_bound (k : ℕ) (hk : 2 ≤ k) (x : Node k → ℝ)
    (P : Matrix (Arc k) (Node k) ℝ) (q : Arc k → ℝ)
    (hf : (lotSizingFamily k).Feasible x (LotSizing.affinePolicy P q)) :
    ∀ l j : Fin k, 1 ≤ x (Sum.inr j) + q (l,j) := by
  classical
  intro l j
  have hc := ((feasible_iff _ _).1 hf).2 (coverDemand l j) (cover_mem l j)
  have hr := hc.2.2 j
  simp_rw [policy_form hk x P q hf] at hr
  simpa [coverDemand, mul_ite] using hr

private lemma zero_mem (k : ℕ) : (0 : Node k → ℝ) ∈ budgetSet k := by
  constructor
  · intro v; norm_num
  · simp

private lemma lower_inventory (k : ℕ) (x : Node k → ℝ)
    (P : Matrix (Arc k) (Node k) ℝ) (q : Arc k → ℝ)
    (hf : (lotSizingFamily k).Feasible x (LotSizing.affinePolicy P q)) :
    (k : ℝ) - 1 ≤ ∑ j, x (Sum.inr j) := by
  have hn : 0 ≤ ∑ j, x (Sum.inr j) :=
    Finset.sum_nonneg (fun j _ => (hf.1 (Sum.inr j)).1)
  by_cases hk : 2 ≤ k
  · let l : Fin k := ⟨0, by omega⟩
    have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => cover_bound k hk x P q hf l j)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.sum_add_distrib] at hs
    have hc := (((feasible_iff _ _).1 hf).2 0 (zero_mem k)).2.1 l
    simp only [policy_form hk x P q hf, Pi.zero_apply, sub_zero, mul_one, zero_add] at hc
    have hx : x (Sum.inl l) ≤ 1 := (hf.1 (Sum.inl l)).2
    linarith
  · have hk' : (k : ℝ) ≤ 1 := by exact_mod_cast (show k ≤ 1 by omega)
    linarith

private lemma lower_values (k : ℕ) : (k : ℝ) - 1 ∈ lowerBounds (lotSizingFamily k).affineValues := by
  rintro t ⟨x, P, q, hf, ht⟩
  have hb := lower_inventory k x P q hf
  have hz := ht 0 (zero_mem k)
  rw [cost_eq] at hz
  exact hb.trans hz

private lemma adjustable_nonneg (k : ℕ) : (0 : ℝ) ∈ lowerBounds (lotSizingFamily k).adjustableValues := by
  rintro t ⟨x, y, hf, ht⟩
  have hn : 0 ≤ ∑ j, x (Sum.inr j) := Finset.sum_nonneg (fun j _ => (hf.1 (Sum.inr j)).1)
  have hz := ht 0 (zero_mem k)
  rw [cost_eq] at hz
  exact hn.trans hz

theorem solution (k : ℕ) (hk : 1 ≤ k) :
    IsLeast (lotSizingFamily k).adjustableValues 0 ∧
      IsLeast (lotSizingFamily k).affineValues ((k : ℝ) - 1) := by
  constructor
  · refine ⟨?_, adjustable_nonneg k⟩
    obtain ⟨y, hf, hc⟩ := BudgetedAffine.NetworkGap.adjustable_cost_zero k
    exact ⟨Sum.elim (fun _ => 1) (fun _ => 0), y, hf, fun h hh => (hc h hh).le⟩
  · refine ⟨?_, lower_values k⟩
    obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k-1, by omega⟩
    refine ⟨ubX n, ubP n, ubQ n, (BudgetedAffine.NetworkGap.affine_solution n).1, ?_⟩
    intro h hh
    rw [(BudgetedAffine.NetworkGap.affine_solution n).2 h hh]
    norm_num

end
