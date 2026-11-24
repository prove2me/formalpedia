-- Prove2me | solution 1 for CellProbeTree.Matching.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-24T00:06:57.857826+00:00
-- url     : https://prove2.me/submissions/b78e59c3-a949-4f40-89c1-aeda9d1e6ea9

import Mathlib
import Definitions.Def_CellProbeTree_Matching_LRBlock

set_option autoImplicit false

open CellProbeTree.Matching

open PowerSeries

/-- Membership in `forestsOfSize`: total node count equals `b`. -/
private lemma mem_fos {u b : ℕ} {f : Fin u → BinaryTree Unit} :
    f ∈ forestsOfSize u b ↔ ∑ i, (f i).numNodes = b := by
  unfold forestsOfSize
  simp only [Finset.mem_biUnion, Fintype.mem_piFinset, BinaryTree.mem_treesOfNumNodesEq,
    Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨c, hc, hf⟩
    rw [← hc]
    exact Finset.sum_congr rfl (fun i _ => hf i)
  · intro h
    exact ⟨fun i => (f i).numNodes, h, fun i => rfl⟩

/-- Splitting off the first tree. -/
private lemma fos_succ (u b : ℕ) : forestsOfSize (u + 1) b =
    (Finset.HasAntidiagonal.antidiagonal b).biUnion (fun p =>
      (BinaryTree.treesOfNumNodesEq p.1 ×ˢ forestsOfSize u p.2).image
        (fun x => (Fin.cons x.1 x.2 : Fin (u + 1) → BinaryTree Unit))) := by
  ext f
  simp only [mem_fos, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product,
    Finset.HasAntidiagonal.mem_antidiagonal, BinaryTree.mem_treesOfNumNodesEq, Fin.sum_univ_succ, Prod.exists]
  constructor
  · intro h
    exact ⟨(f 0).numNodes, ∑ i : Fin u, (f i.succ).numNodes, h, f 0, Fin.tail f, ⟨rfl, rfl⟩,
      Fin.cons_self_tail f⟩
  · rintro ⟨a, c, hac, t, g, ⟨ht, hg⟩, rfl⟩
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [ht, hg, hac]

private lemma fc_succ (u b : ℕ) : forestCount (u + 1) b =
    ∑ p ∈ Finset.HasAntidiagonal.antidiagonal b, catalan p.1 * forestCount u p.2 := by
  unfold forestCount
  rw [fos_succ, Finset.card_biUnion]
  · refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.card_image_of_injective, Finset.card_product,
      BinaryTree.treesOfNumNodesEq_card_eq_catalan]
    intro x y hxy
    obtain ⟨h1, h2⟩ := Fin.cons_injective2 hxy
    exact Prod.ext h1 h2
  · intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro f hf1 hf2
    simp only [Finset.mem_image, Finset.mem_product, BinaryTree.mem_treesOfNumNodesEq,
      mem_fos] at hf1 hf2
    obtain ⟨x, ⟨hx1, hx2⟩, rfl⟩ := hf1
    obtain ⟨y, ⟨hy1, hy2⟩, hxy⟩ := hf2
    obtain ⟨h1, h2⟩ := Fin.cons_injective2 hxy
    rw [Finset.mem_coe, Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
    apply hpq
    have e1 : p.1 = q.1 := by rw [← hx1, ← hy1, h1]
    exact Prod.ext e1 (by omega)

private lemma fc_zero (b : ℕ) : forestCount 0 b = if b = 0 then 1 else 0 := by
  cases b with
  | zero =>
    simp [forestCount, forestsOfSize, Finset.Nat.antidiagonalTuple_zero_zero]
  | succ b =>
    simp [forestCount, forestsOfSize, Finset.Nat.antidiagonalTuple_zero_succ]

private lemma fc_eq_coeff (u b : ℕ) : forestCount u b = coeff b (catalanSeries ^ u) := by
  induction u generalizing b with
  | zero => rw [fc_zero, pow_zero, coeff_one]
  | succ u ih =>
    rw [fc_succ, pow_succ', coeff_mul]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [ih, catalanSeries_coeff]

private lemma cs_pow_succ (u : ℕ) :
    catalanSeries ^ (u + 1) = catalanSeries ^ u + X * catalanSeries ^ (u + 2) := by
  have h : catalanSeries ^ (u + 1) = catalanSeries ^ u * (catalanSeries ^ 2 * X + 1) := by
    rw [catalanSeries_sq_mul_X_add_one, pow_succ]
  rw [h]
  ring

private lemma a_rec (u b : ℕ) : coeff (b + 1) (catalanSeries ^ (u + 1)) =
    coeff (b + 1) (catalanSeries ^ u) + coeff b (catalanSeries ^ (u + 2)) := by
  rw [cs_pow_succ, map_add, coeff_succ_X_mul]

/-- The ballot numbers, written without division. -/
private def H (u : ℕ) : ℕ → ℤ
  | 0 => 1
  | b + 1 => ((2 * b + u + 1).choose (b + 1) : ℤ) - ((2 * b + u + 1).choose b : ℤ)

private lemma a_eq_H (b : ℕ) : ∀ u : ℕ, ((coeff b (catalanSeries ^ u) : ℕ) : ℤ) = H u b := by
  induction b with
  | zero =>
    intro u
    simp [H, coeff_zero_eq_constantCoeff_apply]
  | succ b ihb =>
    intro u
    induction u with
    | zero =>
      have hs : (2 * b + 0 + 1).choose (b + 1) = (2 * b + 1).choose b := by
        simpa using Nat.choose_symm_half b
      simp [H, coeff_one, hs]
    | succ u ihu =>
      rw [a_rec, Nat.cast_add, ihu, ihb (u + 2)]
      cases b with
      | zero =>
        simp only [H]
        push_cast
        simp [Nat.choose_one_right]
      | succ b =>
        simp only [H]
        have e1 : 2 * (b + 1) + (u + 1) + 1 = (2 * b + u + 3) + 1 := by ring
        have e2 : 2 * (b + 1) + u + 1 = 2 * b + u + 3 := by ring
        have e3 : 2 * b + (u + 2) + 1 = 2 * b + u + 3 := by ring
        rw [e1, e2, e3, Nat.choose_succ_succ' (2 * b + u + 3) (b + 1),
          Nat.choose_succ_succ' (2 * b + u + 3) b]
        push_cast
        ring

private lemma H_closed (u b : ℕ) : ((2 * b + u : ℕ) : ℤ) * H u b = u * (2 * b + u).choose b := by
  cases b with
  | zero => simp [H]
  | succ b =>
    simp only [H]
    set n := 2 * b + u + 1 with hn
    have e : 2 * (b + 1) + u = n + 1 := by omega
    rw [e]
    have i1 := Nat.choose_succ_right_eq n b
    have i2 := Nat.add_one_mul_choose_eq n b
    have hnb : n - b = b + u + 1 := by omega
    rw [hnb] at i1
    have i1' : ((n.choose (b + 1) : ℕ) : ℤ) * (b + 1) = (n.choose b : ℤ) * (b + u + 1) := by
      exact_mod_cast i1
    have i2' : ((n + 1 : ℕ) : ℤ) * (n.choose b : ℤ) = ((n + 1).choose (b + 1) : ℤ) * (b + 1) := by
      exact_mod_cast i2
    have hb : ((b : ℤ) + 1) ≠ 0 := by positivity
    apply mul_right_cancel₀ hb
    push_cast at i2' ⊢
    linear_combination ((n : ℤ) + 1) * i1' + (u : ℤ) * i2'

theorem solution (u b : ℕ) (hu : 1 ≤ u) :
    (forestCount u b : ℝ) = (u : ℝ) / (2 * b + u) * (Nat.choose (2 * b + u) b : ℝ) := by
  have h1 : (forestCount u b : ℤ) = H u b := by rw [fc_eq_coeff]; exact a_eq_H b u
  have h2 : ((2 * b + u : ℕ) : ℤ) * (forestCount u b : ℤ) = u * (2 * b + u).choose b := by
    rw [h1]; exact H_closed u b
  have h3 : ((2 * b + u : ℕ) : ℝ) * (forestCount u b : ℝ) = u * (2 * b + u).choose b := by
    exact_mod_cast h2
  have hpos : (2 * (b : ℝ) + u) ≠ 0 := by
    have : (1 : ℝ) ≤ u := by exact_mod_cast hu
    positivity
  push_cast at h3
  field_simp
  linarith
