-- Prove2me | solution 1 for GGHRSW.ColoredMatrix.partial_eval_bound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:26:24.727458+00:00
-- url     : https://prove2.me/submissions/10bcd56e-1060-48d7-acbc-3be5cc886efe

import Mathlib
import Definitions.Def_GGHRSW_ColoredMatrix_Model

set_option autoImplicit false
open Classical
open Matrix GGHRSW.ColoredMatrix

section PartialEvalHelpers

variable {p : ℕ}

private theorem blockDiag_mul {r : ℕ} (d d' : Fin r → ZMod p)
    (B B' : Matrix (Fin 5) (Fin 5) (ZMod p)) :
    GGHRSW.ColoredMatrix.blockDiag d B * GGHRSW.ColoredMatrix.blockDiag d' B' =
      GGHRSW.ColoredMatrix.blockDiag (fun j => d j * d' j) (B * B') := by
  unfold GGHRSW.ColoredMatrix.blockDiag
  rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [Matrix.diagonal_mul_diagonal]

private theorem blockDiag_one {r : ℕ} :
    GGHRSW.ColoredMatrix.blockDiag (fun _ : Fin r => (1 : ZMod p))
      (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) = 1 := by
  unfold GGHRSW.ColoredMatrix.blockDiag
  rw [Matrix.reindex_apply]
  simp [Matrix.diagonal_one, Matrix.fromBlocks_one]

private theorem blockDiag_prod {r : ℕ} (n : ℕ) :
    ∀ (d : Fin n → Fin r → ZMod p) (B : Fin n → Matrix (Fin 5) (Fin 5) (ZMod p)),
      (List.ofFn fun i => GGHRSW.ColoredMatrix.blockDiag (d i) (B i)).prod =
        GGHRSW.ColoredMatrix.blockDiag (fun j => ∏ i, d i j) (List.ofFn B).prod := by
  induction n with
  | zero =>
    intro d B
    simp [blockDiag_one]
  | succ n ih =>
    intro d B
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, ih, blockDiag_mul]
    simp [Fin.prod_univ_succ]

private theorem bd_ll {r : ℕ} (d : Fin r → ZMod p) (B : Matrix (Fin 5) (Fin 5) (ZMod p))
    (k k' : Fin r) :
    GGHRSW.ColoredMatrix.blockDiag d B (Fin.castAdd 5 k) (Fin.castAdd 5 k') = diagonal d k k' := by
  simp [GGHRSW.ColoredMatrix.blockDiag, Matrix.reindex_apply]

private def stepVal {r : ℕ} (j₀ : Fin r) (A B : ZMod p)
    (d₀ : Bool → Fin r → ZMod p) : ZMod p :=
  d₀ false j₀ * A + d₀ true j₀ * B

private theorem stepVal_sub {r : ℕ} (j₀ : Fin r) (A B : ZMod p)
    (u v : Bool → Fin r → ZMod p) :
    stepVal j₀ A B (u - v) = stepVal j₀ A B u - stepVal j₀ A B v := by
  unfold stepVal
  simp only [Pi.sub_apply]
  ring

private theorem stepVal_add {r : ℕ} (j₀ : Fin r) (A B : ZMod p)
    (u v : Bool → Fin r → ZMod p) :
    stepVal j₀ A B (u + v) = stepVal j₀ A B u + stepVal j₀ A B v := by
  unfold stepVal
  simp only [Pi.add_apply]
  ring

private theorem card_stepVal_eq_zero_of_eq (p : ℕ) [Fact p.Prime] {r : ℕ} (j₀ : Fin r)
    (A B : ZMod p) (hAB : A ≠ 0 ∨ B ≠ 0) (a : ZMod p) :
    (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p => stepVal j₀ A B d₀ = a).card =
      (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p => stepVal j₀ A B d₀ = 0).card := by
  have hex : ∃ δ : Bool → Fin r → ZMod p, stepVal j₀ A B δ = a := by
    rcases hAB with hA | hB
    · refine ⟨fun b j => if b = false ∧ j = j₀ then a * A⁻¹ else 0, ?_⟩
      simp [stepVal, mul_assoc, inv_mul_cancel₀ hA]
    · refine ⟨fun b j => if b = true ∧ j = j₀ then a * B⁻¹ else 0, ?_⟩
      simp [stepVal, mul_assoc, inv_mul_cancel₀ hB]
  rcases hex with ⟨δ, hδ⟩
  refine Finset.card_bij (fun d₀ _ => d₀ - δ) ?_ ?_ ?_
  · intro d₀ hd₀
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd₀ ⊢
    rw [stepVal_sub, hd₀, hδ, sub_self]
  · intro u₁ _ u₂ _ h
    exact sub_left_inj.mp h
  · intro d₀ hd₀
    refine ⟨d₀ + δ, ?_, add_sub_cancel_right d₀ δ⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd₀ ⊢
    rw [stepVal_add, hd₀, hδ, zero_add]

private theorem card_stepVal_eq_zero (p : ℕ) [Fact p.Prime] {r : ℕ} (j₀ : Fin r)
    (A B : ZMod p) (hAB : A ≠ 0 ∨ B ≠ 0) :
    p * (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p => stepVal j₀ A B d₀ = 0).card =
      Fintype.card (Bool → Fin r → ZMod p) := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hsum : ∑ a : ZMod p,
      (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p => stepVal j₀ A B d₀ = a).card =
      Fintype.card (Bool → Fin r → ZMod p) := by
    simpa [Finset.card_univ] using (Finset.card_eq_sum_card_fiberwise
      (f := stepVal j₀ A B) (s := Finset.univ) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _)).symm
  have hconst : ∑ a : ZMod p,
      (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p => stepVal j₀ A B d₀ = a).card =
      p * (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p => stepVal j₀ A B d₀ = 0).card := by
    rw [Finset.sum_congr rfl fun a _ => card_stepVal_eq_zero_of_eq p j₀ A B hAB a]
    simp [Finset.sum_const, ZMod.card]
  linarith

private def polyEval {p r : ℕ} (j₀ : Fin r) (L : ℕ)
    (c : (Fin L → Bool) → ZMod p) (d : Fin L → Bool → Fin r → ZMod p) : ZMod p :=
  ∑ b : Fin L → Bool, c b * ∏ k : Fin L, d k (b k) j₀

private theorem polyEval_cons {p r : ℕ} (j₀ : Fin r) (L : ℕ)
    (c : (Fin (L + 1) → Bool) → ZMod p)
    (d₀ : Bool → Fin r → ZMod p) (d' : Fin L → Bool → Fin r → ZMod p) :
    polyEval j₀ (L + 1) c (Fin.cons d₀ d') =
      stepVal j₀ (polyEval j₀ L (fun b' => c (Fin.cons false b')) d')
        (polyEval j₀ L (fun b' => c (Fin.cons true b')) d') d₀ := by
  unfold polyEval stepVal
  rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => Bool)).sum_comp]
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b' _ => by ring

private theorem card_polyEval_eq_zero_le (p : ℕ) [Fact p.Prime] {r : ℕ} (j₀ : Fin r) :
    ∀ (L : ℕ) (c : (Fin L → Bool) → ZMod p), c ≠ 0 →
      p * (Finset.univ.filter fun d : Fin L → Bool → Fin r → ZMod p =>
          polyEval j₀ L c d = 0).card ≤
        L * Fintype.card (Fin L → Bool → Fin r → ZMod p) := by
  intro L
  induction L with
  | zero =>
    intro c hc
    have hempty : (Finset.univ.filter fun d : Fin 0 → Bool → Fin r → ZMod p =>
        polyEval j₀ 0 c d = 0) = ∅ := by
      ext d
      simp [polyEval]
      split_ifs with h0
      · exfalso
        apply hc
        ext b
        rw [Subsingleton.elim b _, h0]
        rfl
      · simp
    rw [hempty, Finset.card_empty, mul_zero, zero_mul]
  | succ L ih =>
    intro c hc
    let c₀ : (Fin L → Bool) → ZMod p := fun b' => c (Fin.cons false b')
    let c₁ : (Fin L → Bool) → ZMod p := fun b' => c (Fin.cons true b')
    have hc01 : c₀ ≠ 0 ∨ c₁ ≠ 0 := by
      by_contra! h
      apply hc
      ext b
      rw [← Fin.cons_self_tail b]
      cases b 0
      · exact congrFun h.1 (Fin.tail b)
      · exact congrFun h.2 (Fin.tail b)
    let cs : (Fin L → Bool) → ZMod p := if c₀ = 0 then c₁ else c₀
    have hcs : cs ≠ 0 := by
      dsimp [cs]
      split_ifs with h0
      · exact hc01.resolve_left (not_not.mpr h0)
      · exact h0
    have hcs_imp : ∀ d' : Fin L → Bool → Fin r → ZMod p,
        polyEval j₀ L cs d' ≠ 0 →
          polyEval j₀ L c₀ d' ≠ 0 ∨ polyEval j₀ L c₁ d' ≠ 0 := by
      intro d' hd'
      dsimp [cs] at hd'
      split_ifs at hd' with h0
      · exact Or.inr hd'
      · exact Or.inl hd'
    let N₀ := Fintype.card (Bool → Fin r → ZMod p)
    let N' := Fintype.card (Fin L → Bool → Fin r → ZMod p)
    have hcard_prod : Fintype.card (Fin (L + 1) → Bool → Fin r → ZMod p) = N₀ * N' := by
      rw [← Fintype.card_prod]
      exact Fintype.card_congr (Fin.consEquiv (fun _ : Fin (L + 1) => Bool → Fin r → ZMod p)).symm
    have hsplit : (Finset.univ.filter fun d : Fin (L + 1) → Bool → Fin r → ZMod p =>
        polyEval j₀ (L + 1) c d = 0).card =
        ∑ d' : Fin L → Bool → Fin r → ZMod p,
          (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p =>
            stepVal j₀ (polyEval j₀ L c₀ d') (polyEval j₀ L c₁ d') d₀ = 0).card := by
      simp only [Finset.card_filter]
      rw [← (Fin.consEquiv (fun _ : Fin (L + 1) => Bool → Fin r → ZMod p)).sum_comp]
      rw [Fintype.sum_prod_type_right]
      refine Finset.sum_congr rfl fun d' _ => ?_
      refine Finset.sum_congr rfl fun d₀ _ => ?_
      simp [Fin.consEquiv, polyEval_cons, c₀, c₁]
    rw [hsplit, Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun d' : Fin L → Bool → Fin r → ZMod p => polyEval j₀ L cs d' = 0)]
    have hpart1 : ∑ d' ∈ Finset.univ.filter
        (fun d' : Fin L → Bool → Fin r → ZMod p => polyEval j₀ L cs d' = 0),
        p * (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p =>
          stepVal j₀ (polyEval j₀ L c₀ d') (polyEval j₀ L c₁ d') d₀ = 0).card ≤
        L * N' * N₀ := by
      have hle1 : ∑ d' ∈ Finset.univ.filter
          (fun d' : Fin L → Bool → Fin r → ZMod p => polyEval j₀ L cs d' = 0),
          p * (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p =>
            stepVal j₀ (polyEval j₀ L c₀ d') (polyEval j₀ L c₁ d') d₀ = 0).card ≤
          ∑ _d' ∈ Finset.univ.filter
            (fun d' : Fin L → Bool → Fin r → ZMod p => polyEval j₀ L cs d' = 0),
            p * N₀ := by
        refine Finset.sum_le_sum fun d' _ => ?_
        refine Nat.mul_le_mul_left p ?_
        simpa [N₀] using Finset.card_filter_le (Finset.univ : Finset (Bool → Fin r → ZMod p)) _
      rw [Finset.sum_const, smul_eq_mul] at hle1
      have hih := ih cs hcs
      have hih_mul : (Finset.univ.filter fun d' : Fin L → Bool → Fin r → ZMod p =>
          polyEval j₀ L cs d' = 0).card * (p * N₀) ≤ L * N' * N₀ := by
        calc (Finset.univ.filter fun d' : Fin L → Bool → Fin r → ZMod p =>
              polyEval j₀ L cs d' = 0).card * (p * N₀)
            = (p * (Finset.univ.filter fun d' : Fin L → Bool → Fin r → ZMod p =>
              polyEval j₀ L cs d' = 0).card) * N₀ := by ring
          _ ≤ (L * N') * N₀ := Nat.mul_le_mul_right N₀ hih
      exact hle1.trans hih_mul
    have hpart2 : ∑ d' ∈ Finset.univ.filter
        (fun d' : Fin L → Bool → Fin r → ZMod p => ¬polyEval j₀ L cs d' = 0),
        p * (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p =>
          stepVal j₀ (polyEval j₀ L c₀ d') (polyEval j₀ L c₁ d') d₀ = 0).card ≤
        N' * N₀ := by
      have heq2 : ∀ d' ∈ Finset.univ.filter
          (fun d' : Fin L → Bool → Fin r → ZMod p => ¬polyEval j₀ L cs d' = 0),
          p * (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p =>
            stepVal j₀ (polyEval j₀ L c₀ d') (polyEval j₀ L c₁ d') d₀ = 0).card = N₀ := by
        intro d' hd'
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd'
        exact card_stepVal_eq_zero p j₀ _ _ (hcs_imp d' hd')
      rw [Finset.sum_congr rfl heq2, Finset.sum_const, smul_eq_mul]
      refine Nat.mul_le_mul_right N₀ ?_
      simpa [N'] using Finset.card_filter_le (Finset.univ : Finset (Fin L → Bool → Fin r → ZMod p)) _
    rw [hcard_prod]
    calc (∑ d' ∈ Finset.univ.filter
            (fun d' : Fin L → Bool → Fin r → ZMod p => polyEval j₀ L cs d' = 0),
            p * (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p =>
              stepVal j₀ (polyEval j₀ L c₀ d') (polyEval j₀ L c₁ d') d₀ = 0).card) +
          ∑ d' ∈ Finset.univ.filter
            (fun d' : Fin L → Bool → Fin r → ZMod p => ¬polyEval j₀ L cs d' = 0),
            p * (Finset.univ.filter fun d₀ : Bool → Fin r → ZMod p =>
              stepVal j₀ (polyEval j₀ L c₀ d') (polyEval j₀ L c₁ d') d₀ = 0).card
        ≤ L * N' * N₀ + N' * N₀ := add_le_add hpart1 hpart2
      _ = (L + 1) * (N₀ * N') := by ring

end PartialEvalHelpers

theorem solution (p : ℕ) [Fact p.Prime] (L r : ℕ) (hr : 0 < r)
    (B : Fin L → Bool → Matrix (Fin 5) (Fin 5) (ZMod p))
    (f g : (Fin L → Bool) → ZMod p) (hfg : f ≠ g) :
    ((Finset.univ.filter fun d : Fin L → Bool → Fin r → ZMod p =>
        ∑ b : Fin L → Bool, f b • (List.ofFn fun k => blockDiag (d k (b k)) (B k (b k))).prod =
          ∑ b : Fin L → Bool, g b • (List.ofFn fun k => blockDiag (d k (b k)) (B k (b k))).prod).card
        : ℝ) / Fintype.card (Fin L → Bool → Fin r → ZMod p) ≤ (L : ℝ) / p := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let j₀ : Fin r := ⟨0, hr⟩
  let i₀ : Fin (r + 5) := Fin.castAdd 5 j₀
  have hsub_ne : f - g ≠ 0 := sub_ne_zero.mpr hfg
  have hsub : (Finset.univ.filter fun d : Fin L → Bool → Fin r → ZMod p =>
      ∑ b : Fin L → Bool, f b • (List.ofFn fun k => blockDiag (d k (b k)) (B k (b k))).prod =
        ∑ b : Fin L → Bool, g b • (List.ofFn fun k => blockDiag (d k (b k)) (B k (b k))).prod) ⊆
      Finset.univ.filter fun d : Fin L → Bool → Fin r → ZMod p =>
        polyEval j₀ L (f - g) d = 0 := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢
    have hentry := congrArg (fun M : Matrix (Fin (r + 5)) (Fin (r + 5)) (ZMod p) => M i₀ i₀) hd
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul] at hentry
    have hprod_entry : ∀ b : Fin L → Bool,
        ((List.ofFn fun k => blockDiag (d k (b k)) (B k (b k))).prod) i₀ i₀ =
          ∏ k : Fin L, d k (b k) j₀ := by
      intro b
      rw [blockDiag_prod L (fun k => d k (b k)) (fun k => B k (b k))]
      simp [i₀, bd_ll]
    simp only [hprod_entry] at hentry
    unfold polyEval
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, hentry, sub_self]
  have hcard_le : p * (Finset.univ.filter fun d : Fin L → Bool → Fin r → ZMod p =>
      ∑ b : Fin L → Bool, f b • (List.ofFn fun k => blockDiag (d k (b k)) (B k (b k))).prod =
        ∑ b : Fin L → Bool, g b • (List.ofFn fun k => blockDiag (d k (b k)) (B k (b k))).prod).card ≤
      L * Fintype.card (Fin L → Bool → Fin r → ZMod p) :=
    (Nat.mul_le_mul_left p (Finset.card_le_card hsub)).trans
      (card_polyEval_eq_zero_le p j₀ L (f - g) hsub_ne)
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hD_pos : (0 : ℝ) < Fintype.card (Fin L → Bool → Fin r → ZMod p) := by
    exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ hD_pos hp_pos]
  have h_real : (p : ℝ) * ((Finset.univ.filter fun d : Fin L → Bool → Fin r → ZMod p =>
      ∑ b : Fin L → Bool, f b • (List.ofFn fun k => blockDiag (d k (b k)) (B k (b k))).prod =
        ∑ b : Fin L → Bool, g b • (List.ofFn fun k => blockDiag (d k (b k)) (B k (b k))).prod).card : ℝ) ≤
      (L : ℝ) * (Fintype.card (Fin L → Bool → Fin r → ZMod p) : ℝ) := by
    exact_mod_cast hcard_le
  linarith
