-- Prove2me | solution 1 for DistancePreserver934.Exact.lemma_13
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T00:00:48.231182+00:00
-- url     : https://prove2.me/submissions/f2bb34c2-e2e5-4e7b-8034-d166f9331e08

import Definitions.Def_DistancePreserver934_Exact_LoyalCore

set_option autoImplicit false
open Classical DistancePreserver934.Exact

private lemma core_univ {V : Type} [Fintype V] (H : SimpleGraph V) (R : Finset (Sym2 V)) :
    coreEdges H R Finset.univ = privEdges H R := by
  simp [coreEdges]

private lemma core_empty {V : Type} [Fintype V] (H : SimpleGraph V) (R : Finset (Sym2 V)) :
    coreEdges H R ∅ = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  obtain ⟨_, h⟩ := Finset.mem_filter.mp he
  induction e using Sym2.ind with
  | _ a b => exact Finset.notMem_empty a (h a (by simp))

private lemma core_erase {V : Type} [Fintype V] (H : SimpleGraph V)
    (R : Finset (Sym2 V)) (S : Finset V) (x : V) :
    coreEdges H R (S.erase x) = (coreEdges H R S).filter (fun e => x ∉ e) := by
  classical
  ext e
  simp only [coreEdges, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨he,h⟩
    refine ⟨⟨he, fun v hv => (h v hv).2⟩, ?_⟩
    intro hx
    exact (h x hx).1 rfl
  · rintro ⟨⟨he,h⟩,hx⟩
    exact ⟨he, fun v hv => ⟨fun hvx => hx (hvx ▸ hv), h v hv⟩⟩

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V) (R : Finset (Sym2 V))
    (n : ℕ) (d : ℝ)
    (hV0 : 0 < Fintype.card V)
    (hR : IsDemandSet G R) (hH : IsMinimalPreserver G H R)
    (hV : Fintype.card V ≤ n) (hE : (numEdges H : ℝ) ≤ n * d)
    (hΛ : (n : ℝ) * d / 20 ≤ ((privEdges H R).card : ℝ)) :
    ∃ Vs : Finset V, Eq6 H R Vs n d := by
  classical
  have hne : (Finset.univ : Finset V).Nonempty := by
    apply Finset.card_pos.mp
    simpa using hV0
  by_cases hd : d ≤ 0
  · refine ⟨Finset.univ, hne, ?_, ?_⟩
    · have : (n : ℝ) * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hd
      exact le_trans (by linarith) (Nat.cast_nonneg _)
    · intro x hx
      exact le_trans (by linarith : d / 40 ≤ 0) (Nat.cast_nonneg _)
  have hd' : 0 < d := lt_of_not_ge hd
  have hn : 0 < (n : ℝ) := by exact_mod_cast hV0.trans_le hV
  let f : Finset V → ℝ := fun S => ((coreEdges H R S).card : ℝ) - d / 40 * S.card
  obtain ⟨S,_,hS⟩ := Finset.exists_max_image (Finset.univ : Finset (Finset V)) f (by simp)
  have hstart := hS Finset.univ (Finset.mem_univ _)
  simp only [f, core_univ, Finset.card_univ] at hstart
  have hV' : (Fintype.card V : ℝ) ≤ n := by exact_mod_cast hV
  have hbudget : (n : ℝ) * d / 40 ≤ f S := by
    dsimp [f]
    nlinarith
  have hnonempty : S.Nonempty := by
    by_contra hs
    have hz : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [hz] at hbudget
    simp only [f, core_empty, Finset.card_empty, Nat.cast_zero, mul_zero, sub_zero] at hbudget
    nlinarith
  refine ⟨S, hnonempty, ?_, ?_⟩
  · dsimp [f] at hbudget
    have : 0 ≤ d / 40 * (S.card : ℝ) := by positivity
    linarith
  · intro x hx
    have hmax := hS (S.erase x) (Finset.mem_univ _)
    have hpart : (coreEdges H R (S.erase x)).card + coreDeg H R S x = (coreEdges H R S).card := by
      rw [core_erase, coreDeg]
      simpa only [not_not] using Finset.card_filter_add_card_filter_not (s := coreEdges H R S) (p := fun e => x ∉ e)
    have hpart' : ((coreEdges H R (S.erase x)).card : ℝ) + (coreDeg H R S x : ℝ) =
        ((coreEdges H R S).card : ℝ) := by exact_mod_cast hpart
    have hcard : ((S.erase x).card : ℝ) + 1 = (S.card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one hx
    dsimp [f] at hmax
    nlinarith
