-- Prove2me | solution 1 for DiscreteConvex.NetworkFlowsC.unique_min_weight_perfect_matching_iff
-- status  : ACCEPTED   (disprove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:26:19.764467+00:00
-- url     : https://prove2.me/submissions/274c31a8-2545-4e26-8f99-8ba0511fcc9d

import Mathlib
import Definitions.Def_DiscreteConvex_NetworkFlowsC_IsMinWeightMatching
import Definitions.Def_DiscreteConvex_NetworkFlowsC_MinWeightValue

set_option autoImplicit false
set_option linter.unusedVariables false

open DiscreteConvex.NetworkFlowsC

namespace MatchCex

def S : Finset Unit := {()}

noncomputable def c : Unit → Unit → WithTop ℝ := fun _ _ => ((5 : ℝ) : WithTop ℝ)

def M0 : Finset (Unit × Unit) := {((), ())}

theorem bm_iff (M : Finset (Unit × Unit)) : BipartiteMatching S S M ↔ M = M0 := by
  constructor
  · rintro ⟨-, h2, -⟩
    obtain ⟨v, hv, -⟩ := h2 () (by simp [S])
    ext p
    obtain ⟨⟨⟩, ⟨⟩⟩ := p
    simp only [M0, Finset.mem_singleton, iff_true]
    exact hv
  · rintro rfl
    refine ⟨?_, ?_, ?_⟩
    · intro p _; simp [S]
    · intro u _; exact ⟨(), by simp [M0], fun _ _ => rfl⟩
    · intro v _; exact ⟨(), by simp [M0], fun _ _ => rfl⟩

theorem weight (M : Finset (Unit × Unit)) (h : BipartiteMatching S S M) :
    MatchingWeight c M = ((5 : ℝ) : WithTop ℝ) := by
  rw [(bm_iff M).mp h]; simp [MatchingWeight, M0, c]

theorem lhs : (∃! M, IsMinWeightMatching S S c M) ∧ MinWeightValue S S c ≠ ⊤ := by
  refine ⟨⟨M0, ⟨(bm_iff M0).mpr rfl, fun M' hM' => by
    rw [weight M0 ((bm_iff M0).mpr rfl), weight M' hM']⟩, fun M hM => (bm_iff M).mp hM.1⟩, ?_⟩
  have hset : {w : WithTop ℝ | ∃ M, BipartiteMatching S S M ∧ w = MatchingWeight c M} =
      {((5 : ℝ) : WithTop ℝ)} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨M, hM, rfl⟩; exact weight M hM
    · rintro rfl; exact ⟨M0, (bm_iff M0).mpr rfl, (weight M0 ((bm_iff M0).mpr rfl)).symm⟩
  unfold MinWeightValue
  rw [hset]
  rw [WithTop.sInf_eq (by simp) (by simp)]
  exact WithTop.coe_ne_top

theorem not_rhs : ¬ ∃ (phat : Unit → ℝ) (ordU ordV : Fin 1 → Unit), (∀ i, ordU i ∈ S) ∧
      (∀ i, ordV i ∈ S) ∧ Function.Injective ordU ∧ Function.Injective ordV ∧
      ∀ i j : Fin 1,
        (i = j → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) -
          (phat (ordV j) : WithTop ℝ) = 0) ∧
        ((j:ℕ) < (i:ℕ) → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) -
          (phat (ordV j) : WithTop ℝ) ≥ 0) ∧
        ((i:ℕ) < (j:ℕ) → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) -
          (phat (ordV j) : WithTop ℝ) > 0) := by
  rintro ⟨phat, ordU, ordV, -, -, -, -, h⟩
  have h0 := (h 0 0).1 rfl
  have e : c (ordU 0) (ordV 0) + (phat (ordU 0) : WithTop ℝ) - (phat (ordV 0) : WithTop ℝ) =
      ((5 + phat () - phat () : ℝ) : WithTop ℝ) := by
    simp only [c]; norm_cast
  rw [e] at h0
  have := WithTop.coe_eq_zero.mp h0
  linarith

end MatchCex

theorem solution : ¬ (∀ {V : Type} [Fintype V] [DecidableEq V]
    (Vp Vn : Finset V) (m : ℕ) (hVp : Vp.card = m) (hVn : Vn.card = m) (c : V → V → WithTop ℝ),
    ((∃! M, IsMinWeightMatching Vp Vn c M) ∧ MinWeightValue Vp Vn c ≠ ⊤) ↔
    ∃ (phat : V → ℝ) (ordU ordV : Fin m → V), (∀ i, ordU i ∈ Vp) ∧ (∀ i, ordV i ∈ Vn) ∧
      Function.Injective ordU ∧ Function.Injective ordV ∧
      ∀ i j : Fin m,
        (i = j → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) - (phat (ordV j) : WithTop ℝ) = 0) ∧
        ((j:ℕ) < (i:ℕ) → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) - (phat (ordV j) : WithTop ℝ) ≥ 0) ∧
        ((i:ℕ) < (j:ℕ) → c (ordU i) (ordV j) + (phat (ordU i) : WithTop ℝ) - (phat (ordV j) : WithTop ℝ) > 0)) := by
  intro h
  exact MatchCex.not_rhs ((h MatchCex.S MatchCex.S 1 rfl rfl MatchCex.c).mp MatchCex.lhs)

#print axioms solution
