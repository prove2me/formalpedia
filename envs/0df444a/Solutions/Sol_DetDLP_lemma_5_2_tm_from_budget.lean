-- Prove2me | solution 1 for DetDLP.lemma_5_2_tm_from_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T14:12:56.098388+00:00
-- url     : https://prove2.me/submissions/0da1b8cb-c952-4ea5-b9c5-32736f5854a6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_lemma_5_2_handshake_hub_bound_and_2adic_loss
import Theorems.Thm_DetDLP_milestones_8_9_primitive_machine_compilation

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem solution :
    ((∀ (D : ℕ) (β ρ : ℝ), 0 ≤ β → 0 < ρ →
        ∑ d ∈ Finset.range (D + 1),
          (β * ((1 : ℝ) / 8) ^ d) / Real.sqrt (ρ * ((1 : ℝ) / 2) ^ d) ≤
          (4 / 3 : ℝ) * (β / Real.sqrt ρ)) ∧
      (∀ (D : ℕ) (ε ρ : ℝ), 0 ≤ ε → 0 ≤ ρ →
        2 * (∑ j ∈ Finset.range (D + 1), (Nat.floor (ε * ρ / (2 : ℝ) ^ j) : ℝ)) ≤
          4 * ε * ρ) ∧
      (∀ M : ℕ, 1 ≤ M →
        3 * M / 32 < M / 8 + 1 ∧ (3 : ℝ) * (M : ℝ) / 32 < (M : ℝ) / 8)) →
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (β P ℓ' Told : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P ℓ'),
            2 ≤ β →
            1 ≤ Told →
            G.nE ≤ C * β →
            G.nV ≤ β ^ c0 →
            1 ≤ P → P ≤ C * β →
            1 ≤ ℓ' → ℓ' ≤ C * β →
            BTNEntryEvaluable desc G P ℓ' T E outE (Told : ℝ) (((β + desc.length : ℕ) : ℝ) ^ c0) →
            let Δbar : ℕ := max G.maxDeg (Nat.ceil ((β : ℝ) ^ ((9 : ℝ) / 10)))
            let ρ : ℕ := max 1 (Nat.floor (Real.logb 2 ((β : ℝ) / (Δbar : ℝ))))
            ∃ w : List Bool,
              EncodesTruncPoly P ℓ' w (BTNContract G T) ∧
              RunsWithin M outM (encodeBTNInstance desc G β P ℓ') w
                (polyBound K (β + desc.length) * (Told : ℝ) *
                  (2 : ℝ) ^ ((K : ℝ) * (β : ℝ) / Real.sqrt (ρ : ℝ)))
                (polyBound K (β + desc.length)) :=
  fun _ =>
    (DetDLP.milestones_8_9_primitive_machine_compilation
      DetDLP.lemma_5_2_handshake_hub_bound_and_2adic_loss).1
