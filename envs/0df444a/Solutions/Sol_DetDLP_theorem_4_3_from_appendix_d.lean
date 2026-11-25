-- Prove2me | solution 1 for DetDLP.theorem_4_3_from_appendix_d
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-24T05:16:15.390748+00:00
-- url     : https://prove2.me/submissions/c788b906-3499-47ee-9492-51c5ef4fafac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_DetDLP_lemma_5_2_from_appendix_d
import Theorems.Thm_DetDLP_section5_guard_and_kronecker
import Theorems.Thm_DetDLP_theorem_4_3_tm_from_lemma_5_2
import Mathlib
import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_FactorBase
import Definitions.Def_DetDLP_TerminalBTN

set_option autoImplicit false

open DetDLP

open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation

theorem solution (hOAI : OpenAIAppendixDPremise) :
    ∀ (C c0 : ℕ), 0 < C → 0 < c0 →
      ∀ (E : PrimitiveMachine) (outE : Fin E.tapeCount),
        ∃ (M : PrimitiveMachine) (outM : Fin M.tapeCount) (K : ℕ),
          ∀ (b m k S P0 ℓ : ℕ) (desc : List Bool) (G : BipartiteMultigraph)
            (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → TruncPoly P0 ℓ),
            2 ≤ b →
            1 ≤ m → 1 ≤ k →
            blockCount b ≤ C * m → m ≤ C * blockCount b →
            S ≤ C * m * b →
            4 * m * k ≤ C * b → b ≤ C * (4 * m * k) →
            1 ≤ P0 → P0 ≤ S →
            1 ≤ ℓ → ℓ ≤ C * m →
            G.nV ≤ (S + desc.length + 1) ^ c0 →
            ∀ (spec : LookupSeparatorSpec G m k S (C * Nat.ceil ((b : ℝ) ^ ((3 : ℝ) / 4)))),
            BTNEntryEvaluable desc G P0 ℓ T E outE
              (polyBound c0 (S + desc.length)) (polyBound c0 (S + desc.length)) →
            ∃ w : List Bool,
              EncodesTruncPoly P0 ℓ w (BTNContract G T) ∧
              RunsWithin M outM (encodeTerminalBTNInstance desc G b m k S P0 ℓ spec.lookupVerts) w
                (polyBound K (S + desc.length) * mainTimeBound K b)
                (polyBound K (S + desc.length)) := by
  exact theorem_4_3_tm_from_lemma_5_2 (lemma_5_2_from_appendix_d hOAI) section5_guard_and_kronecker


