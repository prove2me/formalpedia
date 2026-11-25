-- Prove2me | solution 2 for DetDLP.lemma_2_3_mult_gadget
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T12:27:42.397289+00:00
-- url     : https://prove2.me/submissions/12bd1bde-97fb-4085-a0cf-2163d088e598

import Mathlib
import Definitions.Def_DetDLP_BTN
import Theorems.Thm_DetDLP_schonhage_strassen_fermat_dft_and_carry
import Theorems.Thm_DetDLP_schonhage_strassen_btn_tm_from_fermat_carry

set_option autoImplicit false

open DetDLP
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

theorem solution :
    ∃ (E : PrimitiveMachine) (outE : Fin E.tapeCount) (K : ℕ),
      ∀ d : ℕ, 1 ≤ d →
        ∃ (G : BipartiteMultigraph)
          (T : (v : Fin G.nV) → (Fin (G.deg v) → Bool) → Bool)
          (ext : Fin (4 * d) → Fin G.nE),
          G.nE < 1100 * (d + 1) ∧
          (G.maxDeg : ℝ) < 136 * ((d : ℝ) + 1) ^ ((3 : ℝ) / 4) ∧
          (G.nV : ℝ) ≤ polyBound K d ∧
          BoolBTNEntryEvaluable (countWord d) G T E outE (polyBound K d) (polyBound K d) ∧
          IsParsimonious G T ext (fun x =>
            bitsToNat (fun i : Fin d => x ⟨i.val, by omega⟩) *
            bitsToNat (fun i : Fin d => x ⟨d + i.val, by omega⟩) =
            bitsToNat (fun i : Fin (2 * d) => x ⟨2 * d + i.val, by omega⟩)) :=
  DetDLP.schonhage_strassen_btn_tm_from_fermat_carry
    DetDLP.schonhage_strassen_fermat_dft_and_carry
