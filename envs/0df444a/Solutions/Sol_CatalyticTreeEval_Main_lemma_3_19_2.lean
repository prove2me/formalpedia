-- Prove2me | solution 2 for CatalyticTreeEval.Main.lemma_3_19
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T22:45:31.476414+00:00
-- url     : https://prove2.me/submissions/f3968db0-eada-4d31-b42e-42b2a4573989
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_CatalyticTreeEval_Main_Decoder
import Theorems.Thm_CatalyticTreeEval_Main_canonical_decoder_properties
import Theorems.Thm_CatalyticTreeEval_Main_canonical_decoder_access

set_option autoImplicit false

open CatalyticTreeEval.Main

theorem solution :
    ∃ (M : Machine) (Cs Ct : ℝ) (q : ℕ), 0 < Cs ∧ 0 < Ct ∧ 0 < q ∧
      ∀ (t : ℕ) (p : Fin t → ℕ), OddPrimeData p →
      ∃ (k : ℕ) (D : Decoder (modulus p) k), k ≤ 3 ^ t ∧
        (∀ z : ZMod (modulus p), z ∈ sumset (canonical p (modulus p)) ↔
          ∀ i, z.val % p i = 0 ∨ z.val % p i = 1 ∨ z.val % p i = 2) ∧
        IsDecoder (sumset (canonical p (modulus p))) D ∧
        (∀ j z, PrintsIn M (decoderRequest (primeCode p) j.val z.val)
          (decoderOutput D j z) (Cs * log₂ (modulus p))
          (Ct * (1 + log₂ (modulus p)) ^ q)) := by
  obtain ⟨M, Cs, Ct, q, hCs, hCt, hq, hprint⟩ := canonical_decoder_access
  refine ⟨M, Cs, Ct, q, hCs, hCt, hq, ?_⟩
  intro t p hp
  obtain ⟨hmem, hdecode, _⟩ := canonical_decoder_properties p hp
  exact ⟨3 ^ t, CatalyticTreeEval.DecoderConstruction.canonicalDecoder p hp.1, le_rfl,
    hmem, hdecode, hprint t p hp⟩
