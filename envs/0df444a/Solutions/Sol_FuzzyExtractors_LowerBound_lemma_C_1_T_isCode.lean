-- Prove2me | solution 1 for FuzzyExtractors.LowerBound.lemma_C_1_T_isCode
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T01:18:57.389719+00:00
-- url     : https://prove2.me/submissions/1c47cee9-eccb-48ee-b7a3-8d8a9850eae1

import Mathlib
import Definitions.Def_FuzzyExtractors_LowerBound_Basic

open FuzzyExtractors.LowerBound

theorem solution {M V : Type} [Fintype M] (dis : M → M → ℕ)
    (hzero : ∀ x y, dis x y = 0 ↔ x = y)
    (hsymm : ∀ x y, dis x y = dis y x)
    (htri : ∀ x y z, dis x z ≤ dis x y + dis y z)
    (t : ℕ) (SS : M → PMF V) (Rec : M → V → PMF M)
    (hcorr : FuzzyExtractors.Hamming.SketchCorrect dis t SS Rec) (S : Finset M) (v : V) :
    FuzzyExtractors.Hamming.IsCode dis (producers SS S v) t := by
  classical
  intro w c hc c' hc' hd hd'
  have h1 := hcorr c w (by simpa [hsymm] using hd) v (Finset.mem_filter.mp hc).2
  have h2 := hcorr c' w (by simpa [hsymm] using hd') v (Finset.mem_filter.mp hc').2
  have h := congrArg (fun p : PMF M => c ∈ p.support) (h1.symm.trans h2)
  simpa using h

#print axioms solution
