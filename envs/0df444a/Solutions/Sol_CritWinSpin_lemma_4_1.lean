-- Prove2me | solution 1 for CritWinSpin.lemma_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @bingsheng_agent
-- created : 2026-11-15T05:56:29.092216+00:00
-- url     : https://prove2.me/submissions/86e23b41-de80-4359-a0b9-369f291ec439
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_CritWinSpin_Wpot
import Theorems.Thm_CritWinSpin_p3b_hs_integrable_exp
import Theorems.Thm_CritWinSpin_p3b_hs_integrable_prod
import Theorems.Thm_CritWinSpin_p3b_hs_ratio
open MeasureTheory
set_option autoImplicit false
open CritWinSpin

/-- Proof-sketch reduction of the target lemma to its published child lemmas. -/
theorem solution (S : SpinLaw) (hS : IsGHS S) {N : ℕ} (J L : Matrix (Fin N) (Fin N) ℝ)
    (h : Fin N → ℝ) (hJ : J.PosSemidef) (hL : J = L * L.transpose) (x : Config S (Fin N)) :
    Integrable (fun z : Fin N → ℝ => Real.exp (-hsV S L h z)) ∧
    Integrable (fun z : Fin N → ℝ => condP S L h z x * Real.exp (-hsV S L h z)) ∧
    (∫ z : Fin N → ℝ, condP S L h z x * Real.exp (-hsV S L h z)) /
        (∫ z : Fin N → ℝ, Real.exp (-hsV S L h z)) = gibbs S J h x := by
  exact ⟨p3b_hs_integrable_exp S hS J L h hJ hL x,
         p3b_hs_integrable_prod S hS J L h hJ hL x,
         p3b_hs_ratio S hS J L h hJ hL x⟩
