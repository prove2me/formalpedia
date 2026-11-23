-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FormDomination.mean_dom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:41.661823+00:00
-- url     : https://prove2.me/submissions/6bcc18f1-e419-4a49-98dc-b14d6bf741c0

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementTB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FormDomination
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_prob_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_FormDomination_sum_baseGram_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FormDomination
open Finset Formalism.FourierDecayAlt.TB Formalism.FourierDecayAlt.TB.Data
open scoped ComplexOrder
variable {E W : Type} [Field E] (D : Data E W)
namespace Formalism.FourierDecayAlt.P.FormDomination
theorem _root_.solution (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ)
    (S : Finset W) (θ : W → ℝ) (hθ : IsProb S θ)
    (Y : Finset (Pt E)) (R : Finset E) (c : ℝ) (hc : 0 ≤ c) (κ : Pt E → Pt E → ℂ)
    (Th : E → Pt E → Pt E → ℂ)
    (h : PSDOn Y (fun a b => (c : ℂ) * κ a b - ∑ t ∈ R, Th t a b)) (M : ℝ)
    (hM : ∀ w' ∈ S, D.N0 ε k w' Y κ ≤ M) :
    ∑ t ∈ R, ∑ w' ∈ S, θ w' * D.N0 ε k w' Y (Th t) ≤ c * M := by
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  refine prob_le S θ _ hθ _ fun w' hw' => ?_
  exact (sum_baseGram_le D hG hW hε k w' Y R c κ Th h).trans (mul_le_mul_of_nonneg_left (hM w' hw') hc)
end Formalism.FourierDecayAlt.P.FormDomination
