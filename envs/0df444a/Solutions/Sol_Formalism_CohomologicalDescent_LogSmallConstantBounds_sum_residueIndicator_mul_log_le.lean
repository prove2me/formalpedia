-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LogSmallConstantBounds.sum_residueIndicator_mul_log_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:14:20.195801+00:00
-- url     : https://prove2.me/submissions/cf1b4570-2e00-4043-a525-aab4871bae4d

import Definitions.Def_Formalism_PieriBlockIdeals_MertensReciprocalElementary
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LocalComponentGL
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_CardLargePrimeFactorsLeOneHolds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_eight_lt_lJ
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_floor_h_bounds
import Theorems.Thm_Formalism_CohomologicalDescent_LogSmallConstantBounds_le_floor_h
import Theorems.Thm_Formalism_CohomologicalDescent_residueIndicatorPrimeSum_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LogSmallConstantBounds
open Classical
namespace Formalism.CohomologicalDescent.LogSmallConstantBounds
theorem _root_.solution {P : Par} (H : P.Hyp) (G : P.Large) {ι : Type} {D : SizeData₂ ι}
    (hT : D.ShapeT P) {τ : ι} (hτ : τ ∈ D.T2) {R : Finset ℕ}
    (hR : ∀ l ∈ R, l.Prime ∧ P.lJ < (l : ℝ) ∧ (l : ℝ) ≤ P.h) :
    ∑ l ∈ R, IlInd l (D.xlo τ) (D.xhi τ) (D.maxB τ) * Real.log (l : ℝ) ≤
      (P.S + 1) * Real.log P.h := by
  obtain ⟨hmb0, hmbx, hxx, hxh, hS, _⟩ := hT τ hτ
  have hJ8 := eight_lt_lJ H G
  obtain ⟨f1, f2, f3, f4, f5⟩ := floor_h_bounds H G
  have hxhN := le_floor_h H hxh
  have key := Formalism.CohomologicalDescent.residueIndicatorPrimeSum_holds ⌊P.h⌋₊ P.lJ (D.xlo τ) (D.xhi τ) (D.maxB τ) R
    (by linarith) f3 hmb0 hmbx hxx hxhN (fun l hl => ⟨(hR l hl).1, (hR l hl).2.1⟩)
  have hS0 := H.S_nonneg
  exact key.trans (mul_le_mul (by linarith) f5 f4 (by linarith))
end Formalism.CohomologicalDescent.LogSmallConstantBounds
