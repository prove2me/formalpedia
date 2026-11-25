-- Prove2me | solution 1 for Formalism.CohomologicalDescent.ShortWeightBounds.sizeData_boundW_of_le_seventh_recursion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:23:44.517121+00:00
-- url     : https://prove2.me/submissions/6c69d4f3-4d2e-4618-9abf-f424b258ac60

import Definitions.Def_Formalism_PieriBlockIdeals_LatticeInclusionRealSettingAlt
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RealLocalDeltaNabla
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WeightBounds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_j_w_seven_le_holds
import Theorems.Thm_Formalism_CohomologicalDescent_ShortWeightBounds_seventh_recursion_eq_w_of_large_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.ShortWeightBounds
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds
namespace Formalism.CohomologicalDescent.ShortWeightBounds
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (W : Wts ι) (P : Par) (hH : P.Hyp)
    (hL : P.Large) (hW : W.Ok P) (J : ℕ → ℕ) (hJ : ∀ l : ℕ, l.Prime → J l ≤ W.Jrec7 P l) :
    (W.sizeData₂ P J).BoundW P := by
  intro l hl hlJ hE hS _ _ _
  have hc : ¬ ((l : ℝ) ≤ P.lJ ∨ P.Excl l ∨ l ∈ W.Sp) :=
    not_or.mpr ⟨not_le.mpr hlJ, not_or.mpr ⟨hE, hS⟩⟩
  have h1 := hJ l hl
  rw [seventh_recursion_eq_w_of_large_prime W P l hc] at h1
  have h2 := (j_w_seven_le_holds P hH hL ι W hW J l hl.two_le).2
  have h3 : (J l : ℝ) ≤ (W.coarseWeightBound P l : ℝ) := by exact_mod_cast h1
  refine (h3.trans h2).trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro τ _
  by_cases hτ : τ ∈ (W.sizeData₂ P J).T2
  · rw [if_pos hτ, if_pos hτ]
  · rw [if_neg hτ, if_neg hτ]
end Formalism.CohomologicalDescent.ShortWeightBounds
