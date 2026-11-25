-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.degD_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:00:47.69492+00:00
-- url     : https://prove2.me/submissions/f639fbb9-eced-403a-a14a-0bbe8308a670

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_deg_bot
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_rkK_bot
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_eq_bot_of_rkK
import Theorems.Thm_P2M_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_finrank_pos__df67f6332271
import Theorems.Thm_Formalism_HN_plLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.BranchingDeterminantCap.OrthogonalSumAlt
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap.OrthogonalSumAlt
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (L : Submodule (𝓞 K) V) (hL : L.FG) :
    degD b X L = 2 / (Module.finrank ℚ K : ℝ) * Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L +
      (Formalism.HN.rkK L : ℝ) * (-Real.log 2 + Formalism.HN.logDisc K / (Module.finrank ℚ K : ℝ)) := by
  by_cases h0 : L = ⊥
  · subst h0
    simp [degD, rkK_bot, deg_bot b X hX]
  · have hr : Formalism.HN.rkK L ≠ 0 := fun h => h0 (eq_bot_of_rkK b h)
    have hrk := (Formalism.HN.plLat K V ι b X hX L hL).2.1
    have hs : Formalism.HN.slope (Formalism.HermitianLatticesTheory.realize b X) L =
        Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) L / (Formalism.HN.rk (Formalism.HermitianLatticesTheory.realize b X) L : ℝ) := rfl
    have hn : (Module.finrank ℚ K : ℝ) ≠ 0 := by
      exact_mod_cast (finrank_pos' (K := K)).ne'
    have hr' : (Formalism.HN.rkK L : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [degD, Formalism.HN.muDef, hs, hrk]
    push_cast
    field_simp
    ring
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
