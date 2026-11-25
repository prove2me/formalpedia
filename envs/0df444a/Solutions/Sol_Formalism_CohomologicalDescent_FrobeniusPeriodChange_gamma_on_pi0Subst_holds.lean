-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamma_on_pi0Subst_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:41.109916+00:00
-- url     : https://prove2.me/submissions/eed13e5f-223d-4051-8df7-2bad6935858e

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_constantCoeff_gammaSeries
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_pi0Subst_laws_hold
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_binomialSeriesSubOne
import Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_hasSubst_pi0_alt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : GammaOnInc := by
  intro l _ O _ _ u un hun y
  obtain ⟨hadd, hmul, hC, hX, hq, -, hsub, -⟩ := pi0Subst_laws_hold l O
  have hP := hasSubst_pi0_alt l O
  have h1 : act l O u (inc l O y) = y.subst (act l O u (pi0 l O)) :=
    subst_comp_subst_apply hP (hasSubst_binomialSeriesSubOne l O u) y
  have h2 : inc l O (gam0 (l : O) un y) = y.subst (inc l O (gamSer (l : O) un)) :=
    hsub y _ (constantCoeff_gammaSeries _ _)
  have h3 : inc l O (gamSer (l : O) un) = pi0 l O * (1 + inc l O un * q0 l O) := by
    unfold gamSer
    have h1' : inc l O 1 = 1 := by
      have := hC 1
      simpa using this
    rw [hmul, hadd, hmul, hX, hq, h1']
  rw [h1, h2, h3, hun]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
