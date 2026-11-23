-- Prove2me | solution 1 for Formalism.CountingSumsFrames.harmonicProjection_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:20:59.697229+00:00
-- url     : https://prove2.me/submissions/5cdf0def-03f6-4c33-9213-90078fa8fd43

import Definitions.Def_Formalism_PolynomialDimension_StatementHar
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_HarmonicDecompositionHolds
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_mem
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_sub
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_har
import Theorems.Thm_Formalism_CountingSumsFrames_Har2_harProj_kill

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset MvPolynomial
open Formalism Formalism.CountingSumsFrames
open Har2
namespace Formalism.CountingSumsFrames
theorem _root_.solution : HarProj := by
  unfold HarProj
  intro K _ _ k A B hk
  exact ⟨fun f hf => ⟨harProj_mem hk hf, harProj_sub hf⟩, fun f hf => harProj_har hf,
    fun hA hB g hg => harProj_kill hk hA hB hg⟩
end Formalism.CountingSumsFrames
