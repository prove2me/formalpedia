-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.idxFull_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:26:37.870514+00:00
-- url     : https://prove2.me/submissions/1e1bfe0a-679d-48f0-84f7-036245acb3f5

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxFull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution (hMono : IdxMono) (hSc : IdxScaleIn) : IdxFull := by
  intro K _ _ _ Z _ _ _ _ _ w M Th ThK hM hTh hThK _hThM σ hσ hsc E r hE
  obtain ⟨hlat, heq⟩ := hSc K Z w ⊤ M ThK hM hThK σ hσ
  have hmono : lix w M (sc σ ThK) ≤ lix w M Th := hMono K Z w ⊤ M Th (sc σ ThK) hM hTh hlat hsc
  have hm : (lix w M (sc σ ThK) : ℝ) ≤ (lix w M Th : ℝ) := by exact_mod_cast hmono
  have hv : (lix w M (sc σ ThK) : ℝ) = (lix w M ThK : ℝ) + (finrank K Z : ℝ) * (vw w σ : ℝ) := by
    rw [heq]
    push_cast
    rw [finrank_top]
  linarith
end Formalism.EigenvalueLevelCeiling
