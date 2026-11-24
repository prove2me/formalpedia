-- Prove2me | solution 1 for Formalism.CountingSumsFrames.glAct_isL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:48:32.296407+00:00
-- url     : https://prove2.me/submissions/07b2c75d-3184-4f73-8386-0d4881cadafc

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_MonoCount
import Theorems.Thm_Formalism_CountingSumsFrames_isL_iff
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_lw


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open MvPolynomial Finset Formalism.GM.DimensionMonotonicity Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (L : Letters N) (j0 J : ℕ) (c d : Fin r) {g : MvPolynomial (Fin N × Fin r) ℚ_[p]}
    (hg : IsL (fsj N r j0) g) : IsL (fsj N r j0) (glAct p L J c d g) := by
  rw [isL_iff] at hg ⊢
  exact glAct_lw L J c d (wfir N r j0) (fun i c c' => rfl) hg
end Formalism.CountingSumsFrames
