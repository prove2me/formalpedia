-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.kappa_constant_same_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:06:53.896581+00:00
-- url     : https://prove2.me/submissions/f2e356e1-f4e1-43e0-94b6-2c733aeaae94

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_label_function_same_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}
omit [CharZero K]
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (cst : D.Tau → (Fin D.r → ℕ) → ℕ → K) {ζ ζ' : D.EM} (hb : D.SameBlockAlt ζ ζ') :
    D.kapC cst ζ' = D.kapC cst ζ := by
  have hL := D.label_function_same_block hb
  unfold SameBlockAlt at hb
  obtain ⟨hl, hlab, _⟩ := hb
  unfold kapC
  rw [hL]
  simp only [hl, hlab]
end Formalism.MainNotions.PlaneGram.TwistData
