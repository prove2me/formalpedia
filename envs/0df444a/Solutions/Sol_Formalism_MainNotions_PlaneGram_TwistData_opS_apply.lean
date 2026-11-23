-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.opS_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:45:15.241636+00:00
-- url     : https://prove2.me/submissions/2a586078-db94-4826-be2b-f13fb0f7d347

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_ddiv_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.PlaneGram.letE_apply
attribute [local simp] Formalism.MainNotions.PlaneGram.divE_apply

set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K) (p : ℕ)
variable (t : D.Tau)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (μ κ1 : Fin D.r →₀ ℕ) (c1 : K) (Q : MvPolynomial (D.ML × Fin D.r) K) :
    D.opS t μ κ1 c1 Q = c1 • (monomial (onLetter (D.mw t) μ) (1 : K) * ddiv (onLetter (D.mw t) κ1) Q) := by
  simp only [opS, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulLeft_apply, Formalism.MainNotions.PlaneGram.ddiv_eq]
end Formalism.MainNotions.PlaneGram.TwistData
