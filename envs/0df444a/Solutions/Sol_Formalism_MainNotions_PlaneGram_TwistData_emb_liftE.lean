-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.emb_liftE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:30:43.627928+00:00
-- url     : https://prove2.me/submissions/10237252-480a-436a-82cf-f3002f6c6e9e

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_letE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_divE_apply
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_liftE_mb
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_liftE_mw
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_emb_inl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_emb_inr
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
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (ρ : D.Tau → Fin D.r → ℕ) (α : D.EA) (h : D.InClass p ρ α) :
    D.emb p ρ (D.liftE p α) = α := by
  ext ⟨x, a⟩
  rcases x with b | t
  · rw [emb_inl, liftE_mb]
  · rw [emb_inr, liftE_mw, ← h t a, Nat.mod_add_div]
end Formalism.MainNotions.PlaneGram.TwistData
