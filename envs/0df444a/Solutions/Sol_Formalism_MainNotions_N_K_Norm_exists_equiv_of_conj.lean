-- Prove2me | solution 1 for Formalism.MainNotions.N.K.Norm.exists_equiv_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:23:31.813065+00:00
-- url     : https://prove2.me/submissions/d780e6e9-397e-4530-a789-50c91b89d0f6

import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_QuotientHomNonvanishingBound
import Definitions.Def_Formalism_AdmissibleDesigns_InvariantsEqBotIff
import Theorems.Thm_Formalism_MainNotions_N_K_Norm_matRep_apply
import Theorems.Thm_Formalism_MainNotions_N_K_Norm_matEquiv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module Formalism.WeaklyAdmissibleFiltrations TensorProduct
open Formalism Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.MainNotions.N.K.Norm
variable {Γ : Type} [Group Γ] {K : Type} [CommRing K] {k : ℕ}
namespace Formalism.MainNotions.N.K.Norm
theorem _root_.solution {M M' : Γ →* Matrix (Fin k) (Fin k) K} (h : IsConjM ⇑M ⇑M') :
    ∃ e : (Fin k → K) ≃ₗ[K] (Fin k → K), ∀ g v, e (matRep M g v) = matRep M' g (e v) := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  refine ⟨matEquiv P Q h1 h2, fun g v => ?_⟩
  rw [matEquiv_apply, matEquiv_apply, matRep_apply, matRep_apply, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h3]
end Formalism.MainNotions.N.K.Norm
