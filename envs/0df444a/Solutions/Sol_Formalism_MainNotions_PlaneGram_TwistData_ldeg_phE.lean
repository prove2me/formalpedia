-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.ldeg_phE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:08:53.951983+00:00
-- url     : https://prove2.me/submissions/3884a365-4f33-4e26-ab98-ae8056be7a59

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CollapseExponent
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_Monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_phE_apply_inl
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_phE_apply_inr

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
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution (p : ℕ) (ζ : D.EM) (h : D.GoodE p ζ) (i : D.OL) : ldeg (D.phE p ζ) i = D.dO i := by
  obtain ⟨-, -, h3, h4, -⟩ := h
  rcases i with b | t
  · simp only [ldeg, phE_apply_inl, dO, Sum.elim_inl]
    exact h3 b
  · simp only [ldeg, phE_apply_inr, dO, Sum.elim_inr, Finset.sum_add_distrib, ← Finset.mul_sum]
    exact h4 t
end Formalism.MainNotions.PlaneGram.TwistData
