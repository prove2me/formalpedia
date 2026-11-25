-- Prove2me | solution 1 for Formalism.L2.Pj.LocAlg.qj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:10:19.915465+00:00
-- url     : https://prove2.me/submissions/13e72a70-34e0-4dd7-86c6-9d378590a94f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Theorems.Thm_Formalism_L2_Pj_LocAlg_C_mem_intPoly
import Theorems.Thm_Formalism_L2_Pj_LocAlg_X_mem_intPoly

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LocAlg
open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial
variable {Ω : Type} [Field Ω] {D N : ℕ}
variable {jc j0 : Fin (N + 1)} {x : Fin N → Ω}
namespace Formalism.L2.Pj.LocAlg
theorem _root_.solution {W : Subring Ω} (hyW : ∀ j, yv jc x j / yv jc x j0 ∈ W) (p : TVar D N) :
    qj jc j0 x p ∈ intPoly (SVar D N) W := by
  obtain ⟨i, j⟩ := p
  rcases Fin.eq_self_or_eq_succAbove j0 j with h | ⟨k, h⟩
  · rw [h]
    simp only [qj, Fin.insertNth_apply_same]
    split_ifs
    · exact X_mem_intPoly _
    · exact Subring.neg_mem _ (Subring.sum_mem _ fun k _ =>
        Subring.mul_mem _ (C_mem_intPoly (hyW _)) (X_mem_intPoly _))
  · rw [h]
    simp only [qj, Fin.insertNth_apply_succAbove]
    exact X_mem_intPoly _
end Formalism.L2.Pj.LocAlg
