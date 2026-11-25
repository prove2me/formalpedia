-- Prove2me | solution 1 for Formalism.L2.Pj.LocAlg.aeval_qj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:10:01.621207+00:00
-- url     : https://prove2.me/submissions/8306e007-f7e1-492d-9c82-9439710f83a9

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_LocStructSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LocalIntegralPolynomials_ExistsValuationAdaptedIndex
import Theorems.Thm_Formalism_L2_Pj_LocAlg_sum_y_sImg

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
theorem _root_.solution (hy0 : yv jc x j0 ≠ 0) (p : TVar D N) :
    aeval (tj jc j0 x) (qj jc j0 x p) = sImg jc x p := by
  obtain ⟨i, j⟩ := p
  rcases Fin.eq_self_or_eq_succAbove j0 j with h | ⟨k, h⟩
  · rw [h]
    simp only [qj, Fin.insertNth_apply_same]
    split_ifs with hi
    · rw [hi, aeval_X]
      rfl
    · have hs := sum_y_sImg jc x hi
      rw [Fin.sum_univ_succAbove _ j0] at hs
      have hy : algebraMap Ω (OmS Ω D N) (yv jc x j0) ≠ 0 := (map_ne_zero _).mpr hy0
      have key : sImg jc x (i, j0) = -(∑ k, algebraMap Ω (OmS Ω D N) (yv jc x (j0.succAbove k)) *
          sImg jc x (i, j0.succAbove k)) / algebraMap Ω (OmS Ω D N) (yv jc x j0) := by
        rw [eq_div_iff hy]
        linear_combination hs
      simp only [map_neg, map_sum, map_mul, aeval_X, aeval_C, tj, Sum.elim_inr, map_div₀]
      rw [key, neg_div, Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
  · rw [h]
    simp only [qj, Fin.insertNth_apply_succAbove, aeval_X]
    rfl
end Formalism.L2.Pj.LocAlg
