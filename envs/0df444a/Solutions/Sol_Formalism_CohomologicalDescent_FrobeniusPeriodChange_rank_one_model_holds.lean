-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.rank_one_model_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:05:01.130601+00:00
-- url     : https://prove2.me/submissions/b8744ba2-9d28-47b7-8a8e-8db1c8073c53

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_evaluation_congruence_holds
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_reduction_log_unit_pow_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]
namespace Formalism.CohomologicalDescent.FrobeniusPeriodChange
theorem _root_.solution : RankOneModel := by
  intro ι l h _ O F _ _ _ _ red N u c wt hu hN i
  obtain ⟨-, -, hdet, hD, hTh⟩ := hN
  refine ⟨?_, ?_⟩
  · obtain ⟨v, hv⟩ := hdet i
    refine ⟨v, ?_⟩
    rw [Matrix.det_fin_one, Fin.sum_univ_one] at hv
    exact hv
  · obtain ⟨r, hr, hcp⟩ := hTh i
    have h1 : (N.Th i).charpoly = Polynomial.X - Polynomial.C (N.Th i 0 0) := by
      show (Matrix.charmatrix (N.Th i)).det = _
      rw [Matrix.det_fin_one, Matrix.charmatrix_apply_eq]
    rw [h1, Fin.prod_univ_one] at hcp
    have h2 := congrArg (fun p => Polynomial.coeff p 0) hcp
    simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero, zero_sub,
      neg_inj] at h2
    have h3 := (evaluation_congruence_holds O (l : O) (N.Th i 0 0) (N.D i 0 0) (hD i 0 0)).2 F red
      (by rw [map_natCast, CharP.cast_eq_zero])
    rw [h3, h2, reduction_log_unit_pow_eq l red u c (r 0) (wt i) hu (hr 0)]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
