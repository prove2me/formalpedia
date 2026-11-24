-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.charpoly_theta_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:47.758176+00:00
-- url     : https://prove2.me/submissions/4554b6b8-92fb-4038-a1a5-1e4bd43a7878

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_evaluation_congruence_holds
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_theta_base_change_holds
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_reduction_natCast_prime_eq_zero
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_constantCoeff_map_eq
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
theorem _root_.solution (l h : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ)
    (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c) (hN : LatW l W.N h u U') (i : ι) :
    (thetaOf (W.Gam i)).charpoly = ∏ j, (Polynomial.X -
      Polynomial.C (-W.red (algebraMap ℤ_[l] O c) * ((U' i j : ℤ) : F))) := by
  obtain ⟨-, -, -, hD, hTh⟩ := hN
  obtain ⟨r, hr, hcp⟩ := hTh i
  have h3 := (theta_base_change_holds F n W.unbar (W.g i)
    ((W.N.D i).map (PowerSeries.map W.red))).2.2
  have hD' : ((W.N.D i).map (PowerSeries.map W.red)).map constantCoeff = (W.N.Th i).map W.red := by
    ext a b
    simp only [Matrix.map_apply]
    rw [constantCoeff_map_eq]
    exact (evaluation_congruence_holds O (l : O) (W.N.Th i a b) (W.N.D i a b) (hD i a b)).2 F W.red
      (reduction_natCast_prime_eq_zero l W.red)
  show (thetaOf (chgGam W.unbar (W.g i) ((W.N.D i).map (PowerSeries.map W.red)))).charpoly = _
  rw [h3, hD', Matrix.charpoly_map, hcp, Polynomial.map_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    reduction_log_unit_pow_eq l W.red u c (r j) (U' i j) hu (hr j)]
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
