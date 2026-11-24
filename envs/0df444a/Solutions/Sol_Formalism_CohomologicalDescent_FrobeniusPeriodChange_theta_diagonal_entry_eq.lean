-- Prove2me | solution 1 for Formalism.CohomologicalDescent.FrobeniusPeriodChange.theta_diagonal_entry_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:40.192068+00:00
-- url     : https://prove2.me/submissions/49286f9e-c48c-453a-a9c2-8a65a1d2171c

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_unit_series_constant_holds
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_theta_diagonal_holds
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_constantCoeff_map_eq
import Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_rank_one_model_holds

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
theorem _root_.solution (l h : ℕ) [Fact l.Prime] [IsDomain O] [Algebra ℤ_[l] O] [CharP F l]
    (W : WLat ι t n O F) (σ : Equiv.Perm ι) (u : ℤ_[l]ˣ) (c : ℤ_[l]) (U' : ι → Fin n → ℤ)
    (wt kap : ι → Fin t → ℤ) (hl2 : l ≠ 2) (hW : WInputs W σ l h u c U' wt kap) (i : ι)
    (s : Fin t) :
    thetaOf (W.Gam i) (W.pos s) (W.pos s) =
      -W.red (algebraMap ℤ_[l] O c) * ((wt i s - kap i s : ℤ) : F) := by
  obtain ⟨⟨hu, -, hun⟩, -, -, -, -, -, -, hGamE⟩ := hW.1
  obtain ⟨-, hD⟩ := rank_one_model_holds ι l h O F W.red (W.Npsi s) u c (fun i => wt i s) hu
    (hW.2.2 s) i
  obtain ⟨-, hcc1⟩ := theta_diagonal_holds F W.unbar (PowerSeries.map W.red ((W.Npsi s).D i 0 0))
    (W.Gam i (W.pos s) (W.pos s)) (W.w i s) (kap i s) (hGamE i s)
  obtain ⟨e, he⟩ := ((unit_series_constant_holds l O hl2 (u : ℤ_[l]) c hu).2 W.un hun).2
  show coeff 1 (W.Gam i (W.pos s) (W.pos s)) = _
  rw [hcc1]
  unfold WLat.unbar
  rw [constantCoeff_map_eq, constantCoeff_map_eq, hD, he, map_add, map_mul, map_natCast,
    CharP.cast_eq_zero, zero_mul, add_zero]
  push_cast
  ring
end Formalism.CohomologicalDescent.FrobeniusPeriodChange
