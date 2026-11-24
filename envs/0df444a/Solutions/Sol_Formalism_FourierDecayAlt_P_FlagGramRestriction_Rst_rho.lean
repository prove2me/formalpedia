-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagGramRestriction.Rst_rho
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:28:26.896788+00:00
-- url     : https://prove2.me/submissions/c57513e9-69ee-409c-abcd-9800241962d2

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentUpperFacts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagGramRestriction
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_Hst_iff
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagGramRestriction_mulV
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_gram_det
import Theorems.Thm_Formalism_FourierDecayAlt_P_FixedPointsGramVector_mem_Uperp
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianProjections_eq_rhoOf
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_isUnit_of_uh


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.FlagGramRestriction
open C2x5 C2x6 C2x7 HermitianProjections FixedPointsGramVector UnipotentUpperFacts
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagGramRestriction
theorem _root_.solution {z z' : Fin (2 * r + k + 1) → ℂ} (hstd : C2.Std k r z z') {γ : B.Mat k r}
    (hpos : C2.PosPt k r z z' γ) {ρ : B.Mat k r} (hρ : ρ ∈ C2.Rst k r z z' γ) :
    ρ = rhoOf (Hpk k r) (gnB k r z z' γ) (PhiH k r z z' γ ρ) := by
  have hγ : IsUnit γ.det := WeylGroupFacts.isUnit_of_uh hpos.1
  obtain ⟨hs, hs'⟩ := (Hst_iff hγ ρ).mp hρ.1
  apply eq_rhoOf _ _ _ (gram_det z z' γ hstd hpos) ρ (mulV hstd hγ hs hs')
  intro x hx
  exact hρ.2 x ((mem_Uperp z z' γ x).mpr hx)
end Formalism.FourierDecayAlt.P.FlagGramRestriction
