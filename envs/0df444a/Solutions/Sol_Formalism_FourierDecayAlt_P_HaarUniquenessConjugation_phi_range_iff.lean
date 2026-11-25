-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HaarUniquenessConjugation.phi_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:47:13.145237+00:00
-- url     : https://prove2.me/submissions/7dc207a2-2495-4138-8a96-b2b71d00e7be

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_LiftErrorLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HaarUniquenessConjugation
import Theorems.Thm_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_conj_back
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_HaarUniquenessConjugation_conj_back__c41ce8b27066

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
variable {ε : Fin (2 * r + k + 1) → Bool} {P : Mat k r}
namespace Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
theorem _root_.solution (hE : UJEmb) (hC : UHConj) (hP : IsUnit P.det) (hH : Pᴴ * Jm ε * P = Hpk k r) (g : Mat k r) :
    (∃ u, phi ε P u = g) ↔ g ∈ GV k r := by
  constructor
  · rintro ⟨u, hu⟩
    have : (P⁻¹ * ((u : (Mat k r)ˣ) : Mat k r) * P : Mat k r) = g := hu
    rw [← this]
    refine (hC _ ε _ P hP hH _).2 ?_
    rw [conj_back hP]
    exact u.2
  · intro hg
    have h1 : inUJ ε (P * g * P⁻¹) := (hC _ ε _ P hP hH g).1 hg
    have h2 : P * g * P⁻¹ ∈ Set.range (fun g : UJ ε => ((g : (Mat k r)ˣ) : Mat k r)) := by
      rw [(hE _ ε).2]; exact h1
    obtain ⟨u, hu⟩ := h2
    refine ⟨u, ?_⟩
    show P⁻¹ * _ * P = g
    have hu' : ((u : (Mat k r)ˣ) : Mat k r) = P * g * P⁻¹ := hu
    rw [hu', conj_back' hP]
end Formalism.FourierDecayAlt.P.HaarUniquenessConjugation
