-- Prove2me | solution 1 for Formalism.DivisionValues.second_step_gluing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:43:14.030694+00:00
-- url     : https://prove2.me/submissions/f9c44a04-297e-4a6f-8abc-7c36d55fe2c8

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_glueLat_spec
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_eq_of_localization_eq
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_loc_glueLat
import Theorems.Thm_Formalism_DivisionValues_StepBAux_matLat_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
open Formalism Formalism.DivisionValues
open GluingInclusion Formalism.HermitianLatticesTheory
namespace Formalism.DivisionValues
theorem _root_.solution : StepBGlue := by
  intro K _ _ _ D Tup μ0 μ hμc hμ abelian₂ hLam ι hι
  have hfin : {w : HeightOneSpectrum (𝓞 K) | localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w))) ≠
      localization₂ w.asIdeal (matLat (ι μ0) (abelian₂ μ0))}.Finite :=
    hμ.subset (fun w hw h => hw (by rw [h]))
  obtain ⟨hlat, hloc⟩ := glueLat_spec (matLat (ι μ0) (abelian₂ μ0))
    (fun w => matLat (ι (μ w)) (abelian₂ (μ w))) (StepBAux.matLat_lattice _ (hι _) _ (hLam _))
    (fun w => StepBAux.matLat_lattice _ (hι _) _ (hLam _)) hfin
  have huniq : ∀ R : Submodule (𝓞 K) (Fin D → K),
      (∀ w : HeightOneSpectrum (𝓞 K),
        localization₂ w.asIdeal R = localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
      R = glueLat (fun w => matLat (ι (μ w)) (abelian₂ (μ w))) :=
    fun R hR => eq_of_localization_eq _ _ (fun w => by rw [hR w, hloc w])
  refine ⟨⟨_, hloc, huniq⟩, ?_⟩
  intro R hR
  refine ⟨?_, huniq R hR, ?_, ?_⟩
  · rw [huniq R hR]
    exact hlat
  · exact loc_glueLat (fun w => matLat (ι (μ w)) (abelian₂ (μ w))) (fun w => by simp only [hμc w]) R hR
  · refine hfin.subset (fun w hw => ?_)
    rw [Set.mem_ofPred_eq, hR w] at hw
    exact hw
end Formalism.DivisionValues
