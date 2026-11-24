-- Prove2me | solution 1 for Formalism.DivisionValues.GluingInclusion.loc_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:20.563619+00:00
-- url     : https://prove2.me/submissions/41880ae6-b854-42ad-90a3-3146e2f6b7db

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ReductionSecondStep
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_SecondStepGluing
import Theorems.Thm_Formalism_DivisionValues_GluingInclusion_conjIdeal_eq
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_mem_locS


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
open Formalism.DivisionValues.GluingInclusion
open Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K]
namespace Formalism.DivisionValues.GluingInclusion
theorem _root_.solution (w : HeightOneSpectrum (𝓞 K)) {d : ℕ} (A : Submodule (𝓞 K) (Fin d → K)) :
    loc (K := K) w.asIdeal A = localization₂ w.asIdeal A ⊓ localization₂ (conjPl w).asIdeal A := by
  obtain ⟨hp, h⟩ := (locBasic (𝓞 K) K (Fin d → K) (IsFractionRing.injective (𝓞 K) K)).2.2.2.2
    (fun r => ⟨cO K r, rfl⟩) w.asIdeal
  rw [h A]
  congr 1
  ext x
  unfold localization₂
  simp only [locBasic_mem_locS, Ideal.mem_primeCompl_iff, conjIdeal_eq]
end Formalism.DivisionValues.GluingInclusion
