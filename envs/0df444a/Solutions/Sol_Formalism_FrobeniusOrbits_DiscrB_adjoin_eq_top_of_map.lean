-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.DiscrB.adjoin_eq_top_of_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:22:17.749884+00:00
-- url     : https://prove2.me/submissions/f1ff9427-563a-4df4-8664-bfbd26bb772c

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_DirichletDensity_HostDensityArith
import Definitions.Def_Formalism_CMTypeGalois_HalfTypesFromGeneral
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_DiscrB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField NumberField.InfinitePlace
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.DiscrB
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L]
namespace Formalism.FrobeniusOrbits.DiscrB
theorem _root_.solution {K : Type} [Field K] [Algebra ℚ K] (ι : K →ₐ[ℚ] L) (S : Set K)
    (T : IntermediateField ℚ L) (hS : adjoin ℚ (ι '' S) = T) (hx : ∀ x : K, ι x ∈ T) :
    adjoin ℚ S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h2 : ι x ∈ (adjoin ℚ S).map ι := by
    rw [IntermediateField.adjoin_map, hS]
    exact hx x
  obtain ⟨y, hy, hyx⟩ := h2
  rwa [← (ι : K →+* L).injective hyx]
end Formalism.FrobeniusOrbits.DiscrB
