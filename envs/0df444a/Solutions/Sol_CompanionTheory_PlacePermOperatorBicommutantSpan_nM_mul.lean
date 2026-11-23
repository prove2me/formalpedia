-- Prove2me | solution 1 for CompanionTheory.PlacePermOperatorBicommutantSpan.nM_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:35:54.75498+00:00
-- url     : https://prove2.me/submissions/dbc43e36-cdf9-4c1e-bb1f-495d4c7149b6

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_AutomorphicTheory_ThetaDilations_ParAlg
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_pm_mul
import Theorems.Thm_CompanionTheory_PlacePermOperatorBicommutantSpan_hform_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW Matrix
noncomputable section
open CompanionTheory CompanionTheory.PlacePermOperatorBicommutantSpan
variable {K : Type} [CommRing K] {M : ℕ}
variable (s : K →+* K) (J : Matrix (Fin M) (Fin M) K)
variable {s J}
namespace CompanionTheory.PlacePermOperatorBicommutantSpan
theorem _root_.solution (w w' : Fin M → K) (z z' : K) :
    nM s J w z * nM s J w' z' = nM s J (w + w') (z + z' - hform s J w w') := by
  have e : (s : K → K) ∘ (w + w') = s ∘ w + s ∘ w' := funext fun _ => map_add s _ _
  simp only [nM, pm_mul, hform_eq, e, add_vecMul]
  congr 1 <;> simp <;> ring
end CompanionTheory.PlacePermOperatorBicommutantSpan
