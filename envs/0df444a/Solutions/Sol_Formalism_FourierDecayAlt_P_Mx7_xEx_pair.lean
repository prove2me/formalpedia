-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx7.xEx_pair
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:07.61484+00:00
-- url     : https://prove2.me/submissions/ad5eae20-efe4-4069-b184-41bd4e83e2e2

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MultiplicationOpHom
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EulerZetaGammaInvIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RaisingConstantEqNablaStar
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedSumDifferenceIdentity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx7
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
namespace Formalism.FourierDecayAlt.P.Mx7
theorem _root_.solution (P : Par) (π : Ty P) (Y : ℂ) (l j : ℕ) (hj : j ∈ Icc 1 (P.k - 1)) (hjl : j ≠ l) :
    xEx P {l} π Y = xEx P {l, j} π Y * (Y + (rho P π j : ℂ)) := by
  unfold xEx
  have hset : Icc 1 (P.k - 1) \ {l, j} = (Icc 1 (P.k - 1) \ {l}) \ {j} := by
    ext i; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]; tauto
  have hsub : ({j} : Finset ℕ) ⊆ Icc 1 (P.k - 1) \ {l} :=
    Finset.singleton_subset_iff.2 (Finset.mem_sdiff.2 ⟨hj, by simpa using hjl⟩)
  rw [hset]
  calc ∏ i ∈ Icc 1 (P.k - 1) \ {l}, (Y + (rho P π i : ℂ))
      = (∏ i ∈ (Icc 1 (P.k - 1) \ {l}) \ {j}, (Y + (rho P π i : ℂ))) * ∏ i ∈ {j}, (Y + (rho P π i : ℂ)) :=
        (Finset.prod_sdiff hsub).symm
    _ = _ := by rw [Finset.prod_singleton]
end Formalism.FourierDecayAlt.P.Mx7
