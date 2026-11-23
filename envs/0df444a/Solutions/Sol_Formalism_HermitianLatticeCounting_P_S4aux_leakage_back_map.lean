-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.leakage_back_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:13.317334+00:00
-- url     : https://prove2.me/submissions/73fab9c6-c057-4e16-b945-54dbc552a58e

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_cast
import Theorems.Thm_Formalism_SL_P_SphereChartDerivatives_sn_last
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_cast
attribute [local simp] Formalism.SL.P.SphereChartDerivatives.sn_last



set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution : LeakBack := by
  intro E _ _ V _ _ h O abelian₂ x x' u y v y' m' s c hI hu hm h1 h2
  refine ⟨fun he => ?_, ?_⟩
  · have e : h v u = h m' u := by
      have := congrArg (fun z => h z u) he
      simpa [h1, h2] using this
    exact ⟨e, e ▸ hI _ hm _ hu⟩
  · have l : ∀ a b : V, eich h x u s (eich h x' u s (a + c • b)) = eich h x u s (eich h x' u s a) + c • eich h x u s (eich h x' u s b) := by
      intro a b
      have := ((eichLin h x u s).comp (eichLin h x' u s)).map_add a (c • b)
      rw [((eichLin h x u s).comp (eichLin h x' u s)).map_smul] at this
      exact this
    rw [l]; module
end Formalism.HermitianLatticeCounting.P.S4aux
