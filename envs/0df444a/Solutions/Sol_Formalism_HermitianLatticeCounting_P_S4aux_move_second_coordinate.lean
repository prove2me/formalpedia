-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.move_second_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:06:35.143412+00:00
-- url     : https://prove2.me/submissions/22e9b02e-cad9-42d3-a124-9c9a17dec4e3

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
theorem _root_.solution : MoveY := by
  intro E _ _ V _ _ h O abelian₂ th x u y y' s hL hu hs h1 h2 h3
  have key : eich h x u s (y + y') = y + y' - h y' x • (u + s • x) := by
    simp only [eich, map_add, LinearMap.add_apply, h1, h2, h3]; module
  refine ⟨key, ?_, ?_⟩
  · rintro ⟨w, hw, he⟩ ⟨d, hd, hk⟩
    refine ⟨w - d • (u + s • x), abelian₂.sub_mem hw (hL d hd _ (abelian₂.add_mem hu hs)), ?_⟩
    rw [key, he, hk]; module
  · rintro ⟨t, rfl⟩ ⟨d, hd, hk⟩ w hw he
    change eichLin h x u s w ∈ abelian₂
    have h4 : (t : E) • eichLin h x u s w = (t : E) • (w - d • (u + s • x)) := by
      rw [← map_smul, he]; change eich h x u s (y + y') = _; rw [key, hk, ← he]; module
    have h5 : eichLin h x u s w = w - d • (u + s • x) := by
      have := congrArg (fun z => ((t⁻¹ : Eˣ) : E) • z) h4
      simpa [smul_smul] using this
    rw [h5]; exact abelian₂.sub_mem hw (hL d hd _ (abelian₂.add_mem hu hs))
end Formalism.HermitianLatticeCounting.P.S4aux
