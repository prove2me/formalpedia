-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.unram_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:34:20.134007+00:00
-- url     : https://prove2.me/submissions/a868c7ce-f250-4215-bddf-d7382c520c0a

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_one
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
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hU : Unram o O) : ∃ T : O →ₗ[o] o, ∀ a, algebraMap o O (T a) = a + star a := by
  obtain ⟨l, hl⟩ := unram_one hU
  obtain ⟨b0, hb0⟩ := hU.tr_perfect l
  let sl : O →ₗ[o] O :=
    { toFun := star
      map_add' := star_add
      map_smul' := fun c a => by
        simp only [Algebra.smul_def, star_mul', hU.star_o, RingHom.id_apply] }
  have h1 : star b0 + b0 = 1 := by
    have := hb0 1
    rw [hl, map_one, one_mul, star_star] at this
    exact this.symm
  refine ⟨l + l ∘ₗ sl, fun a => ?_⟩
  rw [LinearMap.add_apply, LinearMap.comp_apply, map_add, hb0, hb0]
  change a * star b0 + star (a * star b0) + (star a * star b0 + star (star a * star b0)) = _
  simp only [star_mul', star_star]
  linear_combination (a + star a) * h1
end Formalism.HermitianLatticeCounting.P.S4aux
