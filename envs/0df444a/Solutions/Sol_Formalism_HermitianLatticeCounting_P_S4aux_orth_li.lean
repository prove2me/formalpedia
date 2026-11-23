-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.orth_li
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:06:35.157171+00:00
-- url     : https://prove2.me/submissions/ae34eb4e-eea2-4ae7-93d8-d33905145d80

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_orth_pair_left
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
variable {O : Type} [CommRing O] [StarRing O] {abelian₂ : Type} [AddCommGroup abelian₂] [Module O abelian₂]
  (h : abelian₂ →ₗ[O] abelian₂ →ₗ⋆[O] O)
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution {κ : Type} [Fintype κ] (v : κ → abelian₂) (horth : ∀ i j, i ≠ j → h (v i) (v j) = 0)
    (hunit : ∀ i, IsUnit (h (v i) (v i))) : LinearIndependent O v := by
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have h1 : h (∑ i, g i • v i) (v j) = 0 := by rw [hg]; simp
  rw [orth_pair_left, Finset.sum_eq_single j (fun i _ hi => by rw [horth i j hi, mul_zero])
    (fun hj => absurd (Finset.mem_univ _) hj)] at h1
  exact (hunit j).mul_left_eq_zero.1 h1
end Formalism.HermitianLatticeCounting.P.S4aux
