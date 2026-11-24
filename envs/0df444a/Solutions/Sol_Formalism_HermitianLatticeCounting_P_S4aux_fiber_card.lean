-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:24.250037+00:00
-- url     : https://prove2.me/submissions/3ffedf67-bbcc-4144-b0d1-ccdbf50464d9

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_mulVec_surj
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
variable {F : Type} [Field F] [Fintype F]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution [DecidableEq F] {j n : ℕ} (M : Matrix (Fin j) (Fin n) F)
    (hM : LinearIndependent F M.row) (g : Fin j → F) :
    (univ.filter fun y : Fin n → F => M.mulVec y = g).card * Fintype.card F ^ j
      = Fintype.card F ^ n := by
  have hs := mulVec_surj M hM
  have heq : ∀ g', (univ.filter fun y : Fin n → F => M.mulVec y = g').card
      = (univ.filter fun y : Fin n → F => M.mulVec y = g).card := fun g' =>
    AddMonoidHom.card_fiber_eq_of_mem_range M.mulVecLin.toAddMonoidHom (hs g') (hs g)
  have h1 := Finset.card_eq_sum_card_fiberwise (f := M.mulVec) (s := (univ : Finset (Fin n → F)))
    (t := (univ : Finset (Fin j → F))) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  simp only [heq, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fun, Fintype.card_fin] at h1
  rw [h1, mul_comm]
end Formalism.HermitianLatticeCounting.P.S4aux
