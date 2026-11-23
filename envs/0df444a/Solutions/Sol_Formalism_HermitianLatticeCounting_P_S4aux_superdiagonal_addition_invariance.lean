-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.superdiagonal_addition_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:26.811803+00:00
-- url     : https://prove2.me/submissions/295ff33e-987b-45e1-9f0f-c8596f68dc5d

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
theorem _root_.solution : SuperDiagAdd := by
  intro R _ n A B hA hA1 hB hB1 j
  rw [Matrix.mul_apply, Finset.sum_eq_add_of_mem j.castSucc j.succ (Finset.mem_univ _) (Finset.mem_univ _)]
  · rw [hA1, hB1]; ring
  · intro hh; have := congrArg Fin.val hh; simp at this
  · intro k _ ⟨h1, h2⟩
    by_cases hk : k < j.castSucc
    · rw [hA _ _ hk, zero_mul]
    · have : j.succ < k := by
        rw [Fin.lt_def] at hk ⊢
        have a1 : k.val ≠ j.val := fun e => h1 (Fin.ext (by simpa using e))
        have a2 : k.val ≠ j.val + 1 := fun e => h2 (Fin.ext (by simpa using e))
        simp at hk ⊢; omega
      rw [hB _ _ this, mul_zero]
end Formalism.HermitianLatticeCounting.P.S4aux
