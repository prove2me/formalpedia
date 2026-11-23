-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.move_preserves_weight
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:06:35.127059+00:00
-- url     : https://prove2.me/submissions/439a09b6-52a5-4876-8b06-cd285a50eaea

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
theorem _root_.solution : MoveWeight := by
  intro E _ _ V _ _ h r f co al u s J hco hal hf hu
  have hx : ∀ i, h (f i) (∑ k, al k • f k) = 0 := by
    intro i
    rw [map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [LinearMap.map_smulₛₗ]
    by_cases hk : k.val ≤ J.val
    · simp [hf i k hk]
    · simp [hal k (by omega)]
  have hcx : ∀ k, co k (∑ i, al i • f i) = al k := by
    intro k; simp [map_sum, hco]
  have : ∀ j : Fin r, co j.castSucc (eich h (∑ i, al i • f i) u s (f j.succ)) = h (f j.succ) u * al j.castSucc := by
    intro j
    simp only [eich, hx, zero_smul, sub_zero, map_add, map_smul, hcx, hco, smul_eq_mul]
    have : j.succ ≠ j.castSucc := by
      intro hh; have := congrArg Fin.val hh; simp at this
    simp [this]
  simp only [this]
  rw [Finset.sum_eq_single J]
  · ring
  · intro j _ hj
    rcases lt_or_gt_of_ne (fun hh => hj (Fin.ext hh) : j.val ≠ J.val) with hlt | hgt
    · rw [hu j.succ (by simp; omega)]; ring
    · rw [hal j.castSucc (by simpa using hgt)]; ring
  · simp
end Formalism.HermitianLatticeCounting.P.S4aux
