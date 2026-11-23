-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.isotropic_complement
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:12.646436+00:00
-- url     : https://prove2.me/submissions/c95332b1-135e-4642-aa9f-447a998ce715

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
theorem _root_.solution : IsoComplement := by
  intro E _ _ V _ _ h O abelian₂ r e y hH htr hI he hy hd
  have hg : ∀ j k, h (y j) (y k) ∈ O := fun j k => hI _ (hy j) _ (hy k)
  have hdiag : ∀ j, ∃ s ∈ O, s + star s = h (y j) (y j) := fun j => htr _ (hg j j) (hH _ _).symm
  choose s hs hss using hdiag
  refine ⟨fun j l => if j < l then h (y j) (y l) else if j = l then s j else 0, fun j l => ?_, fun j k => ?_⟩
  · dsimp only
    split_ifs
    · exact hg j l
    · exact hs j
    · exact O.zero_mem
  · set c : Fin r → Fin r → E := fun j l => if j < l then h (y j) (y l) else if j = l then s j else 0 with hc
    have hd' : ∀ i j, h (e i) (y j) = if i = j then 1 else 0 := by
      intro i j; rw [hH (y j) (e i), hd]; split_ifs <;> simp
    have expand : h (y j - ∑ l, c j l • e l) (y k - ∑ l, c k l • e l)
        = h (y j) (y k) - star (c k j) - c j k := by
      simp only [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, map_smul,
        LinearMap.smul_apply, LinearMap.map_smulₛₗ, he, hd, hd', smul_eq_mul, starRingEnd_apply]
      simp
      ring
    rw [expand]
    rcases lt_trichotomy j k with hjk | hjk | hjk
    · have h1 : c j k = h (y j) (y k) := by simp [hc, hjk]
      have h2 : c k j = 0 := by simp [hc, hjk.not_gt, hjk.ne']
      rw [h1, h2]; simp
    · subst hjk
      have h1 : c j j = s j := by simp [hc]
      rw [h1, ← hss j]; ring
    · have h1 : c j k = 0 := by simp [hc, hjk.not_gt, hjk.ne']
      have h2 : c k j = h (y k) (y j) := by simp [hc, hjk]
      rw [h1, h2, ← hH]; simp
end Formalism.HermitianLatticeCounting.P.S4aux
