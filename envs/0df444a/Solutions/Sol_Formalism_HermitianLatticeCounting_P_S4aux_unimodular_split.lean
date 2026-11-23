-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.unimodular_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:27.291943+00:00
-- url     : https://prove2.me/submissions/e7f3169d-aeb7-43dc-b418-0170885da34f

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_adj_mem
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_gram_pair
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
theorem _root_.solution : UnimodSplit := by
  intro E _ _ V _ _ h O m f hG ⟨d, hd, hdd⟩ v hp
  set G : Matrix (Fin m) (Fin m) E := Matrix.of fun a b => h (f a) (f b) with hGd
  have hadj := adj_mem O m G hG
  set p : Fin m → E := fun j => h v (f j) with hpd
  refine ⟨fun i => d * Matrix.vecMul p G.adjugate i, fun i => ?_, fun j => ?_⟩
  · refine O.mul_mem hd ?_
    simp only [Matrix.vecMul, dotProduct]
    exact O.sum_mem fun j _ => O.mul_mem (hp j) (hadj j i)
  · rw [map_sub, LinearMap.sub_apply, gram_pair]
    have h1 : Matrix.vecMul (Matrix.vecMul p G.adjugate) G = G.det • p := by
      rw [Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
    have h2 := congrFun h1 j
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have h3 : ∑ i, d * Matrix.vecMul p G.adjugate i * h (f i) (f j)
        = d * Matrix.vecMul (Matrix.vecMul p G.adjugate) G j := by
      conv_rhs => rw [Matrix.vecMul, dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc]; rfl
    rw [h3, h2, ← mul_assoc, hdd, one_mul, sub_self]
end Formalism.HermitianLatticeCounting.P.S4aux
