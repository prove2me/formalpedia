-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.involution_well_defined
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:31:48.118084+00:00
-- url     : https://prove2.me/submissions/d35abc99-18b0-40ad-92a4-aa065338bb6f

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
theorem _root_.solution : TauWell := by
  intro E _ _ V _ _ h O abelian₂ th r f f' g c c' hL hI hg hd hf hc' ⟨w, hw, he⟩ j
  choose t ht hte using hf
  have key : ∑ i, (c' i - c i) • f i = th • (w - ∑ i, c' i • t i) := by
    have : ∑ i, (c' i - c i) • f i = (∑ i, c' i • f' i - ∑ i, c i • f i) - ∑ i, c' i • (f' i - f i) := by
      simp only [sub_smul, smul_sub, Finset.sum_sub_distrib]; abel
    rw [this, he, smul_sub, Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by rw [hte i, smul_comm]
  have hm : w - ∑ i, c' i • t i ∈ abelian₂ := abelian₂.sub_mem hw (abelian₂.sum_mem fun i _ => hL _ (hc' i) _ (ht i))
  refine ⟨h (w - ∑ i, c' i • t i) (g j), hI _ hm _ (hg j), ?_⟩
  have := congrArg (fun z => h z (g j)) key
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hd, smul_eq_mul] at this
  simpa using this
end Formalism.HermitianLatticeCounting.P.S4aux
