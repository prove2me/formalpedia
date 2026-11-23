-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.tauKer
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:16.070496+00:00
-- url     : https://prove2.me/submissions/32a833d3-19cf-4c24-a867-4ccb71d6a163

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_sum_mem_lat
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
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution (H : SpanCharRing) : TauKer := by
  intro E _ V _ _ O abelian₂ θ hθ hL n f f' hli hf' a a' w
  refine ⟨fun hw hmem => ?_, fun hw => ⟨by simpa using hw, by simpa using hw, ⟨0, abelian₂.zero_mem, by simp⟩⟩⟩
  have e : (∑ i, a' i • f' i) - (∑ i, a i • f i) = (∑ i, (-a i) • f i) + (∑ i, a' i • f' i) := by
    simp only [neg_smul, Finset.sum_neg_distrib]; abel
  rw [e] at hmem
  have h := (H E V O θ hθ n f f' hli (fun i => -a i) a').mp hmem
  have := abelian₂.sub_mem hw (sum_mem_lat hL hf' (fun i => (h i).1))
  simpa using this
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
