-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.tauLin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:16.393509+00:00
-- url     : https://prove2.me/submissions/5df12f46-eb11-4b0c-97e1-e6e44e81b118

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_inTh_add
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_Part2_inTh_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P Formalism.HermitianLatticeCounting.P.S4aux
open Formalism.HermitianLatticeCounting.S4 Formalism.SL.IwahoriBlocks Finset
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution : TauLin := by
  intro E _ V _ _ O abelian₂ th c w₁ w₂ la₁ la₁' la₂ la₂' hL hc h1 h2
  obtain ⟨a1, b1, c1⟩ := h1
  obtain ⟨a2, b2, c2⟩ := h2
  refine ⟨?_, ?_, ?_⟩
  · have := abelian₂.add_mem (hL c hc _ a1) a2
    convert this using 1
    rw [smul_add]; abel
  · have := abelian₂.add_mem (hL c hc _ b1) b2
    convert this using 1
    rw [smul_add]; abel
  · have := inTh_add (inTh_smul hL hc c1) c2
    convert this using 1
    rw [smul_sub]; abel
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
