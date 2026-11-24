-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.unram_fixed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:39.438672+00:00
-- url     : https://prove2.me/submissions/646c1285-8bf8-415e-b91a-a88c6179a8b8

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_unram_trace

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
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hU : Unram o O) (y : O) (hy : star y = y) : ∃ t : o, algebraMap o O t = y := by
  obtain ⟨T, hT⟩ := unram_trace hU
  obtain ⟨s, hs⟩ := hU.tr_onto 1
  refine ⟨T (y * s), ?_⟩
  rw [hT, star_mul', hy, ← mul_add, hs, map_one, mul_one]
end Formalism.HermitianLatticeCounting.P.S4aux
