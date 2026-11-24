-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.norm_sq_c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:37.277175+00:00
-- url     : https://prove2.me/submissions/689c172a-0738-4c11-9d6f-1ef2491739ed

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance

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
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (x : V) :
    ((‖x‖ : ℝ) : ℂ) ^ 2 = inner ℂ x x := by
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) x]; rfl
end Formalism.HermitianLatticeCounting.P.S4aux
