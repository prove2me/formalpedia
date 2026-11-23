-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.hj_exists_omega
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:01:12.446199+00:00
-- url     : https://prove2.me/submissions/cc1afbe8-e6e3-4f74-b170-383318490de8

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
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] [StarRing E]
omit [StarRing E]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (h2 : Module.finrank F E = 2) : ∃ ω : E, ∀ c : F, algebraMap F E c ≠ ω := by
  by_contra hcon
  push Not at hcon
  have := finrank_le_one (R := F) (1 : E) (fun w => by
    obtain ⟨c, hc⟩ := hcon w
    exact ⟨c, by rw [Algebra.smul_def, mul_one, hc]⟩)
  omega
end Formalism.HermitianLatticeCounting.P.S4aux
