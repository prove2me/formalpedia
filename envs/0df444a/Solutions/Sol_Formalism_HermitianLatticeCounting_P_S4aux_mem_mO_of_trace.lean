-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.mem_mO_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:36.378154+00:00
-- url     : https://prove2.me/submissions/d1b0f451-0eb1-4d04-ad70-fc3115a5f952

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
variable {o O : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [CommRing O] [StarRing O]
  [Algebra o O]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (hU : Unram o O) (T : O →ₗ[o] o) (hT : ∀ a, algebraMap o O (T a) = a + star a)
    (z : O) (hz : ∀ s, T (s * z) ∈ IsLocalRing.maximalIdeal o) : z ∈ mO o O := by
  classical
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let b := Module.Free.chooseBasis o O
  rw [← b.sum_repr z]
  refine Ideal.sum_mem _ fun i _ => ?_
  obtain ⟨bi, hbi⟩ := hU.tr_perfect (b.coord i)
  have h1 := hbi z
  rw [mul_comm z (star bi), ← hT, Module.Basis.coord_apply] at h1
  rw [Algebra.smul_def, h1]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hz _))
end Formalism.HermitianLatticeCounting.P.S4aux
