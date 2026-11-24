-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.unram_uniq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:39.751244+00:00
-- url     : https://prove2.me/submissions/b88c1227-58cf-4958-9f25-cf9b41594b48

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
theorem _root_.solution (hU : Unram o O) (c : O) (hc : ∀ a : O, a * c + star (a * c) = 0) : c = 0 := by
  classical
  have := hU.free
  have : Module.Finite o O := Module.finite_of_finrank_pos (by rw [hU.rank2]; norm_num)
  let b := Module.Free.chooseBasis o O
  rw [← b.sum_repr c]
  refine Finset.sum_eq_zero fun i _ => ?_
  obtain ⟨bi, hbi⟩ := hU.tr_perfect (b.coord i)
  have h1 := hbi c
  rw [mul_comm c (star bi), hc (star bi), Module.Basis.coord_apply] at h1
  rw [Algebra.smul_def, h1, zero_mul]
end Formalism.HermitianLatticeCounting.P.S4aux
