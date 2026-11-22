-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.orth_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:06:36.708806+00:00
-- url     : https://prove2.me/submissions/d2139ae1-f81c-48bd-a890-90ca7c4894b3

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
theorem _root_.solution {U T : Type} [Fintype U] [AddCommGroup T] [Fintype T] [DecidableEq T]
    (Q : U → T) (f : U → ℂ) :
    (∑ u ∈ univ.filter (fun u => Q u = 0), f u) * (Fintype.card T : ℂ)
      = ∑ ψ : AddChar T ℂ, ∑ u, ψ (Q u) * f u := by
  rw [Finset.sum_comm, Finset.sum_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [← Finset.sum_mul, AddChar.sum_apply_eq_ite]
  split_ifs <;> ring
end Formalism.HermitianLatticeCounting.P.S4aux
