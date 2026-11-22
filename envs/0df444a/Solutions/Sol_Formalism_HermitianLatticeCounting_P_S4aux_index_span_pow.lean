-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.index_span_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:29:12.246359+00:00
-- url     : https://prove2.me/submissions/fc9dd635-7250-4c63-91c9-78263948f5e7

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
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o]
namespace Formalism.HermitianLatticeCounting.P.S4aux
theorem _root_.solution (ϖ : o) (hϖ : Irreducible ϖ) (q : ℕ)
    (hq : Nat.card (IsLocalRing.ResidueField o) = q) (i : ℕ) :
    (Ideal.span {ϖ ^ i}).toAddSubgroup.index = q ^ i := by
  have h1 := cardQuot_pow_of_prime (P := IsLocalRing.maximalIdeal o)
    (IsDiscreteValuationRing.not_a_field o) (i := i)
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at h1
  have h2 : Submodule.cardQuot (Ideal.span {ϖ}) = q := by
    rw [← hq, ← hϖ.maximalIdeal_eq]; rfl
  rw [h2] at h1
  exact h1
end Formalism.HermitianLatticeCounting.P.S4aux
