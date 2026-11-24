-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.card_of_surj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:21.159126+00:00
-- url     : https://prove2.me/submissions/3da9452f-ab22-4b95-a7de-b99feef1e52c

import Definitions.Def_Formalism_FlagUnipotentLattices_PairingOrthogonalComplement
import Definitions.Def_Formalism_SobolevGaussianKernels_KernelBoundRel
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SuperdiagonalAdditionInvariance
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_S4aux_index_span_pow

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
    (hq : Nat.card (IsLocalRing.ResidueField o) = q) (i : ℕ) {G : Type} [AddCommGroup G]
    (f : o →+ G) (hf : Function.Surjective f) (hk : ∀ x, f x = 0 ↔ ϖ ^ i ∣ x) :
    Nat.card G = q ^ i := by
  have hker : f.ker = (Ideal.span {ϖ ^ i}).toAddSubgroup := by
    ext x
    rw [AddMonoidHom.mem_ker, hk, Submodule.mem_toAddSubgroup, Ideal.mem_span_singleton]
  rw [← index_span_pow ϖ hϖ q hq i, ← hker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 hf]
  exact (Nat.card_congr (Equiv.Set.univ G)).symm
end Formalism.HermitianLatticeCounting.P.S4aux
