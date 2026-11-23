-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.S4aux.Part2.leakProb
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:58:58.067553+00:00
-- url     : https://prove2.me/submissions/12cb5b96-e350-4c39-9fc8-747a3c11105d

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
open Formalism.HermitianLatticeCounting.P.S4aux.Part2
namespace Formalism.HermitianLatticeCounting.P.S4aux.Part2
theorem _root_.solution : LeakProb := by
  intro S _ _ P n
  have e : {u : Fin n → S // ∀ k, u k ∈ P} ≃ (Fin n → P) :=
    { toFun := fun u k => ⟨u.1 k, u.2 k⟩
      invFun := fun u => ⟨fun k => (u k).1, fun k => (u k).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_fin, ← mul_pow]
  congr 1
  have := Submodule.card_eq_card_quotient_mul_card P
  rw [this, mul_comm]
end Formalism.HermitianLatticeCounting.P.S4aux.Part2
