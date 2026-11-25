-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.lowerBoundOfProdLengths
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:23.220384+00:00
-- url     : https://prove2.me/submissions/44ccc727-2cbe-400b-b102-2f0cbb6a12ad

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : LengthLower := by
  intro r l l' R Dr hl hl' hD b
  have hR : 0 ≤ R := ((hl' b).1.le).trans (hl' b).2
  have h1 : ∏ a, l a ≤ R ^ r := by
    calc ∏ a, l a ≤ ∏ _a : Fin r, R :=
          Finset.prod_le_prod (fun a _ => (hl a).1.le) (fun a _ => (hl a).2)
      _ = R ^ r := by simp
  have h2 : ∏ b', l' b' ≤ l' b * R ^ (r - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ l' (Finset.mem_univ b)]
    apply mul_le_mul_of_nonneg_left _ (hl' b).1.le
    calc ∏ b' ∈ Finset.univ.erase b, l' b' ≤ ∏ _b' ∈ Finset.univ.erase b, R :=
          Finset.prod_le_prod (fun a _ => (hl' a).1.le) (fun a _ => (hl' a).2)
      _ = R ^ (r - 1) := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ b), Finset.card_univ,
            Fintype.card_fin]
  have hr : 0 < r := Fin.pos b
  calc Dr ≤ (∏ a, l a) * ∏ b', l' b' := hD
    _ ≤ R ^ r * (l' b * R ^ (r - 1)) :=
        mul_le_mul h1 h2 (Finset.prod_nonneg (fun a _ => (hl' a).1.le)) (pow_nonneg hR _)
    _ = l' b * R ^ (2 * r - 1) := by
        rw [show 2 * r - 1 = r + (r - 1) by omega, pow_add]; ring
end Formalism.HermitianLatticeCounting.P
