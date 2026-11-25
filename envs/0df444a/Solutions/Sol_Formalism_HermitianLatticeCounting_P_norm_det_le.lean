-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.norm_det_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:56.512106+00:00
-- url     : https://prove2.me/submissions/598a4232-0b2b-4f47-b04c-ca9ea6ab6ade

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MinkowskiNumberDvdFactorial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) (β : ℝ) (hM : ∀ i j, ‖M i j‖ ≤ β) :
    ‖M.det‖ ≤ (n.factorial : ℝ) * β ^ n := by
  rw [Matrix.det_apply]
  calc ‖∑ σ : Equiv.Perm (Fin n), Equiv.Perm.sign σ • ∏ i, M (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), β ^ n := by
        apply Finset.sum_le_sum
        intro σ _
        have h1 : ‖Equiv.Perm.sign σ • ∏ i, M (σ i) i‖ = ‖∏ i, M (σ i) i‖ := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [h1, norm_prod]
        calc ∏ i, ‖M (σ i) i‖ ≤ ∏ _i : Fin n, β :=
              Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hM _ _)
          _ = β ^ n := by simp
    _ = (n.factorial : ℝ) * β ^ n := by
        simp [Fintype.card_perm]
end Formalism.HermitianLatticeCounting.P
