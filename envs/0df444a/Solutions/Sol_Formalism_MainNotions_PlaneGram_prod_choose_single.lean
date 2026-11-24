-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.prod_choose_single
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:08:30.957082+00:00
-- url     : https://prove2.me/submissions/a471cbe2-16f4-419a-9d76-607c60feb1a1

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
variable {K : Type} [Field K] [CharZero K] {L : Type} [Fintype L] [DecidableEq L] {r : ℕ} [NeZero r]
  {sg : L → Bool} {S : Finset L}
omit [CharZero K] [Fintype L] [NeZero r]
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {σ : Type} (α : σ →₀ ℕ) (x : σ) (k : ℕ) (hk : k ≤ α x) :
    (α.prod fun y n => ((n.choose (Finsupp.single x k y) : ℕ) : K)) = ((α x).choose k : ℕ) := by
  classical
  unfold Finsupp.prod
  rw [Finset.prod_eq_single x]
  · dsimp only
    rw [Finsupp.single_eq_same]
  · intro y _ hy
    dsimp only
    rw [Finsupp.single_apply, if_neg (Ne.symm hy), Nat.choose_zero_right, Nat.cast_one]
  · intro hx
    have h0 : α x = 0 := Finsupp.notMem_support_iff.mp hx
    have hk0 : k = 0 := by omega
    dsimp only
    rw [Finsupp.single_eq_same, h0, hk0, Nat.choose_zero_right, Nat.cast_one]
end Formalism.MainNotions.PlaneGram
