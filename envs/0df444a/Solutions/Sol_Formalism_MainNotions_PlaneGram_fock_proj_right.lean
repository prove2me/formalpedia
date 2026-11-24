-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.fock_proj_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:05:23.46+00:00
-- url     : https://prove2.me/submissions/159ec880-f9c3-4011-8475-b2d3c3349f4a

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_comm
import Theorems.Thm_Formalism_MainNotions_PlaneGram_fock_sub_left


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
variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}
variable {L : Type} [Fintype L] [DecidableEq L] (sg : L → Bool) {r : ℕ} [NeZero r] (d : L → ℕ)
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution {W : Set (MvPolynomial (L × Fin r) K)}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d W π) {A G : MvPolynomial (L × Fin r) K}
    (hA : A ∈ PolK K r d) (hAW : A ∈ W) (hG : G ∈ PolK K r d) : fock A (π G) = fock A G := by
  have h := (hπ G hG).2.2.2 A hA hAW
  rw [fock_sub_left] at h
  rw [fock_comm A (π G), fock_comm A G]
  exact (sub_eq_zero.mp h).symm
end Formalism.MainNotions.PlaneGram
