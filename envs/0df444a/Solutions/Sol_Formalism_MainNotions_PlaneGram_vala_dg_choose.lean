-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.vala_dg_choose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:37:04.867055+00:00
-- url     : https://prove2.me/submissions/d01f63dc-3571-4a5b-bf08-61efaf86ef05

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MemPolKIff
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_mul
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_pow
import Theorems.Thm_Formalism_MainNotions_PlaneGram_vala_X
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_vala_ddiv_letter__58971d2a3a04
import Theorems.Thm_Formalism_MainNotions_PlaneGram_dg_choose_eq

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
namespace Formalism.MainNotions.PlaneGram
theorem _root_.solution (hV2 : V2 K) {θ : ℝ} (x : L × Fin r) (k : ℕ)
    {F : MvPolynomial (L × Fin r) K} (hF : vala sg S θ F) :
    vala sg S (θ - k) (dg (fun α => ((α x).choose k : K)) F) := by
  rw [dg_choose_eq]
  have hs : Finsupp.single x k = onLetter x.1 (Finsupp.single x.2 k) := by
    unfold onLetter
    rw [Finsupp.mapDomain_single]
  have habs : absE (Finsupp.single x.2 k) = k := by
    unfold absE
    rw [Finsupp.sum_single_index rfl]
  have h1 := vala_ddiv_letter' hV2 x.1 (Finsupp.single x.2 k) hF
  rw [← hs, habs] at h1
  have h2 : vala sg S (k * (if sg x.1 then 0 else -1 : ℝ))
      (monomial (Finsupp.single x k) (1 : K)) := by
    rw [← X_pow_eq_monomial]
    exact vala_pow (vala_X hV2 x.1 x.2) k
  have h3 := vala_mul h2 h1
  convert h3 using 1
  split_ifs <;> ring
end Formalism.MainNotions.PlaneGram
