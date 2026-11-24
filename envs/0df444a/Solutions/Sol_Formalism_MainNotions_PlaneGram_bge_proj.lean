-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.bge_proj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:33:22.49659+00:00
-- url     : https://prove2.me/submissions/53f78a04-1b22-47a4-8ba8-8505bab8b888

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_FockMonomialRight
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Theorems.Thm_Formalism_MainNotions_PlaneGram_bge_iff


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
theorem _root_.solution (hP : PROJ K v p C0) (hD : DVRHyp v p) {S : Finset L} {th : ℤ}
    {π : MvPolynomial (L × Fin r) K →ₗ[K] MvPolynomial (L × Fin r) K}
    (hπ : IsFockProj (K := K) (r := r) d (Aset sg S th) π) {F : MvPolynomial (L × Fin r) K}
    (hF : F ∈ PolK K r d) {a : ℝ} (ha : bge v a F) :
    bge v (a - (r : ℝ) ^ 2 * lg p r (2 * ∑ i, d i)) (π F) := by
  rw [bge_iff] at ha ⊢
  have hb := ((hP hD L sg r d S th).2 π hπ).2.2 F hF
  have h2 := ha.trans hb
  generalize vBB v (π F) = x at h2 ⊢
  induction x using WithTop.recTopCoe with
  | top => exact le_top
  | coe x =>
    rw [← WithTop.coe_add, WithTop.coe_le_coe] at h2
    rw [WithTop.coe_le_coe]
    linarith
end Formalism.MainNotions.PlaneGram
