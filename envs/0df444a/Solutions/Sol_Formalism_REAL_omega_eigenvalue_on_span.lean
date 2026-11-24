-- Prove2me | solution 1 for Formalism.REAL.omega_eigenvalue_on_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:16:02.490809+00:00
-- url     : https://prove2.me/submissions/612e0c3a-6353-41b6-87a1-19f4aa66bc15

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementU
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_NoncompactArrFiniteDimensional
import Theorems.Thm_Formalism_REAL_noncompact_arr_one_values
import Theorems.Thm_Formalism_REAL_compact_span_le_of_stable
import Theorems.Thm_Formalism_REAL_noncompact_arr_one_compact_stable
import Theorems.Thm_Formalism_REAL_compact_casimir_positions_one
import Theorems.Thm_Formalism_REAL_glRel_kRel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open Finset
noncomputable section
open Formalism Formalism.REAL
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution (hk : KCasSpan) (hca : CasArr) (ha : ArrModule) {ε : Fin n → Bool}
    {E : Fin n → Fin n → Module.End ℂ V} {Λ μ : Fin n → ℝ} {u : V} {y : Arr V n 1}
    (hg : GlRel E) (hΛ : KHighest ε E Λ u) (hy : y ∈ arrV0 ε E u 1)
    (hyh : KHighest ε (arrE E 1) μ y) {G : Arr V n 1} (hG : G ∈ kSpan ε (arrE E 1) y) :
    OmS ε E (0 : Fin 1) G = (((ckv ε μ - n - ckv ε Λ) / 2 : ℝ) : ℂ) • G := by
  have hKR := glRel_kRel ε _ ((ha V n ε E 1).1 hg).1
  have hGS : G ∈ arrV0 ε E u 1 := compact_span_le_of_stable noncompact_arr_one_compact_stable hy hG
  have h1 := (hca V n ε E Λ u 1).1 hg hΛ G hGS
  have h2 := hk (Arr V n 1) n ε (arrE E 1) μ y hKR hyh G hG
  have h3 := compact_casimir_positions_one G (fun a b h => (noncompact_arr_one_values hGS a b).2 h)
  rw [h2, h3, Fin.sum_univ_one] at h1
  have h4 : (2 : ℂ) • OmS ε E (0 : Fin 1) G = ((ckv ε μ : ℂ) - n - ckv ε Λ) • G := by
    rw [sub_smul, sub_smul, h1]; abel
  calc OmS ε E (0 : Fin 1) G = (1 / 2 : ℂ) • ((2 : ℂ) • OmS ε E (0 : Fin 1) G) := by
        rw [smul_smul]; norm_num
    _ = (((ckv ε μ - n - ckv ε Λ) / 2 : ℝ) : ℂ) • G := by
        rw [h4, smul_smul]; congr 1; push_cast; ring
end Formalism.REAL
