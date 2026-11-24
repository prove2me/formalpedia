-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.det_block_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:03.689952+00:00
-- url     : https://prove2.me/submissions/f7e8d275-30e0-46f9-b7f9-3277d960b1fe

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Finset
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution {F : Type} [NormedField F] {n : ℕ} (B G : Matrix (Fin n) (Fin n) F) (e : Fin n → ℕ)
    (β : ℕ → F) (c : ℝ) (hc : 0 ≤ c)
    (hB : ∀ i j, B i j = if e i = e j then β (e i) * G i j else 0)
    (hG : ∀ a, c ^ (Fintype.card {b // e b = a}) ≤ ‖(G.toSquareBlock e a).det‖) :
    ∏ b, (‖β (e b)‖ * c) ≤ ‖B.det‖ := by
  classical
  have hBT : B.BlockTriangular e := by
    intro i j hij
    rw [hB, if_neg (ne_of_gt hij)]
  have hblock : ∀ a, B.toSquareBlock e a = β a • G.toSquareBlock e a := by
    intro a
    ext i j
    simp [Matrix.toSquareBlock_def, hB, i.2, j.2]
  rw [hBT.det, norm_prod]
  have hc := Finset.prod_comp (s := Finset.univ) (fun a => ‖β a‖ * c) e
  rw [hc]
  apply Finset.prod_le_prod (fun a _ => by positivity)
  intro a _
  rw [hblock, Matrix.det_smul, norm_mul, norm_pow, mul_pow]
  have hcard : Fintype.card {i // e i = a} = (Finset.univ.filter fun b => e b = a).card := by
    rw [Fintype.card_subtype]
  rw [← hcard]
  exact mul_le_mul_of_nonneg_left (hG a) (by positivity)
end Formalism.GM.MeanGammaLemmas
