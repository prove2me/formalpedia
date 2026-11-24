-- Prove2me | solution 1 for Formalism.GM.DetBound.gaussR_det_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:20:09.221783+00:00
-- url     : https://prove2.me/submissions/4d26e119-a85a-4269-8970-ff0f8a2517fa

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Theorems.Thm_Formalism_GM_DetBound_gaussR_sum_le
import Theorems.Thm_Formalism_GM_DetBound_gaussR_neg
import Theorems.Thm_Formalism_GM_DetBound_gaussR_prod_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DetBound
open Finset Polynomial
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.GM.DetBound
theorem _root_.solution (ρ : NNReal) {n : ℕ} (M : Matrix (Fin n) (Fin n) K[X]) (b : Fin n → NNReal)
    (hb : ∀ i j, gaussR ρ (M i j) ≤ b i) : gaussR ρ M.det ≤ ∏ i, b i := by
  rw [Matrix.det_apply]
  apply gaussR_sum_le
  intro σ _
  have hsign : gaussR ρ (Equiv.Perm.sign σ • ∏ i, M (σ i) i) = gaussR ρ (∏ i, M (σ i) i) := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h, one_smul]
    · rw [h, Units.neg_smul, one_smul, gaussR_neg]
  rw [hsign]
  calc gaussR ρ (∏ i, M (σ i) i) ≤ ∏ i, gaussR ρ (M (σ i) i) := gaussR_prod_le _ _ _
    _ ≤ ∏ i, b (σ i) := Finset.prod_le_prod' fun i _ => hb _ _
    _ = ∏ i, b i := Equiv.prod_comp σ b
end Formalism.GM.DetBound
