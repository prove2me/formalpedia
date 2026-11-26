-- Prove2me | solution 1 for BKAR.Forest.setIntegral_orderedFinSimplexWithTop_succ_eq_headTail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:41:18.082912+00:00
-- url     : https://prove2.me/submissions/b34ce88d-4158-4780-b0cd-ebe1e3a432b5

import Definitions.Def_BKAR_CubePartition_SimplexSector
import Definitions.Def_BKAR_CubePartition_SimplexSector_Finite
import Theorems.Thm_BKAR_Forest_measurableSet_orderedFinSimplexWithTop
import Theorems.Thm_BKAR_Forest_orderedFinSimplexWithTop_succ_eq_piFinSuccAbove_preimage_headTail

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
open MeasureTheory
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (top : ℝ) (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) :
    ∫ ts in orderedFinSimplexWithTop top (n + 1), f ts =
      ∫ z in orderedFinSimplexHeadTail top n,
        f ((MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => ℝ) 0).symm z) := by
  let φ : (Fin (n + 1) → ℝ) ≃ᵐ ℝ × (Fin n → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hsector :
      orderedFinSimplexWithTop top (n + 1) =
        φ ⁻¹' orderedFinSimplexHeadTail top n := by
    exact orderedFinSimplexWithTop_succ_eq_piFinSuccAbove_preimage_headTail top n
  rw [hsector]
  have hpre :=
    (MeasureTheory.volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).setIntegral_preimage_emb
      (MeasurableEquiv.measurableEmbedding φ)
      (fun z : ℝ × (Fin n → ℝ) => f (φ.symm z))
      (orderedFinSimplexHeadTail top n)
  have hmeas : MeasurableSet (φ ⁻¹' orderedFinSimplexHeadTail top n) := by
    rw [← hsector]
    exact measurableSet_orderedFinSimplexWithTop top (n + 1)
  have hcongr :
      ∫ ts in φ ⁻¹' orderedFinSimplexHeadTail top n, f ts =
        ∫ ts in φ ⁻¹' orderedFinSimplexHeadTail top n, f (φ.symm (φ ts)) := by
    apply setIntegral_congr_fun hmeas
    intro ts _hts
    exact congrArg f (φ.left_inv ts).symm
  exact hcongr.trans hpre
end BKAR.Forest
