-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.RecursionWithDensities.A1.psd_restr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:48:04.959555+00:00
-- url     : https://prove2.me/submissions/e225eaf2-dc56-4203-82e5-2bda8c6559a8

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequality
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OneLevelInequalitySplitBySize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AntidiagMulDiagonal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RecursionWithDensities
import Theorems.Thm_Formalism_FourierDecayAlt_P_RecursionWithDensities_A1_psd_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.RecursionWithDensities Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TA Finset
open scoped ComplexConjugate InnerProductSpace
open Classical
variable {α : Type}
namespace Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
theorem _root_.solution (X Y : Finset α) {k : α → α → ℂ} (hk : PSDOn X k) : PSDOn Y (restr X k) := by
  have hU : PSDOn (X ∪ Y) (restr X k) := by
    unfold TA.PSDOn at hk ⊢
    refine ⟨fun x _ y _ => ?_, fun a => ?_⟩
    · unfold restr
      by_cases hx : x ∈ X
      · by_cases hy : y ∈ X
        · simp [hx, hy, hk.1 x hx y hy]
        · simp [hx, hy]
      · simp [hx]
    · have e : ∑ x ∈ X ∪ Y, ∑ y ∈ X ∪ Y, conj (a x) * restr X k x y * a y =
          ∑ x ∈ X, ∑ y ∈ X, conj (a x) * k x y * a y := by
        rw [← Finset.sum_subset (f := fun x => ∑ y ∈ X ∪ Y, conj (a x) * restr X k x y * a y)
          (fun z hz => Finset.mem_union_left _ hz) (fun x _ hx => by simp [restr, hx])]
        refine Finset.sum_congr rfl fun x hx => ?_
        rw [← Finset.sum_subset (f := fun y => conj (a x) * restr X k x y * a y)
          (fun z hz => Finset.mem_union_left _ hz) (fun y _ hy => by simp [restr, hy])]
        refine Finset.sum_congr rfl fun y hy => ?_
        simp [restr, hx, hy]
      rw [e]
      exact hk.2 a
  exact psd_mono (P := X ∪ Y) (fun z hz => Finset.mem_union_right _ hz) hU
end Formalism.FourierDecayAlt.P.RecursionWithDensities.A1
