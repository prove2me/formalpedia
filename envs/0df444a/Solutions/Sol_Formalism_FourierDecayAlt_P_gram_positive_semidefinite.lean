-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gram_positive_semidefinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:55:15.084081+00:00
-- url     : https://prove2.me/submissions/f5932305-d018-4b07-bfa8-9298207521f6

import Definitions.Def_Formalism_HermitianCurvature_StatementC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelZeroEstimateProduct
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx1_psd_pullback
import Theorems.Thm_Formalism_FourierDecayAlt_P_Cx1_psd_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Jx7_psd_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C
open scoped ComplexOrder
noncomputable section
open Classical
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C.GramPSDOfParts := by
  intro E _ _ _ Wp Wq _ _ _ _ S hP _ Kr hK0 Th e ε hε i w Y
  show TB.PSDOn Y (S.gram ε i w.1)
  have prodPSD : ∀ (s : Finset (Fin S.f)) (k : Fin S.f → TB.Pt E → TB.Pt E → ℂ),
      (∀ v, TB.PSDOn Y (k v)) → TB.PSDOn Y (fun p q => ∏ v ∈ s, k v p q) := by
    intro s k hk
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, TB.PSDOn]
      let A : Matrix Unit Y ℂ := Matrix.of fun _ _ => 1
      have h2 := Matrix.posSemidef_conjTranspose_mul_self A
      convert h2 using 1
      ext x y
      simp [A, Matrix.mul_apply]
    | @insert a s ha ih =>
      simp only [TB.PSDOn] at ih ⊢
      have h1 : (Matrix.of fun x y : Y => ∏ v ∈ insert a s, k v x y) =
          (Matrix.of fun x y : Y => k a x y).hadamard (Matrix.of fun x y : Y => ∏ v ∈ s, k v x y) := by
        ext x y
        simp [Finset.prod_insert ha, Matrix.hadamard]
      rw [h1]
      exact (hk a).hadamard ih
  by_cases hi : i ≤ S.G.r + 1
  · have hg : S.gram ε i w.1 =
        fun p q => ∏ v, S.gramLoc v ε i (w.1 v) (loc (S.σ v) p) (loc (S.σ v) q) := by
      funext p q
      simp [Formalism.FourierDecayAlt.C.HidaSetting.gram, hi]
    rw [hg]
    exact prodPSD Finset.univ _ fun v =>
      Cx1.psd_pullback Y (loc (S.σ v)) _ _ (fun x hx => Finset.mem_image_of_mem _ hx)
        (hP v ε hε i hi w _)
  · have hg : S.gram ε i w.1 = fun _ _ => 0 := by
      funext p q
      simp [Formalism.FourierDecayAlt.C.HidaSetting.gram, hi]
    rw [hg]
    exact Cx1.psd_zero Y
end Formalism.FourierDecayAlt.P
