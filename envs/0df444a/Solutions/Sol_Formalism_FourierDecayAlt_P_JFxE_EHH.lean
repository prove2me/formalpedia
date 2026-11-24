-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.JFxE.EHH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:55:23.859346+00:00
-- url     : https://prove2.me/submissions/d6328338-18b6-4e61-859f-0aa208e9d66e

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EHcChange
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapAdInv
import Theorems.Thm_Formalism_FourierDecayAlt_P_B4_op_op_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_Dx
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_CkOn_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_BetaSesquilinearity_Dx_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_EH_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xa_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_JFxB_Xb_lie


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.JFxE
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity Formalism.FourierDecayAlt.P.JFxB
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace Formalism.FourierDecayAlt.P.JFxE
theorem _root_.solution {φ F : Mat k r → E} {U : Set (Mat k r)} {g : Mat k r} (hφ : CkOn 2 (GV k r) φ) (hU : IsOpen U)
    (hgU : g ∈ U) (hg : g ∈ GV k r) (hF : ContDiffOn ℝ 2 F U) (hff : ∀ h ∈ U, h ∈ GV k r → φ h = F h)
    (a b c d : Fin (2 * r + k + 1)) :
    Q.EH k r a b (Q.EH k r c d φ) g =
      (fderiv ℝ F g (g * Xa k r a b * Xa k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xa k r a b) (g * Xa k r c d)) +
        Complex.I • (fderiv ℝ F g (g * Xa k r a b * Xb k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xa k r a b) (g * Xb k r c d)) +
      Complex.I • ((fderiv ℝ F g (g * Xb k r a b * Xa k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xb k r a b) (g * Xa k r c d)) +
        Complex.I • (fderiv ℝ F g (g * Xb k r a b * Xb k r c d) +
          fderiv ℝ (fderiv ℝ F) g (g * Xb k r a b) (g * Xb k r c d))) := by
  have hc : ContDiffOn ℝ (((1 + 1 : ℕ) : ℕ∞) : WithTop ℕ∞) F U := by simpa using hF
  have hφ2 : CkOn ((1 : ℕ∞) + 1) (GV k r) φ := by
    have e : ((1 : ℕ∞) + 1) = 2 := by norm_num
    rw [e]; exact hφ
  have hφ1 : ∀ X : Mat k r, inLie k r X → CkOn 1 (GV k r) (Dx (false, X) φ) :=
    fun X hX => CkOn_Dx (x := (false, X)) hX hφ2
  have hop : ∀ X Y : Mat k r, inLie k r X → inLie k r Y →
      Dx (false, X) (Dx (false, Y) φ) g =
        fderiv ℝ (fderiv ℝ F) g (g * X) (g * Y) + fderiv ℝ F g (g * X * Y) :=
    fun X Y hX hY => Formalism.FourierDecayAlt.P.B4.op_op_ext false false hU hc hff hX hY hgU hg
  have hEcd : Q.EH k r c d φ = fun h => Dx (false, Xa k r c d) φ h + Complex.I • Dx (false, Xb k r c d) φ h :=
    EH_eq c d φ
  rw [EH_eq a b, hEcd]
  simp only
  rw [Dx_add (x := (false, Xa k r a b)) (Xa_lie a b) (hφ1 _ (Xa_lie c d)) (CkOn_smul _ (hφ1 _ (Xb_lie c d))) g hg,
    Dx_add (x := (false, Xb k r a b)) (Xb_lie a b) (hφ1 _ (Xa_lie c d)) (CkOn_smul _ (hφ1 _ (Xb_lie c d))) g hg,
    Dx_smul, Dx_smul]
  simp only
  rw [hop _ _ (Xa_lie a b) (Xa_lie c d), hop _ _ (Xa_lie a b) (Xb_lie c d), hop _ _ (Xb_lie a b) (Xa_lie c d),
    hop _ _ (Xb_lie a b) (Xb_lie c d)]
  simp only [smul_add]
  abel
end Formalism.FourierDecayAlt.P.JFxE
