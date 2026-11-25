-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBJ.Frz.phiTop_freeze
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:31:49.525834+00:00
-- url     : https://prove2.me/submissions/01d5905d-19c1-4c60-b01f-e7d7eef491f4

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KloostDensOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnitaryInvariantGaussian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BlockTwoDiagonalZeroSize
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_zj_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_vol_univ_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_integrable_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_psiH_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBJ_Frz_psiH_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBJ Formalism.FourierDecayAlt.P.PBJ.Frz
open MeasureTheory Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.PBJ.Frz
theorem _root_.solution [CompleteSpace V] (β c : ℂ) {p : ℕ} (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (hd : ∀ i, d i ≠ 0) {Ψ : G.Mat (p + 1) → V} (hΨ : KCls Ψ) :
    PhiTop (p := p) (s := 1) β σ d Ψ (fun _ _ => c) =
      PhiTop (p := p) (s := 0) β σ d (Psc β c Ψ) (fun x => x.elim0) := by
  have hint := integrable_one β c σ d hd hΨ
  set X : (LW σ → ℂ) × (G.UT p → ℂ) → ℂ :=
    fun vu => G.psi β (subS (wP σ * lowW σ vu.1 * (wP σ)⁻¹) + supS (G.upper vu.2)) with hX
  have eL : (fun η : XiH p 1 σ => psiH β σ η • Ψ (ZjH σ d η (fun _ _ => c))) =
      fun η => X η.2 • gI β c Ψ (headH σ d η.2.1 η.2.2) η.1 := by
    funext η
    rw [psiH_one, mul_smul]
    rfl
  have eR : (fun η : XiH p 0 σ => psiH β σ η • Psc β c Ψ (ZjH σ d η (fun x => x.elim0))) =
      fun η => X η.2 • Psc β c Ψ (headH σ d η.2.1 η.2.2) := by
    funext η
    rw [psiH_zero]
    unfold ZjH
    rw [zj_zero]
  unfold PhiTop muXiH
  rw [eL, eR]
  rw [eL] at hint
  unfold muXiH at hint
  rw [Measure.volume_eq_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  rw [Measure.volume_eq_prod (α := (Fin 0 → Fin p → ℂ) × (Fin p → Fin 0 → ℂ))]
  rw [integral_fun_snd (fun vu : (LW σ → ℂ) × (G.UT p → ℂ) => X vu • Psc β c Ψ (headH σ d vu.1 vu.2))]
  rw [vol_univ_zero, one_smul]
  congr 1
  funext vu
  show ∫ x, X vu • gI β c Ψ (headH σ d vu.1 vu.2) x = X vu • ∫ x, gI β c Ψ (headH σ d vu.1 vu.2) x
  exact integral_smul _ _
end Formalism.FourierDecayAlt.P.PBJ.Frz
