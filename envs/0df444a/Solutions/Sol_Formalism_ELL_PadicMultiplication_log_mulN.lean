-- Prove2me | solution 1 for Formalism.ELL.PadicMultiplication.log_mulN
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:24:07.35904+00:00
-- url     : https://prove2.me/submissions/8880e78f-0bb3-415c-b3b0-111433b98849

import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_PadicMult
import Theorems.Thm_Formalism_ELL_PadicMultiplication_mulN_zero
import Theorems.Thm_Formalism_ELL_PadicMultiplication_constantCoeff_mulN
import Theorems.Thm_Formalism_ELL_PadicMultiplication_map_mulN
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_psubst_subst


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
universe u
open Formalism Formalism.ELL Formalism.ELL.PadicMultiplication
open Formalism.G Formalism.G.LogP
variable {K : Type u} [NormedField K] [IsUltrametricDist K]
namespace Formalism.ELL.PadicMultiplication
theorem _root_.solution (F : FormalGroup (unitBall K)) (l : PowerSeries K)
    (hl : IsLog (F.map (unitBall K).subtype) l) (m : ℕ) :
    l.subst ((mulN F m).map (unitBall K).subtype) = (m : K) • l := by
  obtain ⟨hl0, -, hlF⟩ := hl
  induction m with
  | zero => simp [mulN_zero, hl0]
  | succ m ih =>
    have hM : MvPowerSeries.constantCoeff ((mulN F m).map (unitBall K).subtype) = 0 := by
      show MvPowerSeries.constantCoeff (MvPowerSeries.map _ (mulN F m)) = 0
      rw [MvPowerSeries.constantCoeff_map, constantCoeff_mulN]; simp
    have hs := hs2 (R := K) hM (v := (PowerSeries.X : PowerSeries K)) PowerSeries.constantCoeff_X
    rw [map_mulN, ← psubst_subst l (F.map (unitBall K).subtype).zero_constantCoeff hs, hlF,
      MvPowerSeries.subst_add hs, atX, atY,
      psubst_subst l (by simp) hs, psubst_subst l (by simp) hs,
      MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [ih, PowerSeries.X_subst]
    push_cast
    rw [add_smul, one_smul]
end Formalism.ELL.PadicMultiplication
