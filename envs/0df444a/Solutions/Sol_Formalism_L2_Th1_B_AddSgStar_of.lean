-- Prove2me | solution 1 for Formalism.L2.Th1.B.AddSgStar_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:29:32.52268+00:00
-- url     : https://prove2.me/submissions/331e124c-e162-4017-a222-05630ea47b93

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_subst_sgStar
import Theorems.Thm_Formalism_G_LogP_hX0


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B
open Formalism.InvariantFactorPaths.G7 (at1)
open Add0
namespace Formalism.L2.Th1.B
theorem _root_.solution (hA : AddSigma) (h1 : ExpLogRules) (h3 : ExpLogSubst) : AddSgStar := by
  intro K _ _ g2 g3 s2 P hP
  have hAP := hA K g2 g3 P hP
  obtain ⟨hadd, -, -⟩ := h1 K (Fin 2)
  have hS0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp
  have hD0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp
  have hX0 : ∀ x : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) = 0 :=
    fun x => by simp
  have hq : ∀ u : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff u = 0 →
      MvPowerSeries.constantCoeff (-(MvPowerSeries.C (s2 / 2) * u ^ 2)) = 0 := fun u hu => by simp [hu]
  have eS : atS (sgStar s2 P) = atS (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P hS0
  have eD : atD (sgStar s2 P) = atD (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P hD0
  have e0 : (at1 0 (sgStar s2 P) : MvPowerSeries (Fin 2) K) = at1 0 (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P (hX0 0)
  have e1 : (at1 1 (sgStar s2 P) : MvPowerSeries (Fin 2) K) = at1 1 (sigma P) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2)) :=
    Add0.subst_sgStar h3 s2 P (hX0 1)
  have q0 := hq _ (hX0 0)
  have q1 := hq _ (hX0 1)
  have q00 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2) +
      -(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2)) = 0 := by
    rw [map_add, q0, add_zero]
  have q11 : MvPowerSeries.constantCoeff (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2) +
      -(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2)) = 0 := by
    rw [map_add, q1, add_zero]
  have hG : fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ 2)) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 2)) =
      (fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ^ 2))) *
      (fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2)) *
        fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ^ 2))) := by
    rw [← hadd _ _ (hq _ hS0) (hq _ hD0), ← hadd _ _ q0 q0, ← hadd _ _ q1 q1, ← hadd _ _ q00 q11]
    congr 1
    ring
  rw [eS, eD, e0, e1]
  linear_combination (fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 + MvPowerSeries.X 1) ^ 2)) *
      fExp (-(MvPowerSeries.C (s2 / 2) * (MvPowerSeries.X 0 - MvPowerSeries.X 1) ^ 2))) * hAP +
    ((at1 0 (sigma P) : MvPowerSeries (Fin 2) K) ^ 2 * at1 1 (sigma P) ^ 2 * wpDiff P) * hG
end Formalism.L2.Th1.B
