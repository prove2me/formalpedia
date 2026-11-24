-- Prove2me | solution 1 for Formalism.L2.Th1.B.AddSigma_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:30:47.060951+00:00
-- url     : https://prove2.me/submissions/bb75a19d-29e8-44db-bd47-298d8160f10a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_PderivZeroZeroWeierstrassDifference
import Theorems.Thm_Formalism_L2_Th1_B_Add0_wpDiff_eq
import Theorems.Thm_Formalism_L2_Th1_B_Add0_sigS_cc
import Theorems.Thm_Formalism_L2_Th1_B_Add0_subst_sigma
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
theorem _root_.solution (hL : AddSigmaLog) (h1 : ExpLogRules) (h3 : ExpLogSubst) (h9 : DqRule) :
    AddSigma := by
  intro K _ _ g2 g3 P hP
  have hLog := hL K g2 g3 P hP
  obtain ⟨hadd, -, hexplog⟩ := h1 K (Fin 2)
  have hf0 : PowerSeries.constantCoeff (sigS P) = 0 := Add0.sigS_cc P
  have hcc : ∀ (u : MvPowerSeries (Fin 2) K) (g : PowerSeries K), MvPowerSeries.constantCoeff u = 0 →
      PowerSeries.constantCoeff g = 0 → MvPowerSeries.constantCoeff (PowerSeries.subst u g) = 0 := by
    intro u g hu hg
    obtain ⟨g', rfl⟩ := PowerSeries.X_dvd_iff.2 hg
    have ha := PowerSeries.HasSubst.of_constantCoeff_zero hu
    rw [← PowerSeries.coe_substAlgHom ha, map_mul, PowerSeries.coe_substAlgHom, PowerSeries.subst_X ha, map_mul,
      hu, zero_mul]
  have hS0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp
  have hD0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by
    simp
  have hX0 : ∀ x : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X x : MvPowerSeries (Fin 2) K) = 0 :=
    fun x => by simp
  have eS : atS (sigma P) = (MvPowerSeries.X 0 + MvPowerSeries.X 1) * fExp (atS (sigS P)) :=
    Add0.subst_sigma h3 P hS0
  have eD : atD (sigma P) = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * fExp (atD (sigS P)) :=
    Add0.subst_sigma h3 P hD0
  have e0 : (at1 0 (sigma P) : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X 0 * fExp (at1 0 (sigS P) : MvPowerSeries (Fin 2) K) := Add0.subst_sigma h3 P (hX0 0)
  have e1 : (at1 1 (sigma P) : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.X 1 * fExp (at1 1 (sigS P) : MvPowerSeries (Fin 2) K) := Add0.subst_sigma h3 P (hX0 1)
  have cS : MvPowerSeries.constantCoeff (atS (sigS P)) = 0 := hcc _ _ hS0 hf0
  have cD : MvPowerSeries.constantCoeff (atD (sigS P)) = 0 := hcc _ _ hD0 hf0
  have c0 : MvPowerSeries.constantCoeff (at1 0 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := hcc _ _ (hX0 0) hf0
  have c1 : MvPowerSeries.constantCoeff (at1 1 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := hcc _ _ (hX0 1) hf0
  have hN1 : MvPowerSeries.constantCoeff
      (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P : MvPowerSeries (Fin 2) K) = 1 := by simp
  obtain ⟨hlog0, hexpN⟩ := hexplog _ hN1
  have hsum : atS (sigS P) + atD (sigS P) = (at1 0 (sigS P) + at1 0 (sigS P)) +
      (at1 1 (sigS P) + at1 1 (sigS P)) + fLog (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P) := by
    unfold par0 at hLog
    linear_combination hLog
  have c00 : MvPowerSeries.constantCoeff (at1 0 (sigS P) + at1 0 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [map_add, c0, add_zero]
  have c11 : MvPowerSeries.constantCoeff (at1 1 (sigS P) + at1 1 (sigS P) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [map_add, c1, add_zero]
  have c0011 : MvPowerSeries.constantCoeff ((at1 0 (sigS P) + at1 0 (sigS P)) +
      (at1 1 (sigS P) + at1 1 (sigS P)) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [map_add, c00, c11, add_zero]
  have hprod : fExp (atS (sigS P)) * fExp (atD (sigS P)) =
      (fExp (at1 0 (sigS P)) * fExp (at1 0 (sigS P))) * (fExp (at1 1 (sigS P)) * fExp (at1 1 (sigS P))) *
        (1 - MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 * dq P) := by
    rw [← hadd _ _ cS cD, hsum, hadd _ _ c0011 hlog0, hadd _ _ c00 c11, hadd _ _ c0 c0, hadd _ _ c1 c1, hexpN]
  rw [eS, eD, e0, e1, Add0.wpDiff_eq h9 hP.2.1]
  linear_combination (MvPowerSeries.X 0 ^ 2 * MvPowerSeries.X 1 ^ 2 *
    (MvPowerSeries.X 0 ^ 2 - MvPowerSeries.X 1 ^ 2) : MvPowerSeries (Fin 2) K) * hprod
end Formalism.L2.Th1.B
