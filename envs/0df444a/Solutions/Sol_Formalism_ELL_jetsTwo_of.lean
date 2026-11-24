-- Prove2me | solution 1 for Formalism.ELL.jetsTwo_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:46.765226+00:00
-- url     : https://prove2.me/submissions/639f8a3b-2e83-4fb9-be15-2b48e1be08bf

import Definitions.Def_Formalism_EllipticTorsion_JetsCube
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_ConstantCoeffSubstOfZero
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_JetsTwo
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_Q_sub
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_cc_psubst
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_quadraticJet_subst_X0
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_quadraticJet_subst_X1
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_linearCoeff_zero_subst_X0
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_linearCoeff_one_subst_X1
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_linearCoeff_one_subst_X0
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_linearCoeff_zero_subst_X1
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_Q_phi
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hv
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_ccd_F
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_Q_F
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_ccd_single
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_ccd_mixed
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_constantCoeff_second_derivative_law
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_linearCoeff_zero_formal_group_law
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_linearCoeff_one_formal_group_law
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
noncomputable section
open Formalism Formalism.ELL
open Formalism.G Formalism.ELL.FormalGroupQuadraticJets Formalism.G.LogCR
namespace Formalism.ELL
theorem _root_.solution (hN : Formalism.ELL.NPderiv.{u}) : Formalism.ELL.JetsTwo.{u} := by
  intro K _ _ _ F φ a a' ha ha' hG
  have ha0 : PowerSeries.constantCoeff a = 0 := ha.1
  have ha0' : PowerSeries.constantCoeff a' = 0 := ha'.1
  have hβ : ∀ x y : MvPowerSeries (Fin 2) K, betaF F φ x y =
      φ.subst (MvPowerSeries.subst ![x, y] (FK F).toPowerSeries) - φ.subst x - φ.subst y :=
    fun x y => rfl
  have cX0 : MvPowerSeries.constantCoeff (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have constantCoeff_threeGroupsFirstVariables_eq_zero : MvPowerSeries.constantCoeff (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 :=
    MvPowerSeries.constantCoeff_X _
  have cu : MvPowerSeries.constantCoeff
      (a.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
    rw [cc_psubst cX0]; exact ha0
  have cv : MvPowerSeries.constantCoeff
      (a'.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K)) = 0 := by
    rw [cc_psubst constantCoeff_threeGroupsFirstVariables_eq_zero]; exact ha0'
  have hX00 : ccd 0 (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 1 := by
    rw [ccd_single, MvPowerSeries.coeff_X, if_pos rfl]
  have hX10 : ccd 1 (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [ccd_single, MvPowerSeries.coeff_X, if_neg]
    rw [Finsupp.single_left_inj one_ne_zero]; decide
  have hX01 : ccd 0 (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 0 := by
    rw [ccd_single, MvPowerSeries.coeff_X, if_neg]
    rw [Finsupp.single_left_inj one_ne_zero]; decide
  have hX11 : ccd 1 (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K) = 1 := by
    rw [ccd_single, MvPowerSeries.coeff_X, if_pos rfl]
  have hQX : ∀ j : Fin 2, Q (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = 0 := by
    intro j
    unfold Q
    rw [MvPowerSeries.pderiv_X]
    fin_cases j <;> simp [Pi.single_apply, Derivation.map_one_eq_zero]
  have cS : ∀ x y : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff x = 0 →
      MvPowerSeries.constantCoeff y = 0 →
      MvPowerSeries.constantCoeff (MvPowerSeries.subst ![x, y] (FK F).toPowerSeries) = 0 := by
    intro x y hx hy
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero _ (hv hx hy)]
    exact (FK F).zero_constantCoeff
  have h1 : Q (betaF F φ (a.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
      (MvPowerSeries.X 1)) = PowerSeries.coeff 1 a *
        (PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K φ)) +
          PowerSeries.constantCoeff (PowerSeries.derivative K φ) *
            ccd 0 (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries)) := by
    rw [hβ, Q_sub, Q_sub, Q_phi φ (cS _ _ cu constantCoeff_threeGroupsFirstVariables_eq_zero), Q_phi φ cu, Q_phi φ constantCoeff_threeGroupsFirstVariables_eq_zero,
      ccd_F _ cu constantCoeff_threeGroupsFirstVariables_eq_zero, ccd_F _ cu constantCoeff_threeGroupsFirstVariables_eq_zero, Q_F _ cu constantCoeff_threeGroupsFirstVariables_eq_zero]
    simp only [linearCoeff_zero_formal_group_law, linearCoeff_one_formal_group_law, linearCoeff_zero_subst_X0, linearCoeff_one_subst_X0, quadraticJet_subst_X0, hX01, hX11, hQX, ccd_mixed]
    ring
  have h2 : Q (betaF F φ (MvPowerSeries.X 0)
      (a'.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))) = PowerSeries.coeff 1 a' *
        (PowerSeries.constantCoeff (PowerSeries.derivative K (PowerSeries.derivative K φ)) +
          PowerSeries.constantCoeff (PowerSeries.derivative K φ) *
            ccd 0 (MvPowerSeries.pderiv K 1 (FK F).toPowerSeries)) := by
    rw [hβ, Q_sub, Q_sub, Q_phi φ (cS _ _ cX0 cv), Q_phi φ cX0, Q_phi φ cv,
      ccd_F _ cX0 cv, ccd_F _ cX0 cv, Q_F _ cX0 cv]
    simp only [linearCoeff_zero_formal_group_law, linearCoeff_one_formal_group_law, linearCoeff_one_subst_X1, linearCoeff_zero_subst_X1, quadraticJet_subst_X1, hX00, hX10, hQX, ccd_mixed]
    ring
  have hQG := hN K (Fin 2) _ hG 0
  have key : Q (betaF F φ (a.subst (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) K))
        (MvPowerSeries.X 1) -
      betaF F φ (MvPowerSeries.X 0) (a'.subst (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) K))) =
      (PowerSeries.coeff 1 a - PowerSeries.coeff 1 a') * PowerSeries.constantCoeff ((invD F)^[2] φ) := by
    rw [Q_sub, h1, h2, constantCoeff_second_derivative_law, linearCoeff_one_formal_group_law]
    ring
  rw [← key]
  unfold Q
  rw [show ∀ Z : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K 1 Z) =
      MvPowerSeries.coeff (Finsupp.single 1 1) Z from fun Z => ccd_single Z 1]
  exact hQG _
end Formalism.ELL
