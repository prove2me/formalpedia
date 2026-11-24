-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.div_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:27:06.780767+00:00
-- url     : https://prove2.me/submissions/f510131c-a91f-47c7-9585-61c818e7b5dc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_L2_Th1_B_E2_integral_add
import Theorems.Thm_Formalism_L2_Th1_B_E2_integral_sub
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_Formalism_L2_Th1_B_integral_mvPowerSeries_X
import Theorems.Thm_Formalism_L2_Th1_B_integral_subst_two_variables
import Theorems.Thm_Formalism_L2_Th1_B_law_coeff_axis1
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E2
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob in3)
open Formalism.G.LogP (hs2 hs3 subst2_subst psubst_subst subst_XX subst_zero')
variable {K : Type} [NormedField K] [IsUltrametricDist K] [CharZero K]
namespace Formalism.L2.Th1.B.E2
theorem _root_.solution {G : MvPowerSeries (Fin 2) K} (hG : Integral G)
    (hd : MvPowerSeries.subst
      ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] G = 0) :
    ∃ n : MvPowerSeries (Fin 2) K, Integral n ∧ G = (MvPowerSeries.X 0 - MvPowerSeries.X 1) * n := by
  have c0 : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have c1 : MvPowerSeries.constantCoeff (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cz : MvPowerSeries.constantCoeff (0 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cs : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have cd : MvPowerSeries.constantCoeff
      (MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) = 0 := by simp
  have i0 := integral_mvPowerSeries_X (K := K) (0 : Fin 2)
  have i1 := integral_mvPowerSeries_X (K := K) (1 : Fin 2)
  obtain ⟨H, hH⟩ : ∃ H, H = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] G :=
    ⟨_, rfl⟩
  have iH : Integral H := by
    rw [hH]
    exact integral_subst_two_variables hG _ _ cs c1 (integral_add i0 i1) i1
  have hH0 : MvPowerSeries.subst ![0, (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K)] H = 0 := by
    have hb := hs2 cz c1
    rw [hH, subst2_subst G cs c1 hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb,
      MvPowerSeries.subst_X hb]
    simpa using hd
  have hdvd : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ∣ H := by
    rw [MvPowerSeries.X_dvd_iff]
    intro m hm
    rw [law_coeff_axis1 H m hm, hH0, map_zero]
  obtain ⟨H1, e1⟩ := hdvd
  have iH1 : Integral H1 := by
    intro n
    have := iH (Finsupp.single 0 1 + n)
    rwa [e1, MvPowerSeries.X_def, MvPowerSeries.coeff_add_monomial_mul, one_mul] at this
  have hb := hs2 cd c1
  refine ⟨MvPowerSeries.subst
    ![(MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] H1,
    integral_subst_two_variables iH1 _ _ cd c1 (integral_sub i0 i1) i1, ?_⟩
  have e2 : MvPowerSeries.subst
      ![(MvPowerSeries.X 0 - MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K), MvPowerSeries.X 1] H =
      G := by
    rw [hH, subst2_subst G cs c1 hb, MvPowerSeries.subst_add hb, MvPowerSeries.subst_X hb,
      MvPowerSeries.subst_X hb]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_add_cancel]
    exact subst_XX G
  rw [← e2, e1, MvPowerSeries.subst_mul hb, MvPowerSeries.subst_X hb]
  rfl
end Formalism.L2.Th1.B.E2
