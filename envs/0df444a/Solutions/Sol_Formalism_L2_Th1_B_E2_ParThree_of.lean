-- Prove2me | solution 1 for Formalism.L2.Th1.B.E2.ParThree_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:20.915577+00:00
-- url     : https://prove2.me/submissions/31b21703-7d73-4822-8f9d-f536e4482d5a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_ConstantCoeffLawWithInverseThree
import Theorems.Thm_Formalism_L2_Th1_B_E2_integral_neg
import Theorems.Thm_Formalism_L2_Th1_B_E2_cX
import Theorems.Thm_Formalism_L2_Th1_B_E2_parallelogram_three_weierstrass_key
import Theorems.Thm_Formalism_G_LogP_constantCoeff_subst_of_zero
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_G_LogP_psubst_subst
import Theorems.Thm_Formalism_G_LogP_subst2_subst
import Theorems.Thm_Formalism_G_LogP_subst_XX
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_Formalism_L2_Th1_B_Jets_key
import Theorems.Thm_Formalism_L2_Th1_B_ParO_fLog_mul
import Theorems.Thm_Formalism_L2_Th1_B_constantCoeff_fExp
import Theorems.Thm_Formalism_L2_Th1_B_fLog_fExp
import Theorems.Thm_Formalism_L2_Th1_B_integral_mvPowerSeries_X
import Theorems.Thm_Formalism_L2_Th1_B_integral_subst_two_variables
import Theorems.Thm_Formalism_L2_Th1_B_simeqLog
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211
import Theorems.Thm_P2M_Formalism_InvariantFactorPaths_G7_LogarithmEquivalence_integral_mul__d725f3beb1b3


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
namespace Formalism.L2.Th1.B.E2
theorem _root_.solution (hF : FrobStickStar) (hU : FIUnit) : ParThree := by
  intro K _ _ _ g2 g3 s2 c0 a1 a3 P l i ep F hP hL hi hC hC3
  obtain ⟨-, -, h2, -⟩ := hC
  obtain ⟨h3, e, heI, he0, he⟩ := hC3
  obtain ⟨n, hnI, hn0, hn⟩ := hU K F l i hL hi
  obtain ⟨h0, key⟩ := parallelogram_three_weierstrass_key (s2 := s2) hF hP hL hi h2 h3 he hn
  have iN : ∀ j k : Fin 3, Integral (MvPowerSeries.subst
      ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] n) := fun j k =>
    integral_subst_two_variables hnI _ _ (cX j) (cX k) (integral_mvPowerSeries_X j) (integral_mvPowerSeries_X k)
  have cN : ∀ j k : Fin 3, MvPowerSeries.constantCoeff (MvPowerSeries.subst
      ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] n) = 1 := fun j k => by
    rw [Formalism.G.LogP.constantCoeff_subst_of_zero n (fun s => by fin_cases s <;> simp), hn0]
  generalize par3 F i (phO s2 P l) = q at h0 key ⊢
  obtain ⟨N, hN⟩ : ∃ N, N = MvPowerSeries.subst
      ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 1] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n *
      MvPowerSeries.subst ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) K), MvPowerSeries.X 2] n :=
    ⟨_, rfl⟩
  have iNN : Integral N := by
    rw [hN]
    exact Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (Formalism.InvariantFactorPaths.G7.LogarithmEquivalence.integral_mul' (iN 0 1) (iN 0 2)) (iN 1 2)
  have cNN : MvPowerSeries.constantCoeff N = 1 := by
    rw [hN, map_mul, map_mul, cN, cN, cN]; ring
  rw [← hN] at key
  have hq0 : MvPowerSeries.constantCoeff (-q) = 0 := by rw [map_neg, h0, neg_zero]
  have hlog := ParO.fLog_mul cNN (constantCoeff_fExp hq0)
  rw [key, fLog_fExp hq0] at hlog
  have hq : q = fLog N + -fLog (-e) := by linear_combination hlog
  have s1 := (simeqLog K (Fin 3) N cNN iNN).1
  have s2' := (simeqLog K (Fin 3) (-e) (by rw [map_neg, he0, neg_neg]) (integral_neg heI)).2
  have s3 := (Formalism.InvariantFactorPaths.G7.equivalence_rules K (Fin 3)).2.2.2.1 _ _ _ _ s1 s2'
  rw [add_zero] at s3
  rw [hq]
  exact s3
end Formalism.L2.Th1.B.E2
