-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.formal_law_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:46:34.786164+00:00
-- url     : https://prove2.me/submissions/b3ad6a97-e8fd-4a0c-a03d-16e94cd84e69

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_FormalGroupLog_FormalGroupLogProofs_HomPsSubstMvSubst
import Definitions.Def_Formalism_TorsionNormIteration_LubinTateExample
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_FrobSqV
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_CoeffSubstLgFOfDegreeOne
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_constantCoeff_lgF
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_cob_eq_zero_iff
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_subst_inj
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_law_unique
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_map_law
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_subst
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_lgF_subst_C_mul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_coeff_subst_lgF_of_degree_one
import Theorems.Thm_Formalism_G_LogP_hs2


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open FormalGroupLaws
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution : LawSymm := by
  intro K _ _ _ p hp hnp F hF
  obtain ⟨hF0, _, hFc⟩ := hF
  have hp2 := hp.two_le
  have hFl : PowerSeries.subst F (lgF K p) =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) (lgF K p) +
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) (lgF K p) :=
    (cob_eq_zero_iff F _).mp hFc
  have hFlA : PowerSeries.subst F (lgF K p) = at1 0 (lgF K p) + at1 1 (lgF K p) :=
    (cob_eq_zero_iff F _).mp hFc
  have hl0 := constantCoeff_lgF (K := K) p hp2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro σ
    obtain ⟨h0, hc⟩ := map_law σ p F hF0 hFc
    exact law_unique p hp2 _ F h0 hF0 hc hFc
  · intro ζ hζ
    have hb : MvPowerSeries.HasSubst
        (fun a : Fin 2 => MvPowerSeries.C ζ * (MvPowerSeries.X a : MvPowerSeries (Fin 2) K)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero (fun a => by simp)
    apply lgF_subst_inj p hp2
    · exact MvPowerSeries.constantCoeff_subst_eq_zero hb (fun a => by simp) hF0
    · simp [hF0]
    · rw [← subst_subst hb (PowerSeries.HasSubst.of_constantCoeff_zero hF0), hFlA,
        MvPowerSeries.subst_add hb, subst_single_var hb, subst_single_var hb]
      beta_reduce
      rw [lgF_subst_C_mul hζ hp2 (MvPowerSeries.X (0 : Fin 2)) (by simp),
        lgF_subst_C_mul hζ hp2 (MvPowerSeries.X (1 : Fin 2)) (by simp),
        lgF_subst_C_mul hζ hp2 F hF0, hFl, mul_add]
  · intro n hn
    rw [← coeff_subst_lgF_of_degree_one p hp2 F hF0 n hn, hFl, map_add,
      coeff_subst_lgF_of_degree_one p hp2 (MvPowerSeries.X (0 : Fin 2)) (by simp) n hn,
      coeff_subst_lgF_of_degree_one p hp2 (MvPowerSeries.X (1 : Fin 2)) (by simp) n hn]
    have hsum : n 0 + n 1 = 1 := by
      have h1 := hn
      rw [Finsupp.degree_eq_sum, Fin.sum_univ_two] at h1
      exact h1
    have hne : Finsupp.single (1 : Fin 2) 1 ≠ Finsupp.single 0 1 := by
      rw [Ne, Finsupp.single_left_inj one_ne_zero]
      decide
    rcases Nat.eq_zero_or_pos (n 0) with h0 | h0
    · have hn' : n = Finsupp.single 1 1 := by
        ext i
        fin_cases i <;> simp [h0] <;> omega
      rw [hn', MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_neg hne, if_pos rfl, zero_add]
    · have hn' : n = Finsupp.single 0 1 := by
        ext i
        fin_cases i <;> simp <;> omega
      rw [hn', MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl, if_neg hne.symm, add_zero]
  · have hb : MvPowerSeries.HasSubst ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K), 0] :=
      Formalism.G.LogP.hs2 (by simp) (by simp)
    have hz : PowerSeries.subst (0 : MvPowerSeries (Fin 2) K) (lgF K p) = 0 := by
      obtain ⟨u, hu⟩ := PowerSeries.X_dvd_iff.mpr hl0
      have h0s : PowerSeries.HasSubst (0 : MvPowerSeries (Fin 2) K) :=
        PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
      rw [hu, PowerSeries.subst_mul h0s, PowerSeries.subst_X h0s, zero_mul]
    apply lgF_subst_inj p hp2
    · exact MvPowerSeries.constantCoeff_subst_eq_zero hb (fun a => by fin_cases a <;> simp) hF0
    · simp
    · rw [← subst_subst hb (PowerSeries.HasSubst.of_constantCoeff_zero hF0), hFlA,
        MvPowerSeries.subst_add hb, subst_single_var hb, subst_single_var hb]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [hz, add_zero]
end Formalism.InvariantFactorPaths.G7
