-- Prove2me | solution 1 for Formalism.L2.Th1.B.E3.cube_relation_from_parallelograms
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:14:32.651399+00:00
-- url     : https://prove2.me/submissions/5ad4ea2a-4f58-47cd-a793-e26f42fe4ace

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_FinalB
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_StatementD
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_FirstLevelOfThreeVarParallelogram
import Theorems.Thm_Formalism_L2_Th1_B_E3_parallelogram_three_sub_pairs
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_Formalism_L2_Th1_B_integral_mvPowerSeries_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.B Formalism.L2.Th1.B.E3
open Formalism.DworkPowerSeriesWeights (Integral)
open Formalism.InvariantFactorPaths.G7 (Simeq at1 cob d1 in3 swap2 DivAB equivalence_rules)
namespace Formalism.L2.Th1.B.E3
theorem _root_.solution : CubeFromPars := by
  intro K _ _ _ F l i f hF hi hp h3
  obtain ⟨_, hsymm, _, hadd, _⟩ := equivalence_rules K (Fin 3)
  have hsubS : ∀ a b : MvPowerSeries (Fin 3) K, Simeq a 0 → Simeq b 0 → Simeq (a - b) 0 := by
    intro a b ha hb
    have h := hadd a 0 0 b ha (hsymm _ _ hb)
    rw [add_zero, zero_add] at h
    unfold Simeq at h ⊢
    simpa using h
  have hpar : ∀ j k : Fin 3,
      Simeq (MvPowerSeries.subst ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k]
        (par F i f)) 0 := by
    intro j k
    have hc : ∀ m : Fin 2, MvPowerSeries.constantCoeff
        (![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] m) = 0 := by
      intro m; fin_cases m <;> simp
    have hI : ∀ m : Fin 2, Integral
        (![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k] m) := by
      intro m; fin_cases m <;> simp [integral_mvPowerSeries_X]
    have h := (equivalence_rules K (Fin 2)).2.2.2.2 (Fin 3) (par F i f) 0 _ hc hI hp
    have hz : MvPowerSeries.subst ![(MvPowerSeries.X j : MvPowerSeries (Fin 3) K), MvPowerSeries.X k]
        (0 : MvPowerSeries (Fin 2) K) = 0 := by
      rw [← MvPowerSeries.coe_substAlgHom (MvPowerSeries.hasSubst_of_constantCoeff_zero hc), map_zero]
    rwa [hz] at h
  rw [← parallelogram_three_sub_pairs F hF.1 i f hi.1]
  exact hsubS _ _ (hsubS _ _ (hsubS _ _ h3 (hpar 0 1)) (hpar 0 2)) (hpar 1 2)
end Formalism.L2.Th1.B.E3
