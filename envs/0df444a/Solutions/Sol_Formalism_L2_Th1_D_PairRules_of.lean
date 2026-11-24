-- Prove2me | solution 1 for Formalism.L2.Th1.D.PairRules_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:32:05.648717+00:00
-- url     : https://prove2.me/submissions/6a0e7de0-bf37-4443-b5a2-6dbda66e7e57

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FinalS
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_SubstFirstCoboundaryThree
import Theorems.Thm_Formalism_L2_Th1_D_Pair_hs2
import Theorems.Thm_Formalism_L2_Th1_D_Pair_hs3
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_single_var
import Theorems.Thm_Formalism_L2_Th1_D_Pair_constantCoeff_inVar_eq_zero
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst2_comp
import Theorems.Thm_Formalism_L2_Th1_D_Pair_cc_ps
import Theorems.Thm_Formalism_L2_Th1_D_Pair_addC_log
import Theorems.Thm_Formalism_L2_Th1_D_Pair_log_law
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_first_coboundary_three
import Theorems.Thm_Formalism_L2_Th1_D_Pair_subst_swap2
import Theorems.Thm_Formalism_L2_Th1_D_Pair_isMul_mulF
import Theorems.Thm_Formalism_L2_Th1_D_Pair_log_mul
import Theorems.Thm_P2M_Formalism_L2_Th1_D_Pair_subst_zero__1c375b19f91e
import Theorems.Thm_Formalism_L2_Th1_D_Pair_simeq_of_sub
import Theorems.Thm_Formalism_G_LogP_hs2
import Theorems.Thm_Formalism_G_LogP_hs3
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_CoboundarySeries_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FormalGroupLaws_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_FrobeniusSubstitution_subst_single_var
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_hs3
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_GramFrameCompositionLinFacts_subst_swap2
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_equivalence_rules
import Theorems.Thm_P2M_Formalism_G_LogP_subst_zero__b4a287294211

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
namespace Pair
section Alg
variable {K : Type} [Field K]
private theorem hasSubst_finite_of_constantCoeff_eq_zero {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent fun s => by rw [ha s]; exact IsNilpotent.zero
end Alg
section NormedLin
variable {K : Type} [NormedField K]
end NormedLin
section Normed
variable {K : Type} [NormedField K] [CharZero K]
end Normed
end Pair
open Pair
private theorem constantCoeff_subst_vec_pair_eq_zero {K : Type} [Field K] {τ : Type} {a b : MvPowerSeries τ K}
    (ha : constantCoeff a = 0) (hb : constantCoeff b = 0) {F : MvPowerSeries (Fin 2) K}
    (hF0 : constantCoeff F = 0) : constantCoeff (subst ![a, b] F) = 0 := by
  have hx : ∀ i : Fin 2, constantCoeff (![a, b] i) = 0 := by
    intro i; fin_cases i <;> first | exact ha | exact hb | simp [ha, hb]
  first
  | exact constantCoeff_subst_eq_zero hx F hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hx hF0
  | exact constantCoeff_subst_eq_zero hx hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hx F hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) F hx hF0
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) hF0 hx
  | exact constantCoeff_subst_eq_zero (hasSubst_finite_of_constantCoeff_eq_zero hx) F hF0 hx
  | (apply constantCoeff_subst_eq_zero <;> first | assumption | exact hasSubst_finite_of_constantCoeff_eq_zero hx)
end Formalism.L2.Th1.D
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 in3 cob UnrOK IsLawOfLog SimeqRules)
open MvPowerSeries
open Pair
namespace Formalism.L2.Th1.D
theorem _root_.solution (hE : ExpSpec) (hIP : IPLemma) : PairRules := by
  have hS : SimeqRules := by
    first
    | exact Formalism.InvariantFactorPaths.G7.equivalence_rules
    | exact equivalence_rules
  unfold PairRules
  intro K _ _ _ l σ hU F hF be0 hF1 τ _
  obtain ⟨hF0, -, hFc⟩ := hF
  obtain ⟨-, hd, hds⟩ := hF1
  have hl : 2 ≤ l := by have := hU.2.1; omega
  have lift : ∀ G : MvPowerSeries τ K, IP l σ G → ∃ g : MvPowerSeries τ K, constantCoeff g = 0 ∧
      Integral g ∧ PowerSeries.subst g (lgF K l) = G := fun G hG => hIP K l σ hU τ G hG
  have tr : ∀ g h : MvPowerSeries τ K, constantCoeff g = 0 → constantCoeff h = 0 →
      subst ![PowerSeries.subst g (lgF K l), PowerSeries.subst h (lgF K l)] (addC l be0) =
        subst ![g, h] be0 :=
    fun g h hg hh => addC_log hE hl hg hh be0
  refine ⟨?_, ?_, ?_⟩
  · intro G G' H hG hG' hH
    obtain ⟨g, hg0, hgI, rfl⟩ := lift G hG
    obtain ⟨g', hg0', hgI', rfl⟩ := lift G' hG'
    obtain ⟨h, hh0, hhI, rfl⟩ := lift H hH
    rw [← log_law hF0 hFc hg0 hg0', tr _ _ (constantCoeff_subst_vec_pair_eq_zero hg0 hg0' hF0) hh0, tr _ _ hg0 hh0,
      tr _ _ hg0' hh0]
    apply simeq_of_sub
    have h0 : ∀ i, constantCoeff (![g, g', h] i) = 0 := by
      intro i; fin_cases i <;> first | exact hg0 | exact hg0' | exact hh0
    have hI : ∀ i, Integral (![g, g', h] i) := by
      intro i; fin_cases i <;> first | exact hgI | exact hgI' | exact hhI
    have hh := (hS K (Fin 3)).2.2.2.2 τ (d1 F be0) 0 ![g, g', h] h0 hI hd
    rw [subst_first_coboundary_three hF0 hg0 hg0' hh0, subst_zero' (hs3 hg0 hg0' hh0)] at hh
    exact hh
  · intro G H H' hG hH hH'
    obtain ⟨g, hg0, hgI, rfl⟩ := lift G hG
    obtain ⟨h, hh0, hhI, rfl⟩ := lift H hH
    obtain ⟨h', hh0', hhI', rfl⟩ := lift H' hH'
    rw [← log_law hF0 hFc hh0 hh0', tr _ _ hg0 (constantCoeff_subst_vec_pair_eq_zero hh0 hh0' hF0), tr _ _ hg0 hh0,
      tr _ _ hg0 hh0']
    apply simeq_of_sub
    have h0 : ∀ i, constantCoeff (![h, h', g] i) = 0 := by
      intro i; fin_cases i <;> first | exact hh0 | exact hh0' | exact hg0
    have hI : ∀ i, Integral (![h, h', g] i) := by
      intro i; fin_cases i <;> first | exact hhI | exact hhI' | exact hgI
    have hh := (hS K (Fin 3)).2.2.2.2 τ (d1 F (swap2 be0)) 0 ![h, h', g] h0 hI hds
    rw [subst_first_coboundary_three hF0 hh0 hh0' hg0, subst_zero' (hs3 hh0 hh0' hg0),
      subst_swap2 (constantCoeff_subst_vec_pair_eq_zero hh0 hh0' hF0) hg0, subst_swap2 hh0 hg0, subst_swap2 hh0' hg0] at hh
    exact hh
  · intro hF2 c G H hc hcc hG hH
    obtain ⟨g, hg0, hgI, rfl⟩ := lift G hG
    obtain ⟨h, hh0, hhI, rfl⟩ := lift H hH
    have he := isMul_mulF hE hl c
    have he' := isMul_mulF hE hl (σ c)
    rw [← log_mul he hg0, ← log_mul he' hh0, tr _ _ (cc_ps hg0 he.1) hh0,
      tr _ _ hg0 (cc_ps hh0 he'.1)]
    have h0 : ∀ i, constantCoeff (![g, h] i) = 0 := by
      intro i; fin_cases i <;> first | exact hg0 | exact hh0
    have hI : ∀ i, Integral (![g, h] i) := by
      intro i; fin_cases i <;> first | exact hgI | exact hhI
    have hh := (hS K (Fin 2)).2.2.2.2 τ _ _ ![g, h] h0 hI (hF2 c hc hcc _ _ he he')
    have h2 := hs2 hg0 hh0
    have hX : ∀ i : Fin 2, constantCoeff (X i : MvPowerSeries (Fin 2) K) = 0 := fun i => by simp
    rw [subst2_comp h2 (constantCoeff_inVar_eq_zero (0 : Fin 2) he.1) (hX 1), subst2_comp h2 (hX 0) (constantCoeff_inVar_eq_zero (1 : Fin 2) he'.1),
      subst_single_var h2, subst_single_var h2] at hh
    simp only [subst_X h2] at hh
    exact hh
end Formalism.L2.Th1.D
