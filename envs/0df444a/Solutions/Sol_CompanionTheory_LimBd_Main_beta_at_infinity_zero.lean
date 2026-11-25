-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.beta_at_infinity_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:14:45.485506+00:00
-- url     : https://prove2.me/submissions/8a34e977-b707-4225-9236-eb219361ad78

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_BetaAtInfinityZero
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_ae_inSS
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_dil_mem_N
import Theorems.Thm_Formalism_FourierDecayAlt_P_B6_ae_inSS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk MeasureTheory
open scoped InnerProductSpace
namespace CompanionTheory.LimBd.Main
theorem _root_.solution : BetaInfZero := by
  intro k r Wp Wq _ _ _ _ _ _ D F F' h
  unfold B.betaInf B.betaInfTau
  refine integral_eq_zero_of_ae ?_
  filter_upwards [P.B5.ae_inSS D] with p hp
  have hχ : ∀ t, D.χ t ≠ 0 → t ≠ 0 := fun t ht h0 => by
    have := (D.χ_supp (subset_tsupport _ ht)).1
    rw [h0] at this
    norm_num at this
  have h0 : B.regBracket D F F' p = fun _ _ => 0 := by
    funext t₁ t₂
    unfold B.regBracket
    by_cases h1 : D.χ t₁ = 0
    · simp [h1]
    by_cases h2 : D.χ t₂ = 0
    · simp [h2]
    rw [h (B.dilation₂ (t₁, t₂) p) ⟨hp.1, P.B5.dil_mem_N t₁ (hχ _ h1) hp.2.1, hp.2.2.1,
      P.B5.dil_mem_N t₂ (hχ _ h2) hp.2.2.2⟩, mul_zero]
  simp [h0, B.oneMinusDD]
end CompanionTheory.LimBd.Main
