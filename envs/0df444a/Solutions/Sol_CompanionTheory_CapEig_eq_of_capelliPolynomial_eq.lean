-- Prove2me | solution 1 for CompanionTheory.CapEig.eq_of_capelliPolynomial_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:07:28.974788+00:00
-- url     : https://prove2.me/submissions/adf91edf-0481-46ae-9098-380b54bff7ce

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_BetaAtInfinityZero
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
open Matrix PI.UpqRep Formalism.FourierDecayAlt MeasureTheory CompanionTheory.LimBd.Main CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.CapEig
namespace CompanionTheory.CapEig
theorem _root_.solution {n : ℕ} {μ μ' : Fin n → ℝ} (hμ : StrictAnti μ) (hμ' : StrictAnti μ')
    (h : ∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (μ s : ℂ)) Y = Formalism.QuantumDeterminants.capP (fun s => (μ' s : ℂ)) Y) : μ = μ' := by
  have key : ∀ {a b : Fin n → ℝ}, (∀ Y : ℂ, Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) Y =
      Formalism.QuantumDeterminants.capP (fun s => (b s : ℂ)) Y) → Set.range a ⊆ Set.range b := by
    rintro a b hab _ ⟨s, rfl⟩
    have h0 : Formalism.QuantumDeterminants.capP (fun s => (a s : ℂ)) (-(a s : ℂ)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ s) (by simp)
    rw [hab] at h0
    obtain ⟨t, -, ht⟩ := Finset.prod_eq_zero_iff.1 h0
    refine ⟨t, ?_⟩
    have : ((b t : ℝ) : ℂ) = (a s : ℂ) := by linear_combination ht
    exact_mod_cast this
  exact (hμ.range_inj hμ').1 (Set.Subset.antisymm (key h) (key fun Y => (h Y).symm))
end CompanionTheory.CapEig
