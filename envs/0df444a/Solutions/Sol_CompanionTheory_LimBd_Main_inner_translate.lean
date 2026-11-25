-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.inner_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:02:52.669955+00:00
-- url     : https://prove2.me/submissions/b5aa981f-2a5e-4c0c-8150-db155f05d330

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_BetaAtInfinityZero
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsEquivalent_symm
import Theorems.Thm_PI_UnitaryGroupMassFormula_CapelliEig_unitary_Hecke_group


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk MeasureTheory
open scoped InnerProductSpace
namespace CompanionTheory.LimBd.Main
theorem _root_.solution {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : B.Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (UH (Hpk k r)) σ) {a g b : B.Mat k r} (ha : a ∈ UH (Hpk k r))
    (hg : g ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) (v w : H) :
    ⟪w, σ (a * g * b) v⟫_ℂ = ⟪σ a⁻¹ w, σ g (σ b v)⟫_ℂ := by
  obtain ⟨hu, hai, hm⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r a ha
  let L : H →ₗᵢ[ℂ] H := ⟨(σ a : H →ₗ[ℂ] H), hσ.2.1 a ha⟩
  have e : σ a (σ a⁻¹ w) = w := by
    have := hσ.1.2 a ha _ hai
    rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hu), hσ.1.1] at this
    exact (congrArg (fun T : H →L[ℂ] H => T w) this).symm
  rw [hσ.1.2 _ (hm g hg) b hb, hσ.1.2 a ha g hg, ← L.inner_map_map (σ a⁻¹ w)]
  show _ = ⟪σ a (σ a⁻¹ w), _⟫_ℂ
  rw [e]
  rfl
end CompanionTheory.LimBd.Main
