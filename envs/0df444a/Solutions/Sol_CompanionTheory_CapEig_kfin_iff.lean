-- Prove2me | solution 1 for CompanionTheory.CapEig.kfin_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:43:55.369748+00:00
-- url     : https://prove2.me/submissions/9c86f971-4708-4812-83a4-b296f44dcb5e

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_CapelliEigenvalues_BetaAtInfinityZero
import Theorems.Thm_CompanionTheory_LimBd_SchurHpk_forth_mem
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
theorem _root_.solution (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (P : B.Mat k r) (H : Type) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : B.Mat k r → (H →L[ℂ] H)) (v : H) (hP : IsCayleyU k r ε P) :
    IsKFinHpk (k := k) (r := r) σ v ↔ IsKFin ε (fun g => σ (P⁻¹ * g * P)) v := by
  have hinv : P⁻¹ = star P := Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hP.2)
  have hPi : P⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hinv ▸ Unitary.star_mem hP.2
  constructor
  · rintro ⟨S, hS, hv, hst⟩
    refine ⟨S, hS, hv, fun g hg x hx => hst _ ⟨back_mem hP.1 ?_, ?_⟩ x hx⟩
    · show gᴴ * Jm ε * g = Jm ε
      have h1 : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hg.1
      rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ hPi hg.1) hP.2
  · rintro ⟨S, hS, hv, hst⟩
    refine ⟨S, hS, hv, fun x hx y hy => ?_⟩
    have hu : P * x * P⁻¹ ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ :=
      Submonoid.mul_mem _ (Submonoid.mul_mem _ hP.2 hx.2) hPi
    have hJ : (P * x * P⁻¹)ᴴ * Jm ε * (P * x * P⁻¹) = Jm ε := forth_mem hP.1 hx.1
    have h1 : (P * x * P⁻¹) * (P * x * P⁻¹)ᴴ = 1 := Unitary.mul_star_self_of_mem hu
    have hK : P * x * P⁻¹ ∈ Kset ε := by
      refine ⟨hu, ?_⟩
      generalize P * x * P⁻¹ = g at hJ h1
      calc g * Jm ε = g * (gᴴ * Jm ε * g) := by rw [hJ]
        _ = (g * gᴴ) * Jm ε * g := by simp only [Matrix.mul_assoc]
        _ = Jm ε * g := by rw [h1, Matrix.one_mul]
    have := hst _ hK y hy
    simpa only [back_forth hP.1] using this
end CompanionTheory.CapEig
