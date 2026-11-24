-- Prove2me | solution 1 for Formalism.LIFT.uc_pull_qinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:31:56.503979+00:00
-- url     : https://prove2.me/submissions/2974cf7f-541d-463a-8592-724ca3abbbfb

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.LIFT
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}
variable {D₀ D₁ D₂ : Type}
    [AddCommGroup D₀] [Module A D₀] [Module ℤ_[ℓ] D₀] [IsScalarTower ℤ_[ℓ] A D₀]
    [AddCommGroup D₁] [Module A D₁] [Module ℤ_[ℓ] D₁] [IsScalarTower ℤ_[ℓ] A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module ℤ_[ℓ] D₂] [IsScalarTower ℤ_[ℓ] A D₂]
    {W₀ : WD B M D₀} {W₁ : WD B M D₁} {W₂ : WD B M D₂}
namespace Formalism.LIFT
theorem _root_.solution (S : SES W₀ W₁ W₂) {y : D₁} (hy : W₁.QInv y) (h0 : S.π.f y = 0) :
    ∃ y₀, W₀.QInv y₀ ∧ S.ι.f y₀ = y := by
  obtain ⟨y₀, rfl⟩ := (S.exact y).mp h0
  refine ⟨y₀, ?_, rfl⟩
  unfold WD.QInv at *
  apply S.sat
  rw [map_smul]
  exact hy
end Formalism.LIFT
