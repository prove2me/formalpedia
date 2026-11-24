-- Prove2me | solution 1 for Formalism.LIFT.uc_pull_xn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:31:57.191087+00:00
-- url     : https://prove2.me/submissions/a8684c67-4076-4c87-91aa-569e1caa59dc

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
theorem _root_.solution (S : SES W₀ W₁ W₂) {m : D₁} (hm : m ∈ W₁.N) (h0 : S.π.f (B.X • m) = 0) :
    ∃ m₀ ∈ W₀.N, S.ι.f (B.X • m₀) = B.X • m := by
  have h1 : S.π.f m = 0 := by
    apply W₂.X_inj
    rw [← map_smul]
    exact h0
  obtain ⟨m₀, rfl⟩ := (S.exact m).mp h1
  exact ⟨m₀, S.sat m₀ hm, map_smul _ _ _⟩
end Formalism.LIFT
