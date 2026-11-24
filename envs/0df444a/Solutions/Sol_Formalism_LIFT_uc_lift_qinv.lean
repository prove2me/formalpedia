-- Prove2me | solution 1 for Formalism.LIFT.uc_lift_qinv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:32:06.224193+00:00
-- url     : https://prove2.me/submissions/bfbafb3d-d87b-4437-940a-f4348493635e

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ValProd
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UChase
import Theorems.Thm_Formalism_LIFT_uc_bij
import Theorems.Thm_Formalism_LIFT_uc_smul_comm_A

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
theorem _root_.solution (S : SES W₀ W₁ W₂) {e : ℕ} (hK : CokerKilled S e) {y : D₂} (hy : W₂.QInv y) :
    ∃ y₁, W₁.QInv y₁ ∧ S.π.f y₁ = ((ℓ : ℤ_[ℓ]) ^ e) • y := by
  obtain ⟨n₁, hn₁, he⟩ := hK _ hy
  obtain ⟨y₁, hy₁⟩ := (uc_bij W₁ M).2 n₁
  refine ⟨y₁, ?_, ?_⟩
  · show B.Q ^ M • y₁ ∈ W₁.N
    rw [show B.Q ^ M • y₁ = n₁ from hy₁]
    exact hn₁
  · apply (uc_bij W₂ M).1
    show B.Q ^ M • S.π.f y₁ = B.Q ^ M • (((ℓ : ℤ_[ℓ]) ^ e) • y)
    rw [← map_smul, show B.Q ^ M • y₁ = n₁ from hy₁, he, ← algebraMap_smul A ((ℓ : ℤ_[ℓ]) ^ e) (B.Q ^ M • y),
      ← algebraMap_smul A ((ℓ : ℤ_[ℓ]) ^ e) y, uc_smul_comm_A]
end Formalism.LIFT
