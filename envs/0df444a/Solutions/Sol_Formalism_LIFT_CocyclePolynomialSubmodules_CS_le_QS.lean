-- Prove2me | solution 1 for Formalism.LIFT.CocyclePolynomialSubmodules.CS_le_QS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:32:01.957351+00:00
-- url     : https://prove2.me/submissions/07abfc6c-1cdb-49f1-ab35-7eb90851d7d1

import Definitions.Def_Formalism_LagrangeIdealLifts_Statement
import Definitions.Def_Formalism_WindowSums_AnnihilatorPolynomials_ZpowVal
import Definitions.Def_Formalism_LagrangeIdealLifts_CocyclePolynomialDivision_UClaim
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_mem_QS
import Theorems.Thm_Formalism_LIFT_CocyclePolynomialSubmodules_mem_CS

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
open Formalism.LIFT.CocyclePolynomialSubmodules
variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A]
  {B : Base ℓ A} {M : ℕ} {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
  [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D)
namespace Formalism.LIFT.CocyclePolynomialSubmodules
theorem _root_.solution : CS W ≤ QS W := by
  intro ω hω
  obtain ⟨y, hy, rfl⟩ := (mem_CS W).mp hω
  exact (QS W).smul_mem B.X ((mem_QS W).mpr hy)
end Formalism.LIFT.CocyclePolynomialSubmodules
