-- Prove2me | solution 1 for Formalism.LIFT.uc_phi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:32:07.030712+00:00
-- url     : https://prove2.me/submissions/d3f6c98c-1b53-47a8-932a-f2fe9dd0e6ad

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
variable {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D] [IsScalarTower ℤ_[ℓ] A D]
namespace Formalism.LIFT
theorem _root_.solution (W : WD B M D) {n : D} (hn : n ∈ W.N) :
    W.QInv (B.Q • W.φ n - n) ∧ W.φ (B.X • n) - B.X • n = B.X • (B.Q • W.φ n - n) := by
  refine ⟨?_, ?_⟩
  · unfold WD.QInv
    rw [smul_sub, smul_smul, ← pow_succ, pow_succ', mul_smul]
    exact W.N.sub_mem (W.N.smul_mem _ (W.φ_N n hn)) (W.N.smul_mem _ hn)
  · rw [W.φ_smul, B.φX, mul_smul, smul_sub]
end Formalism.LIFT
