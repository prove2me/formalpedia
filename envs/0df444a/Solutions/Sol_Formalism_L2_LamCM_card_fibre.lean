-- Prove2me | solution 1 for Formalism.L2.LamCM.card_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:32:58.268697+00:00
-- url     : https://prove2.me/submissions/2e7ac4c9-35f9-4dae-9b3d-2ccbf694cf2b

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementP
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CmNumbersLink
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_CountSpanSingletonAlgebraMapEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K K1 : Type} [Field K] [NumberField K] [Field K1] [NumberField K1] [Algebra K K1]
namespace Formalism.L2.LamCM
theorem _root_.solution (σ : K →+* ℂ) :
    Nat.card {σ1 : K1 →+* ℂ // σ1.comp (algebraMap K K1) = σ} = Module.finrank K K1 := by
  letI : Algebra K ℂ := σ.toAlgebra
  have e : {σ1 : K1 →+* ℂ // σ1.comp (algebraMap K K1) = σ} ≃ (K1 →ₐ[K] ℂ) :=
    { toFun := fun s => { s.1 with commutes' := fun r => congrArg (fun g : K →+* ℂ => g r) s.2 }
      invFun := fun f => ⟨f.toRingHom, by ext r; exact f.commutes r⟩
      left_inv := fun s => by ext; rfl
      right_inv := fun f => by ext; rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, AlgHom.card]
end Formalism.L2.LamCM
