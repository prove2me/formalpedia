-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_pow_eq_zero_of_base
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:06.220882+00:00
-- url     : https://prove2.me/submissions/9535bf58-9075-4815-b75b-2370e747ff58

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_coeff_mul_eq_zero_of_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.BaseCaseIdentities (OrdGE NoConst)
variable {C : Type} [Field C] {I : Fin 2 → Type} [∀ g, Fintype (I g)] {ι ι' : Type} [Fintype ι]
  [Fintype ι']
namespace Formalism.L2.FormalSeriesBounds
theorem _root_.solution {σ : Type} (Q : σ → Prop) {F : MvPowerSeries σ C}
    (hF : ∀ M : σ →₀ ℕ, (∀ b, Q b → M b = 0) → coeff M F = 0) {n : ℕ} (hn : n ≠ 0)
    (M : σ →₀ ℕ) (hM : ∀ b, Q b → M b = 0) : coeff M (F ^ n) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [pow_succ']
  exact coeff_mul_eq_zero_of_left Q hF _ M hM
end Formalism.L2.FormalSeriesBounds
