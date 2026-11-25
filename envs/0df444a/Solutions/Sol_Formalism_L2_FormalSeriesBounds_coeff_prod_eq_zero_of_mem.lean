-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_prod_eq_zero_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:01:55.419841+00:00
-- url     : https://prove2.me/submissions/c5b1e0fa-bc63-461b-82b3-739d0728e110

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
theorem _root_.solution {σ ρ : Type} (Q : σ → Prop) (s : Finset ρ)
    (F : ρ → MvPowerSeries σ C) {w : ρ} (hw : w ∈ s)
    (hF : ∀ M : σ →₀ ℕ, (∀ b, Q b → M b = 0) → coeff M (F w) = 0)
    (M : σ →₀ ℕ) (hM : ∀ b, Q b → M b = 0) : coeff M (∏ i ∈ s, F i) = 0 := by
  rw [← Finset.mul_prod_erase s F hw]
  exact coeff_mul_eq_zero_of_left Q hF _ M hM
end Formalism.L2.FormalSeriesBounds
