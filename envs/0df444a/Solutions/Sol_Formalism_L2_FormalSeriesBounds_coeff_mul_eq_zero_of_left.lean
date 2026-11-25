-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.coeff_mul_eq_zero_of_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:13.327794+00:00
-- url     : https://prove2.me/submissions/c349045d-167a-49a8-a5fa-b5c7705624c5

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_FrobeniusBaseCase_BaseCaseFalseGeneral
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LemmaMLin

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
    (hF : ∀ M : σ →₀ ℕ, (∀ b, Q b → M b = 0) → coeff M F = 0) (G : MvPowerSeries σ C)
    (M : σ →₀ ℕ) (hM : ∀ b, Q b → M b = 0) : coeff M (F * G) = 0 := by
  rw [coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' : p.1 + p.2 = M := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [hF p.1 (fun b hb => by
    have h1 := hM b hb
    rw [← hp', Finsupp.add_apply] at h1
    omega), zero_mul]
end Formalism.L2.FormalSeriesBounds
