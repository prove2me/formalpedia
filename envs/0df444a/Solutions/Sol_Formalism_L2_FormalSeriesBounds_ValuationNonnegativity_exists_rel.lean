-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.ValuationNonnegativity.exists_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:40:52.968918+00:00
-- url     : https://prove2.me/submissions/6a89cd72-3ebb-4b00-bb3c-a7095754a852

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieFB
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_IndependenceBoundRaw
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_ValuationNonnegativity_valuation_nonneg_div

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
variable {C : Type} [Field C] {V : VF C}
namespace Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
theorem _root_.solution {N m : ℕ} (hm : m < N) (B : Fin N → Fin m → C) :
    ∃ β : Fin N → C, (∀ ν, V.Ge 0 (β ν)) ∧ (∃ ν, ¬ V.MM (β ν)) ∧ ∀ r, ∑ ν, β ν * B ν r = 0 := by
  let f : (Fin N → C) →ₗ[C] (Fin m → C) := Matrix.vecMulLinear (Matrix.of B)
  have hk : LinearMap.ker f ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hm)
  obtain ⟨β, hβ, hne⟩ := (Submodule.ne_bot_iff _).mp hk
  have hrel : ∀ r, ∑ ν, β ν * B ν r = 0 := fun r => by
    have := congrFun (LinearMap.mem_ker.mp hβ) r
    simpa [f, Matrix.vecMulLinear_apply, Matrix.vecMul, dotProduct] using this
  obtain ⟨ν1, hν1⟩ : ∃ ν, β ν ≠ 0 := by
    by_contra hc; push Not at hc; exact hne (funext hc)
  obtain ⟨ν0, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun ν => V.v (β ν))
    ⟨ν1, Finset.mem_univ _⟩
  have h0 : β ν0 ≠ 0 := by
    intro h
    have := hmin ν1 (Finset.mem_univ _)
    rw [h, V.v.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact hν1 this
  refine ⟨fun ν => β ν / β ν0, fun ν => valuation_nonneg_div h0 (hmin ν (Finset.mem_univ _)), ⟨ν0, ?_⟩, fun r => ?_⟩
  · show ¬ V.MM (β ν0 / β ν0)
    rw [div_self h0]; unfold VF.MM; rw [V.v.map_one]; exact lt_irrefl 0
  · simp_rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div, hrel r, zero_div]
end Formalism.L2.FormalSeriesBounds.ValuationNonnegativity
