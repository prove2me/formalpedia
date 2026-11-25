-- Prove2me | solution 1 for Formalism.IndefR.LiftF.IsKap.unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:05:32.349071+00:00
-- url     : https://prove2.me/submissions/e6046a72-7eba-4d07-996e-c8ec4b170f18

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DatumF
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HasInfExpF

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open Formalism Formalism.IndefR Formalism.IndefR.LiftF
variable {N : Type*} [AddCommGroup N] [Module ℂ N]
namespace Formalism.IndefR.LiftF
namespace IsKap
theorem _root_.solution {Tup Sig : Type*} {m : ℕ} {dnup : Tup → N →ₗ[ℂ] N} {partE : Sig → Submodule ℂ N}
    {lam : Tup → ℕ → Sig → ℝ} {κ κ' : ℝ} (h : IsKap m dnup partE lam κ) (h' : IsKap m dnup partE lam κ')
    (μ : Tup) (σ : Sig) (hσ : partE σ ≠ ⊥) (hl : ∏ j ∈ Finset.Icc 1 m, lam μ j σ ≠ 0) : κ = κ' := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ
  have h2 : (((κ * ∏ j ∈ Finset.Icc 1 m, lam μ j σ : ℝ) : ℂ) -
      ((κ' * ∏ j ∈ Finset.Icc 1 m, lam μ j σ : ℝ) : ℂ)) • x = 0 := by
    rw [sub_smul, ← h μ σ x hx, ← h' μ σ x hx, sub_self]
  rcases smul_eq_zero.1 h2 with h3 | h3
  · have h4 : κ * ∏ j ∈ Finset.Icc 1 m, lam μ j σ = κ' * ∏ j ∈ Finset.Icc 1 m, lam μ j σ := by
      exact_mod_cast sub_eq_zero.1 h3
    exact mul_right_cancel₀ hl h4
  · exact absurd h3 hx0
end IsKap
end Formalism.IndefR.LiftF
