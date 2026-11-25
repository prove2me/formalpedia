-- Prove2me | solution 1 for CompanionTheory.LimBd.Main.mul_mem_spanBox_of_gap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:42:50.777637+00:00
-- url     : https://prove2.me/submissions/5c00e458-20b1-43ac-ad55-009bdc5f8ae5

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_ZuckDualTOfZuckDual
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurH
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_ZuckermanDuality_Letter
import Theorems.Thm_CompanionTheory_LimBd_Main_letter_recursion
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_coe_restrict_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.LimBd.URep.UnitaryRep.coe_restrict_apply



set_option autoImplicit false
noncomputable section
open CompanionTheory CompanionTheory.LimBd CompanionTheory.LimBd.Main
open Formalism.FourierDecayAlt PI.UpqRep Matrix CompanionTheory.LimBd.SchurHpk
open scoped InnerProductSpace
variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : B.Mat k r}
namespace CompanionTheory.LimBd.Main
theorem _root_.solution (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) (hZ : ZuckT t) (hZd : ZuckDualT t) (k r : ℕ)
    (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (d : ℕ) (q φ : B.Mat k r → ℂ)
    (hq : q ∈ Letters k r ^ d) (hφ : IsCoef k r ε lam φ) (hg : PI.ZuckTensor.GapAtLeast ε lam h)
    (hlt : t _ ε + 1 + 2 * (d : ℝ) < h) : q * φ ∈ SpanBox k r ε lam (d : ℝ) := by
  induction d generalizing q with
  | zero =>
    rw [pow_zero, Submodule.mem_one] at hq
    obtain ⟨c, rfl⟩ := hq
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem _ c (Submodule.subset_span ⟨lam, fun s => by simp, hφ⟩)
  | succ d ih =>
    push_cast at hlt ⊢
    have step : Letters k r * SpanBox k r ε lam (d : ℝ) ≤ SpanBox k r ε lam ((d : ℝ) + 1) := by
      unfold Letters
      rw [SpanBox, Submodule.span_mul_span, Submodule.span_le]
      rintro _ ⟨a, ha, b, ⟨μ, hμ, hb⟩, rfl⟩
      have hgμ : PI.ZuckTensor.GapAtLeast ε μ (h - 2 * d) := by
        intro i j hij
        have h1 := hg i j hij
        have h2 := abs_le.1 (hμ i)
        have h3 := abs_le.1 (hμ j)
        rcases abs_cases (lam i - lam j) with h4 | h4 <;> rcases abs_cases (μ i - μ j) with h5 | h5 <;> linarith
      have := letter_recursion t hZ hZd k r ε μ _ a b ha hb hgμ (by linarith)
      refine Submodule.span_mono ?_ this
      rintro ψ ⟨ν, hν, hψ⟩
      refine ⟨ν, fun s => ?_, hψ⟩
      have h2 := abs_le.1 (hμ s)
      have h3 := abs_le.1 (hν s)
      rw [abs_le]
      constructor <;> linarith
    rw [pow_succ'] at hq
    refine Submodule.mul_induction_on hq (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [mul_assoc]
      exact step (Submodule.mul_mem_mul ha (ih b hb (by linarith)))
    · rw [add_mul]
      exact Submodule.add_mem _ ha hb
end CompanionTheory.LimBd.Main
