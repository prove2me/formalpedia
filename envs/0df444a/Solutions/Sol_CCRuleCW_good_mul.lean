-- Prove2me | solution 1 for CCRuleCW.good_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:58:22.513706+00:00
-- url     : https://prove2.me/submissions/aa4e26ca-b329-4da1-ad66-abf41ee8de27

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_GoodMonoProd
import Theorems.Thm_CCRuleCW_gN_pos
import Theorems.Thm_CCRuleCW_leib
import Theorems.Thm_CCRuleCW_mem_splits
import Theorems.Thm_CCRuleCW_norm_sum_map_le
import Theorems.Thm_CCRuleCW_smooth_ck
import Theorems.Thm_CCRuleCW_sum_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexConjugate ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace CCRuleCW
theorem _root_.solution {a b : ℕ} (Q₁ Q₂ : B.Mat k r → ℂ) (h₁ : Good a Q₁) (h₂ : Good b Q₂) :
    Good (a + b) (fun g => Q₁ g * Q₂ g) := by
  refine ⟨h₁.1.mul h₂.1, fun ops hl => ?_⟩
  have hterm : ∀ p ∈ splits ops, ∃ C, ∀ g ∈ B.GV k r,
      ‖apO p.1 Q₁ g • apO p.2 Q₂ g‖ ≤ C * B.gN g ^ (a + b) := by
    intro p hp
    obtain ⟨s1, s2⟩ := mem_splits _ p hp
    obtain ⟨C₁, hC₁⟩ := h₁.2 p.1 (fun o ho => hl o (s1.subset ho))
    obtain ⟨C₂, hC₂⟩ := h₂.2 p.2 (fun o ho => hl o (s2.subset ho))
    refine ⟨max C₁ 0 * max C₂ 0, fun g hg => ?_⟩
    rw [norm_smul, pow_add]
    have hN : 0 ≤ B.gN g := (gN_pos g hg).le
    have e1 : ‖apO p.1 Q₁ g‖ ≤ max C₁ 0 * B.gN g ^ a :=
      (hC₁ g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN _))
    have e2 : ‖apO p.2 Q₂ g‖ ≤ max C₂ 0 * B.gN g ^ b :=
      (hC₂ g hg).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hN _))
    calc _ ≤ (max C₁ 0 * B.gN g ^ a) * (max C₂ 0 * B.gN g ^ b) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg (le_max_right _ _) (pow_nonneg hN _))
      _ = _ := by ring
  obtain ⟨C, hC⟩ := sum_bound _ (B.GV k r) (fun g => B.gN g ^ (a + b))
    (fun (p : List (Bool × B.Mat k r) × List (Bool × B.Mat k r)) (g : B.Mat k r) =>
      ‖apO p.1 Q₁ g • apO p.2 Q₂ g‖) hterm
  refine ⟨C, fun g hg => ?_⟩
  have e : (fun g => Q₁ g * Q₂ g) = (fun g => Q₁ g • Q₂ g) := rfl
  rw [e, leib ops hl Q₁ h₁.1 Q₂ (smooth_ck Q₂ h₂.1) g hg]
  exact (norm_sum_map_le _ _).trans (hC g hg)
end CCRuleCW
