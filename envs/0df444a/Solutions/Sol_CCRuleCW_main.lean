-- Prove2me | solution 1 for CCRuleCW.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:58:22.551106+00:00
-- url     : https://prove2.me/submissions/31a6c21e-557a-420d-9e9f-f61a74f0846f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_LossBoundNonneg
import Theorems.Thm_CCRuleCW_mem_splits
import Theorems.Thm_CCRuleCW_norm_sum_map_le
import Theorems.Thm_CCRuleCW_mul_sum_map
import Theorems.Thm_CCRuleCW_sum_bound
import Theorems.Thm_CCRuleCW_term_bound
import Theorems.Thm_CCRuleCW_apO_nil
import Theorems.Thm_CCRuleCW_apO_cons
import Theorems.Thm_CCRuleCW_leib
import Theorems.Thm_CCRuleCW_opsW_length
import Theorems.Thm_CCRuleCW_dLR_eq
import Theorems.Thm_CCRuleCW_sub_opsW
import Theorems.Thm_CCRuleCW_loss_bound_nonneg
import Theorems.Thm_CCRuleCW_gN_pos
import Theorems.Thm_CCRuleCW_one_le_gN
import Theorems.Thm_CCRuleCW_smul_ck

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CCRuleCW.apO_nil
attribute [local simp] CCRuleCW.apO_cons

set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace CCRuleCW
theorem _root_.solution (A : ℝ) (D : ℕ) (Q : B.Mat k r → ℂ) (hQ : Good D Q) (F : B.Mat k r → E)
    (hF : C2.CCsc k r A F) : C2.CCsc k r (A - D) (fun g => Q g • F g) := by
  refine ⟨smul_ck Q hQ.1 F hF.1, fun u v hu hv => ?_⟩
  have hl : LieW (opsW u v) := by
    intro o ho
    simp only [opsW, List.mem_append, List.mem_map, List.mem_reverse] at ho
    rcases ho with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
    · exact (hv X hX).1
    · exact (hu X hX).1
  have hterm : ∀ p ∈ splits (opsW u v), ∃ C, ∀ g ∈ B.GV k r,
      B.gN g ^ (A - D - C2.B0 r * ((u.length : ℝ) + v.length)) * ‖apO p.1 Q g • apO p.2 F g‖ ≤
        C * (fun _ => (1 : ℝ)) g := by
    intro p hp
    obtain ⟨h1, h2⟩ := mem_splits _ p hp
    obtain ⟨C₁, hC₁⟩ := hQ.2 p.1 (fun o ho => hl o (h1.subset ho))
    obtain ⟨u', v', hp2, hu', hv'⟩ := sub_opsW u v p.2 h2
    obtain ⟨C₂, hC₂⟩ := hF.2 u' v' (fun X hX => hu X (hu' X hX)) (fun X hX => hv X (hv' X hX))
    refine ⟨max C₁ 0 * max C₂ 0, fun g hg => ?_⟩
    have hlen : ((u'.length : ℝ) + v'.length) ≤ (u.length : ℝ) + v.length := by
      have := h2.length_le
      rw [hp2, opsW_length, opsW_length] at this
      exact_mod_cast this
    rw [norm_smul, mul_one]
    have hb := hC₂ g hg
    rw [dLR_eq, ← hp2] at hb
    exact term_bound (one_le_gN g hg) (loss_bound_nonneg r) hlen (norm_nonneg _) (norm_nonneg _) (hC₁ g hg) hb
  obtain ⟨C, hC⟩ := sum_bound _ (B.GV k r) (fun _ => (1 : ℝ))
    (fun (p : List (Bool × B.Mat k r) × List (Bool × B.Mat k r)) (g : B.Mat k r) => B.gN g ^ (A - D - C2.B0 r * ((u.length : ℝ) + v.length)) *
      ‖apO p.1 Q g • apO p.2 F g‖) hterm
  refine ⟨C, fun g hg => ?_⟩
  rw [dLR_eq, leib (opsW u v) hl Q hQ.1 F hF.1 g hg]
  have hN := Real.rpow_nonneg (gN_pos g hg).le (A - D - C2.B0 r * ((u.length : ℝ) + v.length))
  calc _ ≤ B.gN g ^ (A - D - C2.B0 r * ((u.length : ℝ) + v.length)) *
          ((splits (opsW u v)).map (fun p => ‖apO p.1 Q g • apO p.2 F g‖)).sum :=
        mul_le_mul_of_nonneg_left (norm_sum_map_le _ _) hN
    _ = ((splits (opsW u v)).map (fun p => B.gN g ^ (A - D - C2.B0 r * ((u.length : ℝ) + v.length)) *
          ‖apO p.1 Q g • apO p.2 F g‖)).sum := mul_sum_map _ _ _
    _ ≤ C * 1 := hC g hg
    _ = C := mul_one C
end CCRuleCW
