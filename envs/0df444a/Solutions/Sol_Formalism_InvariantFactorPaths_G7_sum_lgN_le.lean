-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.sum_lgN_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:38:42.945316+00:00
-- url     : https://prove2.me/submissions/28edb125-1fae-4401-a31b-b88fcc116a71

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementAB
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_PathBasisOfCount
import Definitions.Def_Formalism_GrowthSums_FactorialBaseGrowth_QuadraticExponentIdentity
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_ABArith
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_lgN_mono

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.GrowthSums (gamP rhoP gainG excessGain)
namespace Formalism.InvariantFactorPaths.G7
theorem _root_.solution (p : ℕ) (hp : 1 < p) (A : ℕ) (f : ℕ → ℕ) (E : Finset ℕ)
    (h : ∀ e', p ^ (2 * e' + 1) * f e' ≤ A) :
    ∑ e' ∈ E, lgN p (f e') ≤ lgN p A ^ 2 := by
  have hle : ∀ e', f e' ≤ A := fun e' =>
    le_trans (Nat.le_mul_of_pos_left _ (pow_pos (by omega) _)) (h e')
  have hsupp : ∀ e' ∈ E, lgN p (f e') ≠ 0 → e' < lgN p A := by
    intro e' _ hne
    have hf : f e' ≠ 0 := by
      intro h0
      apply hne
      simp [lgN, h0]
    have h1 : p ^ (2 * e' + 1) ≤ A :=
      le_trans (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hf)) (h e')
    have hA : A ≠ 0 := by
      have : 0 < p ^ (2 * e' + 1) := pow_pos (by omega) _
      omega
    have h2 := Nat.le_log_of_pow_le hp h1
    simp only [lgN, hA, if_false]
    omega
  rw [← Finset.sum_filter_of_ne hsupp]
  calc ∑ e' ∈ E.filter (fun e' => e' < lgN p A), lgN p (f e')
      ≤ ∑ _e' ∈ E.filter (fun e' => e' < lgN p A), lgN p A :=
        Finset.sum_le_sum (fun e' _ => lgN_mono p (hle e'))
    _ = (E.filter (fun e' => e' < lgN p A)).card * lgN p A := by rw [sum_const, smul_eq_mul]
    _ ≤ lgN p A * lgN p A := by
        apply Nat.mul_le_mul_right
        calc (E.filter (fun e' => e' < lgN p A)).card ≤ (range (lgN p A)).card :=
              card_le_card (fun x hx => by
                simp only [mem_filter, mem_range] at hx ⊢
                exact hx.2)
          _ = lgN p A := card_range _
    _ = lgN p A ^ 2 := (sq _).symm
end Formalism.InvariantFactorPaths.G7
