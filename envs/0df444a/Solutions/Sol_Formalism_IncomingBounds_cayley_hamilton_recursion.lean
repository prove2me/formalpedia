-- Prove2me | solution 1 for Formalism.IncomingBounds.cayley_hamilton_recursion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:56:10.927475+00:00
-- url     : https://prove2.me/submissions/7217690f-f3c3-4a8f-aeda-27121f5de603

import Definitions.Def_Formalism_IncomingBounds_LevelTail
import Definitions.Def_Formalism_IncomingBounds_FrobOrbitPeriod
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_Series
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
namespace Formalism.IncomingBounds
private lemma summable_div_pow_succ {ι : Type} [Fintype ι] (l : ℝ) (hl : 1 < l)
    (u : ι → ℝ) (e : ℕ → ι) : Summable (fun k : ℕ => u (e k) / l ^ (k + 1)) := by
  have hl0 : 0 < l := by linarith
  have hq0 : 0 ≤ l⁻¹ := inv_nonneg.mpr hl0.le
  have hq1 : l⁻¹ < 1 := inv_lt_one_of_one_lt₀ hl
  refine Summable.of_norm_bounded (g := fun k : ℕ => (∑ i, |u i|) * l⁻¹ * (l⁻¹) ^ k)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _) ?_
  intro k
  have h1 : |u (e k)| ≤ ∑ i, |u i| :=
    Finset.single_le_sum (f := fun i => |u i|) (fun i _ => abs_nonneg _) (Finset.mem_univ _)
  have h2 : (l ^ (k + 1))⁻¹ = l⁻¹ * l⁻¹ ^ k := by rw [← pow_succ', inv_pow]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos hl0 _), div_eq_mul_inv, h2, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hq0) (by positivity)
end Formalism.IncomingBounds
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.IncomingBounds
namespace Formalism.IncomingBounds
theorem _root_.solution : CHRecursion := by
  intro d _ l hl h p x
  have hl0 : 0 < l := by linarith
  have hl0' : l ≠ 0 := hl0.ne'
  have hs : ∀ a : ZMod d, Summable (fun k : ℕ => (h - p (a + (k : ZMod d))) / l ^ k) := by
    intro a
    have := summable_div_pow_succ l hl (fun b => h - p b) (fun k => a + ((k + 1 : ℕ) : ZMod d))
    exact (summable_nat_add_iff 1).mp this
  have key : ∀ a : ZMod d, l * chSol d l h p (a - 1) = (h - p a) + chSol d l h p a := by
    intro a
    unfold chSol
    rw [← tsum_mul_left]
    have e1 : (fun k : ℕ => l * ((h - p (a - 1 + ((k + 1 : ℕ) : ZMod d))) / l ^ (k + 1))) =
        (fun k : ℕ => (h - p (a + (k : ZMod d))) / l ^ k) := by
      funext k
      have : a - 1 + ((k + 1 : ℕ) : ZMod d) = a + (k : ZMod d) := by push_cast; ring
      rw [this, pow_succ]
      field_simp
    rw [e1, (hs a).tsum_eq_zero_add]
    congr 1
    simp
  constructor
  · intro hx a
    have hrec : ∀ b : ZMod d, x b - chSol d l h p b = l * (x (b - 1) - chSol d l h p (b - 1)) := by
      intro b; rw [mul_sub]; linarith [hx b, key b]
    have hit : ∀ n : ℕ, ∀ b : ZMod d,
        x b - chSol d l h p b = l ^ n * (x (b - n) - chSol d l h p (b - n)) := by
      intro n
      induction n with
      | zero => intro b; simp
      | succ n ih =>
        intro b
        rw [ih b, hrec (b - n)]
        have : b - (n : ZMod d) - 1 = b - ((n + 1 : ℕ) : ZMod d) := by push_cast; ring
        rw [this, pow_succ]; ring
    have hd := hit d a
    rw [ZMod.natCast_self, sub_zero] at hd
    have hld : 1 < l ^ d := one_lt_pow₀ hl (NeZero.ne d)
    have h0 : (l ^ d - 1) * (x a - chSol d l h p a) = 0 := by
      rw [sub_mul, one_mul, ← hd, sub_self]
    rcases mul_eq_zero.mp h0 with h1 | h1
    · linarith
    · linarith
  · intro hx a
    rw [hx a, hx (a - 1)]
    linarith [key a]
end Formalism.IncomingBounds
