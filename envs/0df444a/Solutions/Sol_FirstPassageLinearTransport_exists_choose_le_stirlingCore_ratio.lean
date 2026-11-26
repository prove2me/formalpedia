-- Prove2me | solution 1 for FirstPassageLinearTransport.exists_choose_le_stirlingCore_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:50.748883+00:00
-- url     : https://prove2.me/submissions/85fdea89-17b6-40e7-902b-9671d28b1d06

import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_FirstPassageLinearTransport_EntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Theorems.Thm_FirstPassageLinearTransport_exists_factorial_stirlingCore_bounds
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution :
    ∃ C : ℝ, 0 < C ∧
      ∀ r k : ℕ, 0 < k → k < r →
        (r.choose k : ℝ) ≤
          C * stirlingCore r /
            (stirlingCore k * stirlingCore (r - k)) := by
  obtain ⟨a, b, ha, hb, hfac⟩ := exists_factorial_stirlingCore_bounds
  refine ⟨b / (a * a), div_pos hb (mul_pos ha ha), ?_⟩
  intro r k hk hkr
  have hr : 0 < r := hk.trans hkr
  have hrk : 0 < r - k := Nat.sub_pos_of_lt hkr
  rcases hfac r hr with ⟨-, hrUpper⟩
  rcases hfac k hk with ⟨hkLower, -⟩
  rcases hfac (r - k) hrk with ⟨hrkLower, -⟩
  have hcorek : 0 < stirlingCore k := by unfold stirlingCore; positivity
  have hcorerk : 0 < stirlingCore (r - k) := by unfold stirlingCore; positivity
  have hden : 0 < (a * stirlingCore k) * (a * stirlingCore (r - k)) := by
    positivity
  have hchoose : 0 ≤ (r.choose k : ℝ) := by positivity
  have hkfac : 0 ≤ (Nat.factorial k : ℝ) := by positivity
  have hmul :
      (r.choose k : ℝ) * (a * stirlingCore k) *
          (a * stirlingCore (r - k)) ≤ b * stirlingCore r := by
    calc
      (r.choose k : ℝ) * (a * stirlingCore k) *
          (a * stirlingCore (r - k)) ≤
          (r.choose k : ℝ) * (Nat.factorial k : ℝ) *
            (Nat.factorial (r - k) : ℝ) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hkLower hchoose
        · exact hrkLower
        · exact le_of_lt (mul_pos ha hcorerk)
        · exact mul_nonneg hchoose hkfac
      _ = (Nat.factorial r : ℝ) := by
        exact_mod_cast
          (Nat.choose_mul_factorial_mul_factorial (Nat.le_of_lt hkr))
      _ ≤ b * stirlingCore r := hrUpper
  have hdiv :
      (r.choose k : ℝ) ≤
        b * stirlingCore r /
          ((a * stirlingCore k) * (a * stirlingCore (r - k))) :=
    (le_div_iff₀ hden).2 (by simpa [mul_assoc] using hmul)
  calc
    (r.choose k : ℝ) ≤
        b * stirlingCore r /
          ((a * stirlingCore k) * (a * stirlingCore (r - k))) := hdiv
    _ = (b / (a * a)) * stirlingCore r /
          (stirlingCore k * stirlingCore (r - k)) := by
      apply (div_eq_div_iff hden.ne'
        (mul_pos hcorek hcorerk).ne').2
      field_simp [ha.ne']
end FirstPassageLinearTransport
