-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.capacity_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:22:54.87761+00:00
-- url     : https://prove2.me/submissions/a959deed-7240-4c0b-9985-c4ea8e184a9d

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric
import Theorems.Thm_Formalism_BranchingDeterminantCap_interlace_antitone
import Theorems.Thm_Formalism_BranchingDeterminantCap_capacity_constant_bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
namespace Formalism.BranchingDeterminantCap
private theorem d1_nonneg_of_interlace {n : ℕ} {lam : Fin (n + 1) → ℤ} {sg : Fin n → ℤ}
    (h : Interlace lam sg) : 0 ≤ d1 lam sg := by
  have hd0 : 0 ≤ d0 lam sg := by
    unfold d0; exact Finset.sum_nonneg (fun i _ => sub_nonneg.2 (h i).2)
  unfold d1
  exact Finset.sum_nonneg (fun i _ => le_min (by linarith [(h i).1, (h i).2]) hd0)
end Formalism.BranchingDeterminantCap
end

set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution : CapLog := by
  unfold CapLog
  intro n lam sg a h ha
  obtain ⟨hne, hle⟩ := capacity_constant_bound n lam sg h
  have hd1 := d1_nonneg_of_interlace h
  have hM : (0:ℝ) ≤ ((lam 0 - lam (Fin.last n) : ℤ) : ℝ) := by
    have := interlace_antitone h (Fin.zero_le (Fin.last n))
    exact_mod_cast (by omega : (0:ℤ) ≤ lam 0 - lam (Fin.last n))
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hcpos : (0:ℝ) < |(cCap lam sg : ℝ)| := by
    rw [abs_pos]; exact_mod_cast hne
  have h1 : |(cCap lam sg : ℝ)| ≤
      (((lam 0 - lam (Fin.last n) + (n:ℤ) - 1) : ℤ) : ℝ) ^ (n * (d1 lam sg).toNat) := by
    exact_mod_cast hle
  have e : (((lam 0 - lam (Fin.last n) + (n:ℤ) - 1) : ℤ) : ℝ) =
      ((lam 0 - lam (Fin.last n) : ℤ) : ℝ) + n - 1 := by push_cast; ring
  have hB : |(((lam 0 - lam (Fin.last n) + (n:ℤ) - 1) : ℤ) : ℝ)| ≤ 2 * a := by
    rw [e, abs_le]; constructor <;> linarith
  have h2 : |(cCap lam sg : ℝ)| ≤ (2 * a) ^ (n * (d1 lam sg).toNat) := by
    calc _ ≤ _ := h1
      _ ≤ |(((lam 0 - lam (Fin.last n) + (n:ℤ) - 1) : ℤ) : ℝ)| ^ (n * (d1 lam sg).toNat) := by
          rw [← abs_pow]; exact le_abs_self _
      _ ≤ (2 * a) ^ (n * (d1 lam sg).toNat) := by gcongr
  have ht : (((d1 lam sg).toNat : ℕ) : ℝ) = ((d1 lam sg : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hd1
  calc Real.log |(cCap lam sg : ℝ)| ≤ Real.log ((2 * a) ^ (n * (d1 lam sg).toNat)) :=
        Real.log_le_log hcpos h2
    _ = ((n * (d1 lam sg).toNat : ℕ) : ℝ) * Real.log (2 * a) := Real.log_pow _ _
    _ = ((n:ℝ) + 1 - 1) * ((d1 lam sg : ℤ) : ℝ) * Real.log (2 * a) := by
        rw [Nat.cast_mul, ht]; ring
end Formalism.BranchingDeterminantCap
