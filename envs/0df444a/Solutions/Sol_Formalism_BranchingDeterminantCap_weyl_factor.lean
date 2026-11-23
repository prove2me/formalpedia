-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.weyl_factor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:12.877826+00:00
-- url     : https://prove2.me/submissions/3e1b9cf8-538a-4773-9c6f-13ac2319d85c

import Definitions.Def_Formalism_BranchSandwichDivisors_NormLog
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Interlace
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Numeric

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BranchingDeterminantCap
namespace Formalism.BranchingDeterminantCap
theorem _root_.solution {n : ℕ} {nu : Fin (n + 1) → ℤ} (h : Antitone nu) (p : Fin (n + 1) × Fin (n + 1))
    (hp : p.1 < p.2) :
    1 ≤ (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
          (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) ∧
    (((nu p.1 - nu p.2 : ℤ) : ℝ) + ((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) /
          (((p.2 : ℕ) : ℝ) - ((p.1 : ℕ) : ℝ)) ≤ ((nu 0 - nu (Fin.last n) : ℤ) : ℝ) + (n : ℝ) := by
  obtain ⟨a, b⟩ := p
  dsimp only at hp ⊢
  have hab : (a : ℕ) < (b : ℕ) := hp
  have hD : nu b ≤ nu a := h hp.le
  have h0 : nu a ≤ nu 0 := h (Fin.zero_le a)
  have hl : nu (Fin.last n) ≤ nu b := h (Fin.le_last b)
  have hn : (1:ℝ) ≤ n := by
    have := b.isLt
    exact_mod_cast (by omega : 1 ≤ n)
  have hd1 : ((a : ℕ) : ℝ) + 1 ≤ ((b : ℕ) : ℝ) := by exact_mod_cast hab
  have hDr : (0:ℝ) ≤ ((nu a - nu b : ℤ) : ℝ) := by
    exact_mod_cast (by omega : (0:ℤ) ≤ nu a - nu b)
  have hM : ((nu a - nu b : ℤ) : ℝ) ≤ ((nu 0 - nu (Fin.last n) : ℤ) : ℝ) := by
    exact_mod_cast (by omega : nu a - nu b ≤ nu 0 - nu (Fin.last n))
  have hdpos : (0:ℝ) < ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ) := by linarith
  constructor
  · rw [le_div_iff₀ hdpos]; linarith
  · rw [div_le_iff₀ hdpos]
    nlinarith [mul_le_mul_of_nonneg_left (by linarith : (1:ℝ) ≤ ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))
      (le_trans hDr hM), mul_le_mul_of_nonneg_right hn hdpos.le]
end Formalism.BranchingDeterminantCap
