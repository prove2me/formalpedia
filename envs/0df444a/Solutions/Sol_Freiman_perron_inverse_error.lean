-- Prove2me | solution 1 for Freiman.perron_inverse_error
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T11:27:04.011333+00:00
-- url     : https://prove2.me/submissions/548a6efc-ac76-4204-834a-50d9694cefed

import Definitions.Def_Freiman_perronArithmetic
import Theorems.Thm_Freiman_cfValue_prefix
import Theorems.Thm_Freiman_prefixEval_mobius
import Theorems.Thm_Freiman_continuant_determinant
import Theorems.Thm_Freiman_continuant_denominator_pos
import Theorems.Thm_Freiman_continuant_inverse_error_algebra
import Theorems.Thm_Freiman_continuant_reverse
import Theorems.Thm_Freiman_cf_convergence

open Freiman

theorem solution (b : ℕ → ℕ+) (n : ℕ) :
    1 / ((continuantQ b n : ℝ) *
      |(continuantQ b n : ℝ) * cfValue b - (continuantP b n : ℝ)|) = perronValue b n := by
  let τ := cfValue (fun k => b (n+k))
  have ht : 0 < τ := (cf_convergence (fun k => b (n+k))).2.2.1
  have hp := cfValue_prefix b n
  rw [prefixEval_mobius _ τ (le_of_lt ht)] at hp
  have hd : |(continuantPrevP b n:ℝ)*(continuantQ b n:ℝ)-
      (continuantP b n:ℝ)*(continuantPrevQ b n:ℝ)| = 1 := by
    have hz := congrArg abs (continuant_determinant ((List.range n).map b))
    have hz' : |(wordContinuantPrevP ((List.range n).map b):ℤ)*wordContinuantQ ((List.range n).map b)-
        (wordContinuantP ((List.range n).map b):ℤ)*wordContinuantPrevQ ((List.range n).map b)|=1 := by
      simpa using hz
    exact_mod_cast hz'
  have hi := continuant_inverse_error_algebra (continuantP b n) (continuantPrevP b n)
    (continuantQ b n) (continuantPrevQ b n) τ (cfValue b)
    (by exact_mod_cast continuant_denominator_pos ((List.range n).map b))
    (by positivity) ht hp hd
  rw [hi]
  have hs := (cf_convergence (fun k => b (n+k))).2.2.2.2
  have hτ : 1/τ = ((b n:ℕ):ℝ)+cfValue (fun k => b (n+1+k)) := by
    change 1 / cfValue (fun k => b (n+k)) = _
    rw [hs]
    simp only [Nat.add_zero, one_div_one_div]
    congr 2
    funext k
    congr 1
    omega
  rw [hτ]
  unfold perronValue
  rw [continuant_reverse]
  ring
