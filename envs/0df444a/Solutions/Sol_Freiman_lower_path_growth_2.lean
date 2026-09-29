-- Prove2me | solution 2 for Freiman.lower_path_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T09:57:49.546677+00:00
-- url     : https://prove2.me/submissions/2df6b4a0-9b0e-429d-a40e-773357ff0852

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Theorems.Thm_Freiman_lower_width_bounds
import Theorems.Thm_Freiman_lower_width_append
import Theorems.Thm_Freiman_lower_path_prefixes
import Theorems.Thm_Freiman_lower_path_fairness
import Theorems.Thm_Freiman_lower_two_sided_growth

open Freiman

-- `lower_two_sided_growth` already proves the two `Tendsto` statements for an abstract
-- sequence `h`, from five inputs. Instantiated at `lowerPhysicalPath h`, the width inputs
-- are the Proved `lower_width_bounds` and `lower_width_append`, the extension and
-- prefix-size inputs are the second and third conjuncts of `lower_path_prefixes`, and the
-- fairness input is `lower_path_fairness`.
theorem solution (t : ℝ) (h : ℕ → LowerPair) (hh : lowerPath t h) :
    Filter.Tendsto (fun n => (lowerPhysicalPath h n).1.length) Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun n => (lowerPhysicalPath h n).2.length) Filter.atTop Filter.atTop := by
  obtain ⟨-, hext, hsize⟩ := lower_path_prefixes t h hh
  exact lower_two_sided_growth
    (fun w => lower_width_bounds w)
    (fun w u hu => lower_width_append w u hu)
    (lowerPhysicalPath h) hext hsize (lower_path_fairness t h hh)
