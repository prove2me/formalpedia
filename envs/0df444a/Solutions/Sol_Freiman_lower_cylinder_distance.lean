-- Prove2me | solution 1 for Freiman.lower_cylinder_distance
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T12:57:00.957119+00:00
-- url     : https://prove2.me/submissions/4ec0cc36-6f2e-4ba4-84ab-33416fbcda19

import Theorems.Thm_Freiman_cfValue_cylinder_bound
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem solution (p : LowerPair) (a b : ℤ → ℕ+) (ha : lowerCylinder p a) (hb : lowerCylinder p b) :
    |localValue a 0 - localValue b 0| ≤ lowerCylinderError p := by
  have hl := cfValue_cylinder_bound (fun n => a (-(n : ℤ)-1))
    (fun n => b (-(n : ℤ)-1)) p.1.length (fun n hn => (ha.2.1 n hn).trans (hb.2.1 n hn).symm)
  have hr := cfValue_cylinder_bound (fun n => a ((n : ℤ)+1))
    (fun n => b ((n : ℤ)+1)) p.2.length (fun n hn => (ha.2.2 n hn).trans (hb.2.2 n hn).symm)
  have hv : localValue a 0 - localValue b 0 =
      (cfValue (fun n => a (-(n : ℤ)-1)) - cfValue (fun n => b (-(n : ℤ)-1))) +
      (cfValue (fun n => a ((n : ℤ)+1)) - cfValue (fun n => b ((n : ℤ)+1))) := by
    simp only [localValue, ha.1, hb.1, zero_sub, zero_add]
    ring
  rw [hv]
  exact le_trans (abs_add_le _ _) (add_le_add hl hr)
