-- Prove2me | solution 1 for Conway99Formal.SrgCore.root_profile_arithmetic_core
-- status  : ACCEPTED   (prove)
-- author  : @harry
-- created : 2026-10-04T03:22:41.756737+00:00
-- url     : https://prove2.me/submissions/0cc0b2c0-d272-43fe-b4a4-68ecdfd15213

import Mathlib

namespace Conway99Formal.SrgCore
end Conway99Formal.SrgCore

set_option autoImplicit false

/-! Graph-owned parameter and adjacency identities for a hypothetical SRG(99,14,1,2).
Sources: `Conway99/Conway99/Core.lean` §§1–3, 8.1;
`Conway99/Conway99/Claims/C01srgcorealgebra.lean` §§0, 3, 6;
`Conway99/results/R005_star_complement_square_discriminant.md`.
-/

namespace Conway99Formal.SrgCore

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
























































end Conway99Formal.SrgCore

set_option autoImplicit false

/-! Graph-owned parameter and adjacency identities for a hypothetical SRG(99,14,1,2).
Sources: `Conway99/Conway99/Core.lean` §§1–3, 8.1;
`Conway99/Conway99/Claims/C01srgcorealgebra.lean` §§0, 3, 6;
`Conway99/results/R005_star_complement_square_discriminant.md`.
-/

open Conway99Formal.SrgCore

open SimpleGraph Matrix Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

open Conway99Formal.SrgCore in
theorem solution (m : ℕ) (hm : 1 ≤ m)
    (heven : Even m → 2 ^ m ∣ 4 * m - 4)
    (hodd : Odd m → 2 ^ (m - 1) ∣ 4 * m - 4) :
    m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 5 := by
  have hbound (k : ℕ) : 4 * (k + 6) - 4 < 2 ^ (k + 5) := by
    induction k with
    | zero => norm_num
    | succ k ih =>
        rw [show k + 1 + 5 = k + 5 + 1 by omega, pow_succ]
        omega
  by_cases hlarge : 6 ≤ m
  · have hs : m - 6 + 6 = m := by omega
    have ht : m - 6 + 5 = m - 1 := by omega
    have hb : 4 * m - 4 < 2 ^ (m - 1) := by
      simpa only [hs, ht] using hbound (m - 6)
    rcases m.even_or_odd with he | ho
    · have hfactor : 2 ^ (m - 1) ∣ 2 ^ m := by
        refine ⟨2, ?_⟩
        calc
          2 ^ m = 2 ^ (m - 1 + 1) := by congr 1 <;> omega
          _ = 2 ^ (m - 1) * 2 := pow_succ _ _
      have hd := dvd_trans hfactor (heven he)
      have hle := Nat.le_of_dvd (by omega : 0 < 4 * m - 4) hd
      omega
    · have hle := Nat.le_of_dvd (by omega : 0 < 4 * m - 4) (hodd ho)
      omega
  · have hsmall : m ≤ 5 := by omega
    interval_cases m <;> norm_num at *
