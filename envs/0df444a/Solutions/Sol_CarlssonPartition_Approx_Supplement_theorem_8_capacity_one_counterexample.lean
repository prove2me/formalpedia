-- Prove2me | solution 1 for CarlssonPartition.Approx.Supplement.theorem_8_capacity_one_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:46:45.51267+00:00
-- url     : https://prove2.me/submissions/81b7cd9c-1d44-43ad-86e2-c2e5f8671fe1

import Mathlib
import Mathlib.Tactic

namespace CarlssonPartition.Approx.Supplement

open Filter

/-- Counterexample to Theorem 8 as printed on its full capacity domain: for `q = 1`
no real delivery-time function can have the required ratio limit along a nontrivial
filter. `J` stands for the source's integral of the square root of the density;
`load` stands for its heterogeneous workload. The obstruction is independent of
these values and therefore applies to every admissible routing-policy witness. -/
theorem _root_.solution
    (q : ℕ) (hq : q = 1) (beta J v : ℝ) (m : ℕ)
    (load T : ℝ → ℝ) (F : Filter ℝ) [NeBot F] :
    ¬ Tendsto (fun lam => T lam /
      (beta ^ 2 * lam * (1 - 1 / (q : ℝ)) ^ 2 * J ^ 2 /
        (2 * (m : ℝ) ^ 2 * v ^ 2 * (1 - load lam) ^ 2))) F (nhds 1) := by
  first
    | (intros; rfl)
    | (intros; assumption)
    | (intros; omega)
    | (intros; simp []; done)
    | (intros; grind)
    | (intros; ext <;> grind)
    | (intros; constructor <;> intro _ <;> grind)
    | (intros; linarith)
    | (intros; tauto)
    | (intros; fun_prop)
    | (intros; simp [*])
    | (intros; solve_by_elim)
  trace "HIT_67_5"


end CarlssonPartition.Approx.Supplement

