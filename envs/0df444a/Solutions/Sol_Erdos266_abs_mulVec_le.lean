-- Prove2me | solution 1 for Erdos266.abs_mulVec_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:41:13.536103+00:00
-- url     : https://prove2.me/submissions/fa684654-4612-4c46-9dea-c428d8afb74c

module
public import Definitions.Def_Erdos266_SlopeLemma
public import Definitions.Def_Erdos266_LatticeLemma

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Matrix
namespace Erdos266
theorem _root_.solution {d : ℕ} (B : Matrix (Fin d) (Fin d) ℤ) (z : Fin d → ℤ)
    {zb : ℝ} (hz : ∀ j, |(z j : ℝ)| ≤ zb) (i : Fin d) :
    |((B.mulVec z i : ℤ) : ℝ)|
      ≤ (∑ p : Fin d × Fin d, |((B p.1 p.2 : ℤ) : ℝ)|) * zb := by
  have hzb : 0 ≤ zb := (abs_nonneg _).trans (hz i)
  have hcast : ((B.mulVec z i : ℤ) : ℝ) = ∑ j, ((B i j : ℤ) : ℝ) * ((z j : ℤ) : ℝ) := by
    rw [Matrix.mulVec, dotProduct]
    push_cast
    rfl
  rw [hcast]
  calc |∑ j, ((B i j : ℤ) : ℝ) * ((z j : ℤ) : ℝ)|
      ≤ ∑ j, |((B i j : ℤ) : ℝ) * ((z j : ℤ) : ℝ)| := abs_sum_le_sum_abs _ _
  _ ≤ ∑ j, |((B i j : ℤ) : ℝ)| * zb := by
      refine sum_le_sum fun j _ => ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hz j) (abs_nonneg _)
  _ = (∑ j, |((B i j : ℤ) : ℝ)|) * zb := by rw [sum_mul]
  _ ≤ (∑ p : Fin d × Fin d, |((B p.1 p.2 : ℤ) : ℝ)|) * zb := by
      refine mul_le_mul_of_nonneg_right ?_ hzb
      rw [Fintype.sum_prod_type]
      exact single_le_sum (f := fun i' => ∑ j, |((B i' j : ℤ) : ℝ)|)
        (fun i' _ => by positivity) (mem_univ i)
end Erdos266
