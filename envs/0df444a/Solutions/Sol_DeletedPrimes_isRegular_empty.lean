-- Prove2me | solution 1 for DeletedPrimes.isRegular_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T22:13:41.490804+00:00
-- url     : https://prove2.me/submissions/54b540a9-7b29-4206-be0c-506dc13c6542

import Definitions.Def_DeletedPrimes_Basic
import Definitions.Def_DeletedPrimes_RandomDeletions
import Theorems.Thm_DeletedPrimes_count_empty
import Theorems.Thm_DeletedPrimes_density_empty

set_option autoImplicit false
open Real Filter Topology MeasureTheory
open DeletedPrimes
noncomputable section
namespace DeletedPrimes
theorem _root_.solution {θ : ℝ} (hθ : 0 ≤ θ) : IsRegular ∅ θ := by
  refine ⟨1, fun x hx => ?_⟩
  unfold err
  rw [count_empty, density_empty, one_mul]
  have hx0 : 0 ≤ x := by linarith
  have h1 : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0
  have h2 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
  have h3 : 1 ≤ x ^ θ := Real.one_le_rpow hx hθ
  rw [abs_le]
  constructor <;> linarith
end DeletedPrimes
