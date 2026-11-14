-- Prove2me | solution 1 for ConsistentSubmodular.unionProbability_mem_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:26:19.090668+00:00
-- url     : https://prove2.me/submissions/f4e05e48-2c42-4340-95a6-4750b639f6f5

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}

omit [DecidableEq ι] in
theorem solution (cores : ι → Finset (Fin n)) (U : Finset ι)
    (p : ι → ℝ) (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (e : Fin n) :
    0 ≤ unionProbability cores U p e ∧ unionProbability cores U p e ≤ 1 := by
  have hnonneg : 0 ≤ ∏ i ∈ U, if e ∈ cores i then 1 - p i else 1 := by
    apply Finset.prod_nonneg
    intro i hi
    split_ifs
    · exact sub_nonneg.mpr (hp i hi).2
    · norm_num
  have hle : (∏ i ∈ U, if e ∈ cores i then 1 - p i else 1) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i hi
      split_ifs
      · exact sub_nonneg.mpr (hp i hi).2
      · norm_num
    · intro i hi
      split_ifs
      · linarith [(hp i hi).1]
      · rfl
  dsimp [unionProbability]
  constructor <;> linarith

end
