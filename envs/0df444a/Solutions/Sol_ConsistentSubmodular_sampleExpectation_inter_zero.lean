-- Prove2me | solution 1 for ConsistentSubmodular.sampleExpectation_inter_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:27:47.069692+00:00
-- url     : https://prove2.me/submissions/d233445d-26ce-47c6-8dd5-6c70301bc1c1

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_insert

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem solution (U V : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∉ U, p i = 0) (v : Finset ι → ℝ) :
    sampleExpectation V p v = sampleExpectation (V ∩ U) p v := by
  induction V using Finset.induction_on generalizing v with
  | empty => simp
  | @insert e V he ih =>
    by_cases heU : e ∈ U
    · have hinter : insert e V ∩ U = insert e (V ∩ U) := by
        ext i
        by_cases hie : i = e <;> simp [hie, heU]
      rw [hinter, sampleExpectation_insert V he,
        sampleExpectation_insert (V ∩ U) (by simp [he]), ih, ih]
    · have hinter : insert e V ∩ U = V ∩ U := by
        ext i
        by_cases hie : i = e <;> simp [hie, heU]
      rw [hinter, sampleExpectation_insert V he, hp e heU]
      simp [ih]

end
