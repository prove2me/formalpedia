-- Prove2me | solution 1 for ConsistentSubmodular.sampleAdd_union_probabilities
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:27:45.883963+00:00
-- url     : https://prove2.me/submissions/f3cab1f5-0beb-41d0-abbf-b6c63ac58410

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_insert

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleExpectation_mul (U : Finset ι) (p : ι → ℝ) (c : ℝ) (v : Finset ι → ℝ) :
    sampleExpectation U p (fun S => c * v S) = c * sampleExpectation U p v := by
  simp only [sampleExpectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  ring

theorem sampleAdd_insert (U : Finset ι) {e : ι} (he : e ∉ U)
    (p : ι → ℝ) (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd (insert e U) p v B =
      (1 - p e) * sampleAdd U p v B + p e * sampleAdd U p v (insert e B) := by
  unfold sampleAdd
  rw [sampleExpectation_insert U he]
  simp only [Finset.union_insert, Finset.insert_union]

theorem sampleAdd_add (U : Finset ι) (p : ι → ℝ) (v w : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd U p (fun S => v S + w S) B = sampleAdd U p v B + sampleAdd U p w B :=
  sampleExpectation_add U p _ _

theorem sampleAdd_mul (U : Finset ι) (p : ι → ℝ) (c : ℝ) (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd U p (fun S => c * v S) B = c * sampleAdd U p v B :=
  sampleExpectation_mul U p c _

theorem sampleAdd_insert_base (U : Finset ι) (p : ι → ℝ) (v : Finset ι → ℝ)
    (B : Finset ι) (e : ι) :
    sampleAdd U p (fun S => v (insert e S)) B = sampleAdd U p v (insert e B) := by
  simp only [sampleAdd, Finset.insert_union]

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem solution (U : Finset ι) (p q : ι → ℝ)
    (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd U p (sampleAdd U q v) B =
      sampleAdd U (fun i => p i + q i - p i * q i) v B := by
  induction U using Finset.induction_on generalizing B with
  | empty => simp
  | @insert e U he ih =>
    rw [sampleAdd_insert U he, sampleAdd_insert U he]
    have hfun : sampleAdd (insert e U) q v =
        fun S => (1 - q e) * sampleAdd U q v S + q e * sampleAdd U q v (insert e S) := by
      funext S
      exact sampleAdd_insert U he q v S
    rw [hfun]
    simp only [sampleAdd_add, sampleAdd_mul, sampleAdd_insert_base, ih, Finset.insert_idem]
    ring

end
