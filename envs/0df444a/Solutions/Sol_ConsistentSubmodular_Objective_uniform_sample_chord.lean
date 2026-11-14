-- Prove2me | solution 1 for ConsistentSubmodular.Objective.uniform_sample_chord
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T16:27:46.451402+00:00
-- url     : https://prove2.me/submissions/49972bb9-ffa7-4c4c-a4e3-f17bf0a2e37e

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators
import Theorems.Thm_ConsistentSubmodular_sampleExpectation_insert

section

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

variable {ι : Type*} [DecidableEq ι]

theorem sampleAdd_insert (U : Finset ι) {e : ι} (he : e ∉ U)
    (p : ι → ℝ) (v : Finset ι → ℝ) (B : Finset ι) :
    sampleAdd (insert e U) p v B =
      (1 - p e) * sampleAdd U p v B + p e * sampleAdd U p v (insert e B) := by
  unfold sampleAdd
  rw [sampleExpectation_insert U he]
  simp only [Finset.union_insert, Finset.insert_union]

end ConsistentSubmodular

end

end

section

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem solution (A B : Finset (Fin n)) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    (1 - p) * f.value B + p * f.value (B ∪ A) ≤ sampleAdd A (fun _ => p) f.value B := by
  induction A using Finset.induction_on generalizing B with
  | empty => simp only [sampleAdd_empty, Finset.union_empty]; nlinarith
  | @insert e A he ih =>
    rw [sampleAdd_insert A he]
    have h0 := mul_le_mul_of_nonneg_left (ih B) (sub_nonneg.mpr hp')
    have h1 := mul_le_mul_of_nonneg_left (ih (insert e B)) hp
    have hs := f.submodular (B ∪ A) (insert e B)
    have hB : B ⊆ (B ∪ A) ∩ insert e B := by
      exact Finset.subset_inter Finset.subset_union_left (Finset.subset_insert e B)
    have hb := f.monotone _ _ hB
    have hu : (B ∪ A) ∪ insert e B = B ∪ insert e A := by
      ext i
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    have hu' : insert e B ∪ A = B ∪ insert e A := by
      ext i
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    rw [hu] at hs
    have hmargin : 0 ≤ f.value (B ∪ A) + f.value (insert e B) - f.value B - f.value (B ∪ insert e A) := by linarith
    have hweighted := mul_nonneg (mul_nonneg hp (sub_nonneg.mpr hp')) hmargin
    rw [hu'] at h1
    nlinarith only [h0, h1, hweighted]

end
