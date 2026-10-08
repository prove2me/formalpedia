-- Prove2me | solution 1 for BookProof.ChapterUnboundedPosition.mulDomain_dense
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T07:34:26.333992+00:00
-- url     : https://prove2.me/submissions/9a94fe78-ab08-463f-b504-f661c70394eb

import Mathlib
import Definitions.Def_ChapterUnboundedPosition
import Definitions.Def_ChapterContinuityUnitaryInfinite

set_option autoImplicit false

open BookProof.ChapterContinuityUnitaryInfinite BookProof.ChapterUnboundedPosition in
theorem c0a9b2aa_single_mem (f : ℤ → ℝ) (i : ℤ) (c : ℂ) :
    (lp.single (E := fun _ : ℤ => ℂ) 2 i c : L2Z) ∈ mulDomain f := by
  have heq : (fun k => (f k : ℂ) * ((lp.single (E := fun _ : ℤ => ℂ) 2 i c : L2Z) : ℤ → ℂ) k)
      = ((lp.single (E := fun _ : ℤ => ℂ) 2 i ((f i : ℂ) * c) : L2Z) : ℤ → ℂ) := by
    funext k
    rw [lp.single_apply, lp.single_apply]
    by_cases h : k = i
    · subst h; simp
    · simp [h]
  change Memℓp (fun k => (f k : ℂ) * ((lp.single (E := fun _ : ℤ => ℂ) 2 i c : L2Z) : ℤ → ℂ) k) 2
  rw [heq]
  exact (lp.single (E := fun _ : ℤ => ℂ) 2 i ((f i : ℂ) * c)).2

open BookProof.ChapterContinuityUnitaryInfinite BookProof.ChapterUnboundedPosition in
theorem solution (f : ℤ → ℝ) : Dense ((mulDomain f : Submodule ℂ L2Z) : Set L2Z) := by
  intro psi
  have hs : HasSum (fun i : ℤ => (lp.single (E := fun _ : ℤ => ℂ) 2 i ((psi : ℤ → ℂ) i) : L2Z)) psi :=
    lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := 2) (by simp) psi
  apply mem_closure_of_tendsto hs
  refine Filter.Eventually.of_forall (fun s => ?_)
  exact Submodule.sum_mem _ (fun i _ => c0a9b2aa_single_mem f i _)
