-- Prove2me | solution 1 for DPDeconstructed.display_19
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:48:28.972209+00:00
-- url     : https://prove2.me/submissions/17b93801-0065-4f30-acd4-c97a82bbfeeb

import Mathlib
import Definitions.Def_DPDeconstructed_PlanFactorization

open DPDeconstructed DPDeconstructed.DynProg in
theorem solution {X A : Type*} [Nonempty X] (D : DPDeconstructed.DynProg X A) (σ : D.Policy)
    (h : D.SA → ℝ) (x : X) :
    ((D.Mσ σ h x : ℝ) : EReal) ≤ D.M h x := by
  unfold DPDeconstructed.DynProg.Mσ DPDeconstructed.DynProg.M
  exact le_iSup₂ (f := fun (a : A) (ha : a ∈ D.Γ x) => ((h ⟨(x, a), ha⟩ : ℝ) : EReal))
    (σ.1 x) (σ.2.1 x)
