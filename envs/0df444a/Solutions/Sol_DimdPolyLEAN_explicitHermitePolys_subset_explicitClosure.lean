-- Prove2me | solution 1 for DimdPolyLEAN.explicitHermitePolys_subset_explicitClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:56:11.596155+00:00
-- url     : https://prove2.me/submissions/87092f96-f08e-42c9-bf0a-8aa02b7fbcde

module
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_PhaseStability
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.NormNum.Parity
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Auxiliary
section
@[expose] public section
open scoped BigOperators
noncomputable section
namespace DimdPolyLEAN
private theorem memLp_of_explicitHermitePoly
    {d : ℕ} (hd : 0 < d) {κ : Fin d -> ℕ} {Q : (Fin d -> ℂ) -> ℂ}
    (hQ : Q ∈ Set.range (explicitEvalPkappa κ)) :
    MeasureTheory.MemLp Q 2 (explicitGamma d) := by
  rcases hQ with ⟨F, rfl⟩
  exact memLp_two_evalPkappa hd κ F
end DimdPolyLEAN
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
noncomputable section
open DimdPolyLEAN
namespace DimdPolyLEAN
theorem _root_.solution
    {d : ℕ} (hd : 0 < d) (κ : Fin d -> ℕ) :
    Set.range (explicitEvalPkappa κ) ⊆ explicitClosureOfHermitePolys κ := by
  intro Q hQ
  rcases hQ with ⟨F, rfl⟩
  let hmem : MeasureTheory.MemLp (explicitEvalPkappa κ F) 2 (explicitGamma d) :=
    memLp_of_explicitHermitePoly hd ⟨F, rfl⟩
  refine ⟨hmem, subset_closure ?_⟩
  exact ⟨explicitEvalPkappa κ F, ⟨F, rfl⟩, hmem, rfl⟩
end DimdPolyLEAN
