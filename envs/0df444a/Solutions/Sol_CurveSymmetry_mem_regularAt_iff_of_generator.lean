-- Prove2me | solution 1 for CurveSymmetry.mem_regularAt_iff_of_generator
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-07T12:57:14.557984+00:00
-- url     : https://prove2.me/submissions/32e829ac-a5f4-4d3f-b473-2c3029d09b85

-- Solution generated from lean/FunctionFieldGenus.lean (curve-symmetry-lean): inlined helpers in
-- their own scopes, then the node renamed to `solution` in its own context.
import Definitions.Def_CurveSymmetry_08_Differentials
import Definitions.Def_CurveSymmetry_09_Genus
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Valuation.ValuationSubring

namespace CurveSymmetry
set_option autoImplicit false
section Genus
variable {K : Type*} [Field K] [Algebra ℂ K]
lemma smul_D_mem_regularAt {O : ValuationSubring K} {a b : K} (ha : a ∈ O) (hb : b ∈ O) :
    a • KaehlerDifferential.D ℂ K b ∈ regularAt O :=
  Submodule.subset_span ⟨a, ha, b, hb, rfl⟩
end Genus
end CurveSymmetry

section
open CurveSymmetry
set_option autoImplicit false
variable {K : Type*} [Field K] [Algebra ℂ K]
theorem solution {O : ValuationSubring K} {u : K} (hu : u ∈ O)
    (hconst : ∀ z : ℂ, algebraMap ℂ K z ∈ O)
    (hgen : ∀ b ∈ O, ∃ g ∈ O,
      KaehlerDifferential.D ℂ K b = g • KaehlerDifferential.D ℂ K u)
    (ω : Ω[K⁄ℂ]) :
    ω ∈ regularAt O ↔ ∃ f ∈ O, ω = f • KaehlerDifferential.D ℂ K u := by
  constructor
  · intro hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨g, hg, hbg⟩ := hgen b hb
      exact ⟨a * g, mul_mem ha hg, by rw [hbg, smul_smul]⟩
    | zero => exact ⟨0, O.zero_mem, by rw [zero_smul]⟩
    | add x y _ _ hx hy =>
      obtain ⟨f, hf, rfl⟩ := hx
      obtain ⟨f', hf', rfl⟩ := hy
      exact ⟨f + f', add_mem hf hf', by rw [add_smul]⟩
    | smul z x _ hx =>
      obtain ⟨f, hf, rfl⟩ := hx
      refine ⟨algebraMap ℂ K z * f, mul_mem (hconst z) hf, ?_⟩
      rw [← smul_assoc, Algebra.smul_def]
  · rintro ⟨f, hf, rfl⟩
    exact smul_D_mem_regularAt hf hu
end

#print axioms solution
