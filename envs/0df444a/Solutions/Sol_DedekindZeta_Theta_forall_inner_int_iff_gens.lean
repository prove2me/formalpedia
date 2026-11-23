-- Prove2me | solution 1 for DedekindZeta.Theta.forall_inner_int_iff_gens
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:10:18.634607+00:00
-- url     : https://prove2.me/submissions/4b714fd6-f4a9-4fac-be2f-28b567a872d5

import Mathlib
import Definitions.Def_DedekindZeta_PoissonSummation
import Definitions.Def_DedekindZeta_Theta

set_option autoImplicit true
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace
open scoped Real nonZeroDivisors Classical FourierTransform RealInnerProductSpace ContDiff
open DedekindZeta DedekindZeta.Theta
variable (K : Type*) [Field K] [NumberField K]
noncomputable section
namespace DedekindZeta.Theta
theorem _root_.solution (I : FractionalIdeal (𝓞 K)⁰ K)
    (y : minkowskiSpace K) :
    (∀ x ∈ idealLattice K I, ∃ k : ℤ, (inner ℝ y x : ℝ) = k) ↔
      ∀ a ∈ (I : Submodule (𝓞 K) K), ∃ k : ℤ,
        (inner ℝ y (eEmb K a) : ℝ) = k := by
  classical
  -- The set of points pairing integrally with `y` is a `ℤ`-submodule.
  set N : Submodule ℤ (minkowskiSpace K) :=
    { carrier := {x | ∃ k : ℤ, (inner ℝ y x : ℝ) = k}
      zero_mem' := ⟨0, by simp⟩
      add_mem' := by
        rintro a b ⟨ka, ha⟩ ⟨kb, hb⟩
        exact ⟨ka + kb, by rw [inner_add_right, ha, hb]; push_cast; ring⟩
      smul_mem' := by
        rintro c a ⟨k, hk⟩
        refine ⟨c * k, ?_⟩
        have hcs : (c • a : minkowskiSpace K) = (c : ℝ) • a :=
          (Int.cast_smul_eq_zsmul ℝ c a).symm
        rw [hcs, real_inner_smul_right, hk]; push_cast; ring } with hN
  constructor
  · intro h a ha
    exact h (eEmb K a) (Submodule.subset_span ⟨a, ha, rfl⟩)
  · intro h x hx
    have hle : idealLattice K I ≤ N := by
      rw [idealLattice, Submodule.span_le]
      rintro _ ⟨a, ha, rfl⟩
      exact h a ha
    exact hle hx
end DedekindZeta.Theta
