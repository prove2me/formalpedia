-- Prove2me | solution 1 for Formalism.HermitianLatticesTheory.majDual_memI
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:43:14.7592+00:00
-- url     : https://prove2.me/submissions/e8ff4e8f-68fd-4c89-8881-8a593f8328b0

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMaj
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajLattice
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MajDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors
noncomputable section
open Formalism Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]
namespace Formalism.HermitianLatticesTheory
theorem _root_.solution (a : K) : a ∈ majDualI K ↔ a ∈ invDiff K := by
  have h10 : (1 : FractionalIdeal (RingOfIntegers K)⁰ K) ≠ 0 := by
    intro h0
    have h1 : (1 : K) ∈ (1 : FractionalIdeal (RingOfIntegers K)⁰ K) :=
      (FractionalIdeal.mem_one_iff _).2 ⟨1, map_one _⟩
    rw [h0, FractionalIdeal.mem_zero_iff] at h1
    exact one_ne_zero h1
  rw [majDualI, FractionalIdeal.mem_dual h10]
  constructor
  · intro h r
    obtain ⟨z, hz⟩ := RingHom.mem_range.1
      (h (algebraMap (RingOfIntegers K) K r) ((FractionalIdeal.mem_one_iff _).2 ⟨r, rfl⟩))
    rw [Algebra.traceForm_apply] at hz
    exact ⟨z, hz.symm.trans (eq_intCast (algebraMap ℤ ℚ) z)⟩
  · intro h x hx
    obtain ⟨r, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hx
    obtain ⟨z, hz⟩ := h r
    rw [RingHom.mem_range]
    refine ⟨z, ?_⟩
    rw [Algebra.traceForm_apply]
    exact (eq_intCast (algebraMap ℤ ℚ) z).trans hz.symm
end Formalism.HermitianLatticesTheory
