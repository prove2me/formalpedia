-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S6x5.exists_nat_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:42:01.642901+00:00
-- url     : https://prove2.me/submissions/e8225a99-72d4-4055-877a-a83c1f37890b

import Definitions.Def_Formalism_HermitianCurvature_PrimeToDifferent
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwistedIsRealOrderLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S6x5
open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module MeasureTheory
open scoped nonZeroDivisors
namespace Formalism.FourierDecayAlt.P.S6x5
theorem _root_.solution (E : Type) [Field E] [NumberField E] (B : FI E) (hB : B ≠ 0) (t : E) :
    ∃ n : ℕ, 0 < n ∧ (n : E) * t ∈ B := by
  obtain ⟨b, hb, hb0⟩ : ∃ b ∈ B, b ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hB ((FractionalIdeal.eq_zero_iff).2 hcon)
  have halg : IsAlgebraic ℤ (t / b) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (t / b))
  obtain ⟨y, hy0, hy⟩ := halg.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy0, ?_⟩
  have h1 : (y : E) * t ∈ B := by
    obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, algebraMap (𝓞 E) E z = y • (t / b) :=
      ⟨⟨y • (t / b), hy⟩, rfl⟩
    have := (B : Submodule (𝓞 E) E).smul_mem z hb
    rw [Algebra.smul_def, hz, zsmul_eq_mul] at this
    have h2 : (y : E) * (t / b) * b = (y : E) * t := by field_simp
    rw [h2] at this
    exact this
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact h1
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact (B : Submodule (𝓞 E) E).neg_mem h1
end Formalism.FourierDecayAlt.P.S6x5
