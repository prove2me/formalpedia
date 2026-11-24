-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.complex_multiplication_root
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:42.801424+00:00
-- url     : https://prove2.me/submissions/dcc57d8d-5476-4705-a6c9-5377580c34f2

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ComplexMultiplicationRoot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.LocalIntegralStructure.CMRoot := by
  intro E _ _ q x hc hq hx h
  have hm : ∀ w : InfinitePlace E, w.mult = 2 := fun w =>
    NumberField.InfinitePlace.mult_isComplex ⟨w, hc w⟩
  have hn : Module.finrank ℚ E = 2 * Fintype.card (InfinitePlace E) := by
    rw [← NumberField.InfinitePlace.sum_mult_eq]
    simp only [hm, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  simp only [hm] at h
  rw [hn] at h
  have hP : ∏ w : InfinitePlace E, (x w ^ 2) ^ 2 = (∏ w : InfinitePlace E, x w) ^ 4 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl (fun w _ => by ring)
  have hA : (q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2)) ^ 4 =
      q ^ (2 * Fintype.card (InfinitePlace E)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, ← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have key : (q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2)) ^ 4 ≤ (∏ w : InfinitePlace E, x w) ^ 4 := by
    rw [hA, ← hP]; exact h
  have h0 : 0 ≤ ∏ w : InfinitePlace E, x w := Finset.prod_nonneg fun w _ => hx w
  have hq0 : 0 ≤ q ^ ((Fintype.card (InfinitePlace E) : ℝ) / 2) := (Real.rpow_pos_of_pos hq _).le
  first
  | exact le_of_pow_le_pow_left₀ (by norm_num) h0 key
  | exact (pow_le_pow_iff_left₀ hq0 h0 (by norm_num)).mp key
  | exact le_of_pow_le_pow_left (by norm_num) h0 key
  | exact (pow_le_pow_iff_left hq0 h0 (by norm_num)).mp key
end Formalism.HermitianLatticeCounting.P
