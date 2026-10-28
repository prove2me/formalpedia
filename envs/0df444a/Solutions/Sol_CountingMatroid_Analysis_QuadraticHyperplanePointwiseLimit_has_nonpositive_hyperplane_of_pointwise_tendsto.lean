-- Prove2me | solution 1 for CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit.has_nonpositive_hyperplane_of_pointwise_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-24T15:28:08.668978+00:00
-- url     : https://prove2.me/submissions/bc4ec8f7-572d-4387-b85c-91408d13e041

import Definitions.Def_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Theorems.Thm_CountingMatroid_Analysis_QuadraticNonpositiveHyperplane_HasNonpositiveHyperplane_nonpos_of_associated_eq_zero

namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
set_option autoImplicit false

/-!
Pointwise limits of real quadratic forms preserve a nonpositive hyperplane,
without a dimension hypothesis. A positive vector of the limit fixes its
associated kernel; polynomially corrected vectors in the approximants give
the limiting inequality on that kernel.
-/

namespace CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
end CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit

open Filter
open QuadraticNonpositiveHyperplane

/-- INTERNAL: The associated kernel of a positive vector witnesses closure of
nonpositive hyperplanes under pointwise convergence, in arbitrary dimension.
TEXLINE: main.tex:340-347 -/
theorem solution {V : Type}
    [AddCommGroup V] [Module ℝ V] [Invertible (2 : ℝ)]
    (Qn : ℕ → QuadraticForm ℝ V) (Q : QuadraticForm ℝ V)
    (hn : ∀ n, HasNonpositiveHyperplane (Qn n))
    (hconv : ∀ v, Tendsto (fun n => Qn n v) atTop (nhds (Q v))) :
    HasNonpositiveHyperplane Q := by
  classical
  by_cases hpos : ∃ e, 0 < Q e
  · obtain ⟨e, he⟩ := hpos
    refine ⟨Q.associated e, ?_⟩
    intro v hv
    have hpolar (P : QuadraticForm ℝ V) (x y : V) :
        P.associated x y = (P (x + y) - P x - P y) / 2 := by
      have h := congrArg (fun B => B x y) (QuadraticMap.two_nsmul_associated ℝ P)
      have htwo : 2 * P.associated x y = P (x + y) - P x - P y := by
        simpa only [LinearMap.smul_apply, smul_eq_mul,
          QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
          nsmul_eq_mul, Nat.cast_ofNat] using h
      linarith
    have hB : Tendsto (fun n => (Qn n).associated e v) atTop (nhds 0) := by
      simpa only [← hpolar, hv] using
        (((hconv (e + v)).sub (hconv e)).sub (hconv v)).div_const 2
    have hineq : ∀ᶠ n in atTop,
        (Qn n e) ^ 2 * Qn n v - Qn n e * ((Qn n).associated e v) ^ 2 ≤ 0 := by
      filter_upwards [(hconv e).eventually_const_lt he] with n hen
      let z := (Qn n e) • v - ((Qn n).associated e v) • e
      have hz : (Qn n).associated e z = 0 := by
        simp [z, QuadraticMap.associated_eq_self_apply, smul_eq_mul, mul_comm]
      have hnonpos := (hn n).nonpos_of_associated_eq_zero e z hen hz
      have hexp : Qn n z =
          (Qn n e) ^ 2 * Qn n v - Qn n e * ((Qn n).associated e v) ^ 2 := by
        calc
          Qn n z = (Qn n).associated z z :=
            (QuadraticMap.associated_eq_self_apply ℝ (Qn n) z).symm
          _ = _ := by
            dsimp only [z]
            simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
              smul_eq_mul, QuadraticMap.associated_eq_self_apply]
            rw [QuadraticMap.associated_isSymm ℝ (Qn n) v e]
            ring
      rwa [hexp] at hnonpos
    have hlimit : (Q e) ^ 2 * Q v ≤ 0 := by
      have h := le_of_tendsto
        (((hconv e).pow 2 |>.mul (hconv v)).sub ((hconv e).mul (hB.pow 2))) hineq
      simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, sub_zero] using h
    exact nonpos_of_mul_nonpos_right hlimit (sq_pos_of_pos he)
  · refine ⟨0, fun v _ => ?_⟩
    exact le_of_not_gt (fun hv => hpos ⟨v, hv⟩)
