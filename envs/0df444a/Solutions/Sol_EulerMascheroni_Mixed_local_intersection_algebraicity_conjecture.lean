-- Prove2me | solution 1 for EulerMascheroni.Mixed.local_intersection_algebraicity_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:25:42.806803+00:00
-- url     : https://prove2.me/submissions/2a1e375b-c4c0-4c4e-9848-345cb7c849c4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_Mixed_mixed_value_coefficient_sum
import Theorems.Thm_EulerMascheroni_Mixed_decaying_algebraic_mixed_quotient_conjecture
import Theorems.Thm_EulerMascheroni_Mixed_algebraic_quotient_boundary
open EulerMascheroni.Mixed

theorem solution (a b c : ℝ) (ha : IsAlgebraic ℚ a) (hb : IsAlgebraic ℚ b)
    (hc : IsAlgebraic ℚ c)
    (h : (EulerMascheroni.gompertzConstant : ℂ) =
      (a : ℂ) + (b : ℂ) * Complex.exp 1 +
      (c : ℂ) * EulerMascheroni.Mixed.expEin 1) :
    IsAlgebraic ℚ EulerMascheroni.gompertzConstant := by
  obtain ⟨u, hu0, hrec, hlim, halg⟩ :=
    decaying_algebraic_mixed_quotient_conjecture a b c ha hb hc h
  have hsum := mixed_value_coefficient_sum a b c
  have hf0 : IsAlgebraic ℚ (valueCoefficient a b c 0) := by
    rw [hsum.2]
    exact (ha.algebraMap : IsAlgebraic ℚ (algebraMap ℝ ℂ a)).add hb.algebraMap
  have hd := algebraic_quotient_boundary (valueCoefficient a b c) u
    (EulerMascheroni.gompertzConstant:ℂ) (EulerMascheroni.gompertzConstant:ℂ)
    hu0 hrec (by rw [h]; exact hsum.1) hlim hf0 (halg 0)
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℚ ℝ ℂ)
    (algebraMap ℝ ℂ).injective).mp hd

#print axioms solution
