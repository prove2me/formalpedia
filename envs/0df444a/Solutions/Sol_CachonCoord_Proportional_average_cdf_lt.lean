-- Prove2me | solution 1 for CachonCoord.Proportional.average_cdf_lt
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T01:07:41.682271+00:00
-- url     : https://prove2.me/submissions/9c3db7a9-17e1-4c9d-af25-1aa5b329a995

import Mathlib
import Definitions.Def_CachonCoord_Proportional_Demand

open MeasureTheory ProbabilityTheory

lemma cachon247_int_le (M : CachonCoord.Proportional.Model) (a b : ℝ) (hab : a ≤ b) :
    ∫ x in a..b, M.F x ≤ (b - a) * M.F b := by
  have hmono : Monotone M.F := fun x y h => ProbabilityTheory.monotone_cdf M.law h
  have h1 : ∫ x in a..b, M.F x ≤ ∫ x in a..b, M.F b := by
    apply intervalIntegral.integral_mono_on hab (hmono.intervalIntegrable) intervalIntegrable_const
    intro x hx
    exact hmono hx.2
  simpa [intervalIntegral.integral_const, smul_eq_mul] using h1

open CachonCoord.Proportional in
theorem solution (M : Model) (q : ℝ) (hq : 0 < q) : M.avgF q < M.F q := by
  have hmono : Monotone M.F := fun x y h => ProbabilityTheory.monotone_cdf M.law h
  have hint : ∀ a b : ℝ, IntervalIntegrable M.F MeasureSpace.volume a b :=
    fun a b => hmono.intervalIntegrable
  have hsplit : ∫ x in (0:ℝ)..q, M.F x = (∫ x in (0:ℝ)..(q/2), M.F x) + ∫ x in (q/2)..q, M.F x :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 (q/2)) (hint (q/2) q)).symm
  have h1 := cachon247_int_le M 0 (q/2) (by linarith)
  have h2 := cachon247_int_le M (q/2) q (by linarith)
  have hlt : M.F (q/2) < M.F q :=
    M.strictMonoOn_cdf (Set.mem_Ici.2 (by linarith)) (Set.mem_Ici.2 (by linarith)) (by linarith)
  have hI : ∫ x in (0:ℝ)..q, M.F x < q * M.F q := by
    rw [hsplit]; nlinarith
  unfold Model.avgF
  rw [one_div, inv_mul_lt_iff₀ hq]
  exact hI
