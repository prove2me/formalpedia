-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.B2x3.real_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:11:11.090774+00:00
-- url     : https://prove2.me/submissions/666e0ea4-cafe-4ca6-9053-c361f382b52f

import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B2x3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.B2x3
theorem _root_.solution (u z : Fin (k + 1) → ℂ) (τ : ℝ)
    (h1 : (∑ i : Fin k, ‖u i.castSucc‖ ^ 2) - ‖u (Fin.last k)‖ ^ 2 ≤ 1)
    (h2 : ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k)‖ ≤ τ)
    (hT : (∑ i : Fin k, ‖z i.castSucc‖ ^ 2) < ‖z (Fin.last k)‖ ^ 2) (i : Fin (k + 1)) :
    ‖u i‖ ≤ 1 + (τ + √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) / (‖z (Fin.last k)‖ - √(∑ i : Fin k, ‖z i.castSucc‖ ^ 2)) := by
  set X := ∑ i : Fin k, ‖u i.castSucc‖ ^ 2 with hX
  set Y := ∑ i : Fin k, ‖z i.castSucc‖ ^ 2 with hY
  set A := ‖u (Fin.last k)‖ with hA
  set B := ‖z (Fin.last k)‖ with hB
  have hA0 : 0 ≤ A := norm_nonneg _
  have hB0 : 0 ≤ B := norm_nonneg _
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => by positivity
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i _ => by positivity
  have hBpos : 0 < B := by
    rcases hB0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hT; norm_num at hT; linarith
  have hy : √Y < B := (Real.sqrt_lt' hBpos).mpr hT
  have hy0 : 0 ≤ √Y := Real.sqrt_nonneg _
  have hx : √X ≤ 1 + A := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hS : ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ ≤ √Y * √X := by
    calc ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ ≤ ∑ i : Fin k, ‖star (z i.castSucc) * u i.castSucc‖ :=
          norm_sum_le _ _
      _ = ∑ i : Fin k, ‖z i.castSucc‖ * ‖u i.castSucc‖ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [norm_mul, norm_star]
      _ ≤ √Y * √X := Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hBA : B * A ≤ τ + √Y * √X := by
    have e : B * A = ‖star (z (Fin.last k)) * u (Fin.last k)‖ := by rw [norm_mul, norm_star]
    rw [e]
    calc ‖star (z (Fin.last k)) * u (Fin.last k)‖
        = ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) -
            ((∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k))‖ := by
          congr 1; ring
      _ ≤ ‖∑ i : Fin k, star (z i.castSucc) * u i.castSucc‖ +
            ‖(∑ i : Fin k, star (z i.castSucc) * u i.castSucc) - star (z (Fin.last k)) * u (Fin.last k)‖ :=
          norm_sub_le _ _
      _ ≤ τ + √Y * √X := by linarith
  have hd : 0 < B - √Y := by linarith
  have hAle : A ≤ (τ + √Y) / (B - √Y) := by
    rw [le_div_iff₀ hd]
    have : √Y * √X ≤ √Y * (1 + A) := mul_le_mul_of_nonneg_left hx hy0
    nlinarith
  refine Fin.lastCases ?_ (fun j => ?_) i
  · linarith
  · have hj : ‖u j.castSucc‖ ^ 2 ≤ X :=
      Finset.single_le_sum (f := fun i : Fin k => ‖u i.castSucc‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)
    have : ‖u j.castSucc‖ ≤ √X := Real.le_sqrt_of_sq_le hj
    linarith
end Formalism.FourierDecayAlt.P.B2x3
