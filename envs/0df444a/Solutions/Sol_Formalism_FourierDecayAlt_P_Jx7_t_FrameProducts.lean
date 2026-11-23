-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Jx7.t_FrameProducts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:18:01.742427+00:00
-- url     : https://prove2.me/submissions/87801c61-75af-4512-a9ff-364abb9d74dc

import Definitions.Def_Formalism_HermitianCurvature_StatementJ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JointInstanceTheoremA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField Formalism.FourierDecayAlt Formalism.FourierDecayAlt.J
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Jx7
namespace Formalism.FourierDecayAlt.P.Jx7
theorem _root_.solution : FrameProducts := by
  intro r i s C rd g N I A TT hi hs hrd hg
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have e1 : 2 * r + 2 - 1 = 2 * r + 1 := by omega
  have e2 : 2 * (j + 1 - 1) + (t + 1) - 1 = 2 * j + t := by omega
  have e3 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have e4 : 2 * (j + 1) - 2 = 2 * j := by omega
  have e5 : 2 * (j + 1 - 1) = 2 * j := by omega
  constructor
  · unfold Sz.lamThreshold Sz.lamHat S6.nuBlock
    rw [e1, e2]
    have hz : rd ^ ((2 * (r : ℤ) + 3 - 2 * ((j + 1 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ)) + 1) =
        rd ^ (2 * r + 1) / rd ^ (2 * j + t) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd.ne']
      congr 1; push_cast; ring
    rw [hz]
    have hb : C * (2 * Real.pi / g) * N / I = C * (2 * Real.pi / rd) * N / (g * I) * rd := by
      by_cases hI : I = 0
      · simp [hI]
      · field_simp
    rw [hb, mul_pow]
    generalize (C * (2 * Real.pi / rd) * N / (g * I)) ^ (2 * j + t) = Z
    simp only [div_pow]
    field_simp
    ring
  · unfold Sz.lamPrimeSq Sz.lamPrimeHat S6.nuBlock
    rw [e1, e3, e4, e5]
    have hz : rd ^ (2 * (r : ℤ) + 3 - 2 * ((j + 1 : ℕ) : ℤ) - ((r : ℤ) + 2 - ((j + 1 : ℕ) : ℤ))) =
        rd ^ r / rd ^ j := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ hrd.ne']
      congr 1; push_cast; ring
    rw [hz]
    have hbpos : 0 ≤ g * (rd ^ r / rd ^ j) := by positivity
    rw [← Real.sqrt_sq hbpos, ← Real.sqrt_mul' _ (sq_nonneg _)]
    congr 1
    have hb : C * (2 * Real.pi / rd) * N / I = C * N / I * (2 * Real.pi / rd) := by ring
    rw [hb, mul_pow (C * N / I)]
    generalize (C * N / I) ^ (2 * j) = Z
    generalize (√TT)⁻¹ = S
    simp only [div_pow, mul_pow]
    field_simp
    ring
end Formalism.FourierDecayAlt.P.Jx7
