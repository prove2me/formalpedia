-- Prove2me | solution 1 for Formalism.HermitianLattices.IntegralLatticeDensity.kronecker_symbol_comparison
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:06:08.910621+00:00
-- url     : https://prove2.me/submissions/56a1ee7a-7a2c-41fc-8a06-b2206ed00a15

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvariantSeriesBidegreeOneOne
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_TaylorLogMetric
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_BimultiplicativeDivisibleTorsion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.IntegralLatticeDensity
open Finset Formalism.LogVandermondeBounds.TaylorLogMetric
namespace Formalism.HermitianLattices.IntegralLatticeDensity
theorem _root_.solution : KroneckerCompare := by
  unfold KroneckerCompare
  intro h w d γ L1 L1' S hh hw hd hL1 heq
  have hr : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hl1 : Real.log (2 / Real.sqrt d) = Real.log 2 - Real.log (Real.sqrt d) :=
    Real.log_div (by norm_num) hr.ne'
  have hl2 : Real.log (2 * Real.sqrt d) = Real.log 2 + Real.log (Real.sqrt d) :=
    Real.log_mul (by norm_num) hr.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hh' : h ≠ 0 := hh.ne'
  have hw' : w ≠ 0 := hw.ne'
  have hr' : Real.sqrt d ≠ 0 := hr.ne'
  subst hL1
  rw [hl1] at heq
  rw [hl2]
  have heq2 : L1' = γ * (2 * Real.pi * h / (w * Real.sqrt d))
      - 2 * Real.pi * h / (w * Real.sqrt d) * (Real.log 2 + Real.log (Real.sqrt d))
      - 2 * Real.pi * S / (w * Real.sqrt d) := by
    have h5 : L1' = (2 / (w * Real.sqrt d)) * (Real.pi * h * (Real.log 2 - Real.log (Real.sqrt d))
        + 2 * Real.pi * (h * (γ - Real.log 2) - S / 2))
        - γ * (2 * Real.pi * h / (w * Real.sqrt d)) := by linarith
    rw [h5]
    field_simp
    ring
  rw [heq2]
  field_simp
  ring
end Formalism.HermitianLattices.IntegralLatticeDensity
