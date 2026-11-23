-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Herglotz.fac_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:01.246359+00:00
-- url     : https://prove2.me/submissions/40c48233-8306-4a17-8c98-a82464131aba

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Herglotz
open Real Filter Topology Finset
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.Herglotz
theorem _root_.solution (t : ℤ) : Tendsto (fun N : ℕ => fac N t) atTop (𝓝 1) := by
  have h : ∀ᶠ N : ℕ in atTop, 1 - (|(t : ℝ)|) / N = fac N t := by
    filter_upwards [eventually_ge_atTop (t.natAbs + 1)] with N hN
    unfold fac
    have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    have h2 : ((((N : ℤ) - |t|).toNat : ℕ) : ℤ) = (N : ℤ) - |t| := by
      apply Int.toNat_of_nonneg
      rw [Int.abs_eq_natAbs]
      omega
    have h3 : ((((N : ℤ) - |t|).toNat : ℕ) : ℝ) = (N : ℝ) - |(t : ℝ)| := by
      rw [← Int.cast_natCast, h2]
      push_cast
      ring
    rw [h3]
    field_simp
  refine Tendsto.congr' h ?_
  simpa using (tendsto_const_div_atTop_nhds_zero_nat (|(t : ℝ)|)).const_sub 1
end Formalism.FourierDecayAlt.P.Herglotz
