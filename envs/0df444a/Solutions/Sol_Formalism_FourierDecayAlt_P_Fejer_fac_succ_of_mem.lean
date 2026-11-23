-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fejer.fac_succ_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:50.980309+00:00
-- url     : https://prove2.me/submissions/23591d13-3691-46ce-ac6b-0e83e2f11fd6

import Definitions.Def_Formalism_HermitianCurvature_StatementH
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Herglotz
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FacSuccOfNotMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fejer
open Real Finset Formalism.FourierDecayAlt.P.Herglotz
variable {d : ℕ}
namespace Formalism.FourierDecayAlt.P.Fejer
theorem _root_.solution (N : ℕ) (t : ℤ) (ht : t ∈ Finset.Icc (-(N : ℤ)) N) :
    fac (N + 1) t = 1 - |((t : ℤ) : ℝ)| / ((N : ℝ) + 1) := by
  rw [Finset.mem_Icc] at ht
  have habs : |t| ≤ (N : ℤ) := abs_le.2 ht
  have hz : (0 : ℤ) ≤ ((N + 1 : ℕ) : ℤ) - |t| := by push_cast; omega
  have hN0 : ((N : ℝ) + 1) ≠ 0 := by positivity
  unfold fac
  rw [show (((((N + 1 : ℕ) : ℤ) - |t|).toNat : ℕ) : ℝ)
      = ((((((N + 1 : ℕ) : ℤ) - |t|).toNat : ℕ) : ℤ) : ℝ) by norm_cast,
    Int.toNat_of_nonneg hz]
  push_cast
  field_simp
end Formalism.FourierDecayAlt.P.Fejer
