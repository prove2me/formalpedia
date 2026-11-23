-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.pt_mul_ptInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:56:51.840117+00:00
-- url     : https://prove2.me/submissions/ee6da27e-c5b4-4466-892c-eabd0d1ac4e5

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_revIn_inj
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_revIn_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Measure Topology Matrix
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P
open Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
variable {K : Type} [CommRing K]
namespace Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
theorem _root_.solution (s : List ℕ) (t : ℕ → Kˣ) : pt s t * ptInv s t = (1 : Matrix _ _ K) := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single ⟨revIn s a, revIn_lt s a a.2⟩]
  · simp only [pt, ptInv, if_true]
    by_cases hab : a = b
    · subst hab; simp
    · have : revIn s a ≠ revIn s b := fun h => hab (Fin.ext (revIn_inj s h))
      simp [this, hab]
  · intro k _ hk
    simp only [pt]
    rw [if_neg (fun h => hk (Fin.ext h)), zero_mul]
  · simp
end Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
