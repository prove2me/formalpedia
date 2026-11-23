-- Prove2me | solution 1 for Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact.lowW_closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:04:42.558071+00:00
-- url     : https://prove2.me/submissions/f6288025-bd08-4eca-b5aa-a92fcde6d546

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GLRealOpen
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_GlR
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_IsClosedLowUni
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_pt_mul_ptInv
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_ptInv_mul_pt
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_GeneralLinearIntegersOpenCompact_isClosed_lowUni

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
theorem _root_.solution [T2Space K] (s : List ℕ) (t : ℕ → Kˣ) :
    IsClosed (lowW K s t : Set (GL (Fin s.sum) K)) := by
  have e : (lowW K s t : Set (GL (Fin s.sum) K)) =
      (fun g : GL (Fin s.sum) K => (g : Matrix (Fin s.sum) (Fin s.sum) K)) ⁻¹' {x | IsLowUni x} ∩
      (fun g : GL (Fin s.sum) K => ptInv s t * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t) ⁻¹'
        {x | IsLowUni x} := by
    ext g
    constructor
    · rintro ⟨hg, h, hh, he⟩
      refine ⟨hg, ?_⟩
      show IsLowUni (ptInv s t * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t)
      rw [Matrix.mul_assoc, he, ← Matrix.mul_assoc, ptInv_mul_pt, Matrix.one_mul]; exact hh
    · rintro ⟨hg, hh⟩
      refine ⟨hg, _, hh, ?_⟩
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, pt_mul_ptInv, Matrix.one_mul]
  rw [e]
  exact ((isClosed_lowUni _).preimage Units.continuous_val).inter ((isClosed_lowUni _).preimage
    ((continuous_const.mul Units.continuous_val).mul continuous_const))
end Formalism.DoubleCosetMeasures.P.GeneralLinearIntegersOpenCompact
