-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.diagonal_splitting
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:50:08.056791+00:00
-- url     : https://prove2.me/submissions/02bc0be8-b6db-4a56-82ed-6d21a4c626b4

import Definitions.Def_Formalism_FlagUnipotentLattices_HalfDifferenceL1Bound
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_CoefficientLeOperatorNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S7 Finset MeasureTheory
open scoped ComplexOrder
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : DiagSplit := by
  intro X _ μ _ K Rm Mod k0 hM hK hKR
  rw [← integral_add_compl hM hK]
  congr 1
  have hR : IntegrableOn Rm Mod μ := by
    have : IntegrableOn (fun x => K x - k0) Mod μ := hK.integrableOn.sub (integrable_const _)
    refine this.congr_fun (fun x hx => ?_) hM
    simp only
    rw [hKR x hx]; ring
  rw [setIntegral_congr_fun hM hKR, integral_add (integrable_const _) hR]
  simp [mul_comm, Measure.real]
end Formalism.HermitianLatticeCounting.P
