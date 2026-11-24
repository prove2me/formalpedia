-- Prove2me | solution 1 for Formalism.REAL.spectrum_pos_of_posSemidef_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:36:01.772804+00:00
-- url     : https://prove2.me/submissions/97f5a52a-f70e-44db-a8da-fa2caafd3f46

import Definitions.Def_Formalism_RealPlaceAnalysis_Complexify
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IndefiniteUnitaryPreservesForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open Formalism Formalism.REAL
variable {n : ℕ}
namespace Formalism.REAL
theorem _root_.solution {P : Matrix (Fin n) (Fin n) ℂ} (hP : P.PosSemidef) (hu : IsUnit P) :
    ∀ x ∈ spectrum ℝ P, 0 < x := by
  intro x hx
  have h0 : 0 ≤ x := by
    open scoped MatrixOrder in
    first
    | exact spectrum_nonneg_of_nonneg (Matrix.nonneg_iff_posSemidef.mpr hP) hx
    | exact spectrum_nonneg_of_nonneg hP.nonneg hx
  have hne : x ≠ 0 := by
    rintro rfl
    first
    | exact (spectrum.zero_notMem_iff ℝ).mpr hu hx
    | exact (spectrum.zero_not_mem_iff ℝ).mpr hu hx
  exact lt_of_le_of_ne h0 (Ne.symm hne)
end Formalism.REAL
