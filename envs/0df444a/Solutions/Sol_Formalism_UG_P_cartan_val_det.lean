-- Prove2me | solution 1 for Formalism.UG.P.cartan_val_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:42:10.290774+00:00
-- url     : https://prove2.me/submissions/1a99096e-e95b-479a-b29c-bcd22d091c99

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Theorems.Thm_Formalism_UG_P_cartan_entries_of_mem
import Theorems.Thm_Formalism_UG_P_cartan_det_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] (O : Subring L) {n : Type} [Fintype n] [DecidableEq n]
variable {Γ : Type} [LinearOrderedCommGroupWithZero Γ]
namespace Formalism.UG.P
theorem _root_.solution (val : Valuation L Γ) (hO : ∀ x, x ∈ O ↔ val x ≤ 1) (U : GL n L)
    (hU : U ∈ GLint n O) : val (U : Matrix n n L).det = 1 := by
  have h1 := cartan_entries_of_mem O U hU
  have h2 := cartan_entries_of_mem O U⁻¹ (inv_mem hU)
  have ha : val (U : Matrix n n L).det ≤ 1 := (hO _).mp (cartan_det_mem O _ h1)
  have hb : val ((U⁻¹ : GL n L) : Matrix n n L).det ≤ 1 := (hO _).mp (cartan_det_mem O _ h2)
  have hprod : val (U : Matrix n n L).det * val ((U⁻¹ : GL n L) : Matrix n n L).det = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      map_one]
  refine le_antisymm ha ?_
  calc (1 : Γ) = _ := hprod.symm
    _ ≤ _ := mul_le_of_le_one_right' hb
end Formalism.UG.P
