-- Prove2me | solution 1 for Formalism.UG.P.fSatake_borel_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:13.396794+00:00
-- url     : https://prove2.me/submissions/214b36e4-c9ce-4089-b3f3-fe8a507c12ee

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Theorems.Thm_Formalism_UG_P_fSatake_borel_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
namespace Formalism.UG.P
theorem _root_.solution {b : GU σ n} (hb : IsBorelU b) : IsBorelU b⁻¹ := by
  rw [fSatake_borel_iff] at hb ⊢
  haveI : Invertible (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := Units.invertible _
  have := Matrix.blockTriangular_inv_of_blockTriangular hb
  simpa [Matrix.coe_units_inv] using this
end Formalism.UG.P
