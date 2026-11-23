-- Prove2me | solution 1 for Formalism.UG.P.fSatake_ne_zero_of_borel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:13.699269+00:00
-- url     : https://prove2.me/submissions/25194918-b5a4-4312-bb7a-1baad8fa42dc

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC

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
local notation "⟪" b "⟫" => (((b : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
namespace Formalism.UG.P
theorem _root_.solution {b : GU σ n} (hb : IsBorelU b) (i : Fin n) : ⟪b⟫ i i ≠ 0 := by
  intro h
  have hdet : (⟪b⟫).det = ∏ i, ⟪b⟫ i i :=
    Matrix.det_of_upperTriangular (fun i j hij => hb i j hij)
  have hu : IsUnit (⟪b⟫).det := (Matrix.isUnit_iff_isUnit_det _).mp (Units.isUnit _)
  exact hu.ne_zero (by rw [hdet]; exact Finset.prod_eq_zero (Finset.mem_univ i) h)
end Formalism.UG.P
