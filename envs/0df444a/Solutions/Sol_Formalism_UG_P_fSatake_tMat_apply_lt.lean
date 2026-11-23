-- Prove2me | solution 1 for Formalism.UG.P.fSatake_tMat_apply_lt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:27:29.259545+00:00
-- url     : https://prove2.me/submissions/95d9d397-f0a1-46cf-b453-ead311d7ebff

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
theorem _root_.solution (ϖ : L) {m : ℕ} (a : Fin m → ℤ) (j : Fin m) (hj : (j : ℕ) < n) :
    tMat ϖ n m a ⟨j, hj⟩ ⟨j, hj⟩ = ϖ ^ (a j) := by
  simp [tMat, j.isLt]
end Formalism.UG.P
