-- Prove2me | solution 1 for Formalism.UG.P.fSatake_borel_of_diag
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:49:09.497907+00:00
-- url     : https://prove2.me/submissions/fca7f5f5-70da-462a-b139-1eddb164b89f

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
theorem _root_.solution {d : GU σ n} {e : Fin n → L} (hd : ⟪d⟫ = Matrix.diagonal e) :
    IsBorelU d := by
  intro i j hij
  change ⟪d⟫ i j = 0
  rw [hd, Matrix.diagonal_apply_ne _ (ne_of_lt hij).symm]
end Formalism.UG.P
