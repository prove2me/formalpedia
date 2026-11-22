-- Prove2me | solution 1 for Formalism.UG.P.fSatake_borel_tMat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:56:09.700875+00:00
-- url     : https://prove2.me/submissions/3c21efe5-97d0-4695-851f-a7bac02c8466

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeC
import Theorems.Thm_Formalism_UG_P_fSatake_borel_of_diag

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
theorem _root_.solution {ϖ : L} {m : ℕ} {a : Fin m → ℤ} {t : GU σ n} (ht : ⟪t⟫ = tMat ϖ n m a) :
    IsBorelU t := by
  rw [tMat] at ht
  exact fSatake_borel_of_diag ht
end Formalism.UG.P
