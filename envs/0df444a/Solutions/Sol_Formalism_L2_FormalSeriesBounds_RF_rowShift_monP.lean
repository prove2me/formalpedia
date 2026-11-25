-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.rowShift_monP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:22:04.707683+00:00
-- url     : https://prove2.me/submissions/d3970380-9423-475e-9d79-ae16639adb2b

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rowShift_minor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution {N N' : ℕ} (lam : Fin N × Fin N' → Letter T r n) (σ0 : T) (col : Fin N → Fin n)
    (hlam : ∀ ρ c, keyL (lam (ρ, c)) = (σ0, c.val, col ρ)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) (e : ℕ → ℕ) :
    rowShift r n C σ i i' t (rename lam (monP C N N' e)) = rename lam (monP C N N' e) := by
  unfold monP
  simp only [map_prod, map_pow, rowShift_minor lam σ0 col hlam σ i i' hi t]
end Formalism.L2.FormalSeriesBounds.RF
