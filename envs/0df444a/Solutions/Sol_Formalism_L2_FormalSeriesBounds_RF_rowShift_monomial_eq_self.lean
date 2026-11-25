-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.rowShift_monomial_eq_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:24:01.267951+00:00
-- url     : https://prove2.me/submissions/a727579f-b6ea-4a78-b991-a35a1c6fc0fd

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rowShift_minor_lin
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


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
variable {N N' : ℕ} (Φ : MvPolynomial (Fin N × Fin N') C →ₐ[C] MvPolynomial (Letter T r n) C) (σ0 : T)
  (w : Fin N → Fin 2 → C) (lt : Fin N × Fin N' → Fin 2 → Letter T r n) (colf : Fin N → Fin 2 → Fin n)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C)
    (e : ℕ → ℕ) : rowShift r n C σ i i' t (Φ (monP C N N' e)) = Φ (monP C N N' e) := by
  unfold monP
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_pow, map_pow, rowShift_minor_lin Φ σ0 w lt colf hΦ hlt σ i i' hi t k]
end Formalism.L2.FormalSeriesBounds.RF
