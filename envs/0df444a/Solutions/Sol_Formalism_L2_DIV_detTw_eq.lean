-- Prove2me | solution 1 for Formalism.L2.DIV.detTw_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:18.392284+00:00
-- url     : https://prove2.me/submissions/7f685fad-242a-4704-8f10-77c505d00a0d

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) K) :
    detTwK lam g = ∏ τ, ((g τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det ^ (lam τ).detShift := by
  unfold detTwK detPow
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [Units.val_zpow_eq_zpow_val]
  rfl
end Formalism.L2.DIV
