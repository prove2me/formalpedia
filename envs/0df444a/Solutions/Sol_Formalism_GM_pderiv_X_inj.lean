-- Prove2me | solution 1 for Formalism.GM.pderiv_X_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:25:59.794809+00:00
-- url     : https://prove2.me/submissions/3116aab5-fbb1-4e5e-9414-9db0ac41f90d

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GM
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
variable {w e}
private theorem mvPolynomial_pderiv_X_of_ne {i j : σ} (h : j ≠ i) : pderiv i (X j : MvPolynomial σ k) = 0 := by
  exact pderiv_X_of_ne h
private theorem mvPolynomial_pderiv_X_self (i : σ) : pderiv i (X i : MvPolynomial σ k) = 1 := by
  exact pderiv_X_self i
end
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset
variable {k σ : Type} [Field k] {r : ℕ} (w e : Fin r → σ)
variable {w e}
namespace Formalism.GM
theorem _root_.solution {f : Fin r → σ} (hf : Function.Injective f) (c d : Fin r) :
    pderiv (f c) (X (f d) : MvPolynomial σ k) = if d = c then 1 else 0 := by
  by_cases h : d = c
  · subst h
    rw [if_pos rfl]
    exact mvPolynomial_pderiv_X_self _
  · rw [if_neg h]
    exact mvPolynomial_pderiv_X_of_ne (fun h' => h (hf h'))
end Formalism.GM
