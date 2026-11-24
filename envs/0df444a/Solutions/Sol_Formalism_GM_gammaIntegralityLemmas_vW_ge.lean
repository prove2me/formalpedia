-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.vW_ge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:27.968948+00:00
-- url     : https://prove2.me/submissions/068af658-9543-4f5f-af5e-c3e895b52e7f

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_vfact_sum
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_v_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (δ : Fin (N + 1 + 1) × Fin r →₀ ℕ) {T B : ℕ} (hB : Nat.log p T ≤ B)
    (hT : ∀ i, δv δ i ≤ T) :
    ∑ i, padicValNat p (δv δ i).factorial ≤
      padicValNat p (∏ v : Fin (N + 1 + 1) × Fin r, (δ v).factorial) + (N + 2) * (r * B) := by
  rw [v_prod _ _ (fun v _ => (Nat.factorial_pos _).ne'), Fintype.sum_prod_type]
  have : ∀ i : Fin (N + 1 + 1), padicValNat p (δv δ i).factorial ≤
      ∑ c : Fin r, padicValNat p (δ (i, c)).factorial + r * B := by
    intro i
    have := vfact_sum (p := p) (univ : Finset (Fin r)) (fun c => δ (i, c)) (hT i) hB
    simpa [δv] using this
  calc ∑ i, padicValNat p (δv δ i).factorial ≤ ∑ i : Fin (N + 1 + 1), (∑ c : Fin r, padicValNat p (δ (i, c)).factorial + r * B) :=
        sum_le_sum (fun i _ => this i)
    _ = _ := by rw [sum_add_distrib]; simp
end Formalism.GM.gammaIntegralityLemmas
