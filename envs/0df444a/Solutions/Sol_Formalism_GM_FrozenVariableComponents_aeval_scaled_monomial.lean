-- Prove2me | solution 1 for Formalism.GM.FrozenVariableComponents.aeval_scaled_monomial
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:15:07.380191+00:00
-- url     : https://prove2.me/submissions/e9ebb869-e6b9-45d2-b1fe-f4d964c560b2

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_apply
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_castSucc
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_comb_last
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_llPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_etaPart_comb
import Theorems.Thm_Formalism_GM_FrozenVariableComponents_emb_inj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_apply
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_castSucc
attribute [local simp] Formalism.GM.FrozenVariableComponents.comb_last
attribute [local simp] Formalism.GM.FrozenVariableComponents.llPart_comb
attribute [local simp] Formalism.GM.FrozenVariableComponents.etaPart_comb

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.FrozenVariableComponents
theorem _root_.solution (ρ : Fin r) (m : Fin N × Fin r →₀ ℕ) (a : ℚ_[p]) :
    aeval (fun x : Fin N × Fin r => (X (Fin.last N, ρ) * X (emb x) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]))
      (monomial m a) = X (Fin.last N, ρ) ^ m.degree * monomial (Finsupp.mapDomain emb m) a := by
  have h1 : (monomial (Finsupp.mapDomain emb m) a : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) =
      algebraMap ℚ_[p] (MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) a *
        m.prod (fun x k => (X (emb x) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p]) ^ k) := by
    first
    | rw [monomial_eq, Finsupp.prod_mapDomain_index_inj emb_inj, MvPolynomial.algebraMap_eq]
    | rw [monomial_eq, Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _),
        MvPolynomial.algebraMap_eq]
    | (rw [← rename_monomial]
       show aeval (fun i => (X (emb i) : MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p])) (monomial m a) = _
       rw [aeval_monomial])
    all_goals rfl
  have hdeg : m.degree = ∑ i ∈ m.support, m i := by
    first
    | rfl
    | simp [Finsupp.degree]
    | exact Finsupp.degree_eq_sum m
  rw [aeval_monomial, h1]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [hdeg]
  ring
end Formalism.GM.FrozenVariableComponents
