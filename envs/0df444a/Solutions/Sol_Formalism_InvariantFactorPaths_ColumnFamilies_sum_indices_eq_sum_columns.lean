-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.sum_indices_eq_sum_columns
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:10:42.275815+00:00
-- url     : https://prove2.me/submissions/20992cd0-68d2-488e-ac2e-82ec18ec4a86

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_LWedge
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_SumIndicesEqSumColumns
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_E_fill
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_ql_fill_card
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : Type*} [AddCommMonoid M] {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ}
    (h1 : lo ≤ mu (lastIdx n)) (h2 : mu 0 ≤ lo + N) (φ : (Fin N → Finset (Fin n)) → M)
    (hφ : ∀ f, (∃ j : Fin N, (f j).card ≠ colH mu (lo + 1 + (j : ℕ))) → φ f = 0) :
    ∑ I : TIdx mu, φ (ql_E lo N (qs_ext mu I)) = ∑ f, φ f := by
  refine Fintype.sum_of_injective (fun I : TIdx mu => ql_E lo N (qs_ext mu I)) ?_ _ _ ?_ (fun _ => rfl)
  · intro I I' h
    funext c
    apply Subtype.ext
    rw [← qs_ext_mem, ← qs_ext_mem]
    have hc := c.2
    simp only [TCols, mem_Ioc] at hc
    have := congrFun h ⟨(c.1 - lo - 1).toNat, by omega⟩
    have e : lo + 1 + ((c.1 - lo - 1).toNat : ℤ) = c.1 := by omega
    simp only [ql_E, e] at this
    exact this
  · intro f hf
    apply hφ
    by_contra hc
    push Not at hc
    exact hf ⟨qs_res mu (ql_fill lo N f) (ql_fill_card hmu h1 h2 f hc), by
      simp only [qs_ext_res hmu, ql_E_fill]⟩
end Formalism.InvariantFactorPaths.ColumnFamilies
