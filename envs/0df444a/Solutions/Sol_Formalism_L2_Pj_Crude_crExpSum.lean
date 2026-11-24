-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crExpSum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:21:20.761737+00:00
-- url     : https://prove2.me/submissions/a4d21020-f499-4900-b520-3e18cdf8a35f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crTele

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (a : T → ℕ → ℕ) (ha : Dom r a) (σ : T) (i : Fin (r σ)) :
    (∑ kk : Fin (r σ), if (i : ℕ) < (kk : ℕ) + 1 then crExp r a σ kk else 0) = a σ i := by
  have hi := i.isLt
  let f : ℕ → ℕ := fun j => if j < r σ then a σ j else 0
  have hf : ∀ j, j < r σ → f (j + 1) ≤ f j := by
    intro j hj
    simp only [f]
    by_cases h : j + 1 < r σ
    · rw [if_pos h, if_pos hj]
      exact ha σ ⟨j, hj⟩ ⟨j + 1, h⟩ (Fin.mk_le_mk.mpr (Nat.le_succ j))
    · rw [if_neg h]
      exact Nat.zero_le _
  have hR : f (r σ) = 0 := by simp [f]
  have key := crTele f (r σ) hf hR (r σ - i) i (by omega)
  have e1 : (∑ kk : Fin (r σ), if (i : ℕ) < (kk : ℕ) + 1 then crExp r a σ kk else 0) =
      ∑ j ∈ Finset.range (r σ), (if (i : ℕ) ≤ j then f j - f (j + 1) else 0) := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun kk _ => ?_
    have hk := kk.isLt
    simp only [f, crExp, if_pos hk, Nat.lt_add_one_iff]
  rw [e1, key]
  simp [f, hi]
end Formalism.L2.Pj.Crude
