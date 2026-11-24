-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cw_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:58:11.762104+00:00
-- url     : https://prove2.me/submissions/645e0b65-de34-47a2-9fb6-fe5a1af50399

import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_FockPairingHighestWeight
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_ColSums
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_FockModels_TransposeWords_TransposeWordsProofs_CwlApplyWordAppendSingle
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.L2 Formalism.L2.G Formalism.L2.G.Model Formalism.L2.G.Model.TS
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.L2.G.Model.TS
theorem _root_.solution (m e : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e) (hs : cwStrict m = cwStrict e)
    (hc : ∀ s : Fin n, ∑ a : Fin r, m (a, s) = ∑ a : Fin r, e (a, s)) : m = e := by
  classical
  have off : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = e (a, s) := by
    intro a s hne
    rcases lt_or_gt_of_ne hne with c | c
    · rw [hm a s c, he a s c]
    · have h0 := DFunLike.congr_fun hs (a, s)
      simpa [cwStrict, Finsupp.filter_apply, c] using h0
  ext ⟨a, s⟩
  by_cases h : a.val = s.val
  · have h0 := hc s
    rw [← Finset.add_sum_erase _ (fun x => m (x, s)) (Finset.mem_univ a),
      ← Finset.add_sum_erase _ (fun x => e (x, s)) (Finset.mem_univ a)] at h0
    have h2 : ∑ x ∈ Finset.univ.erase a, m (x, s) = ∑ x ∈ Finset.univ.erase a, e (x, s) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply off
      intro hxs
      exact (Finset.mem_erase.mp hx).1 (Fin.ext (by omega))
    omega
  · exact off a s h
end Formalism.L2.G.Model.TS
