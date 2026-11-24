-- Prove2me | solution 1 for Formalism.CohomologicalDescent.LR.lrf_pt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:18.60405+00:00
-- url     : https://prove2.me/submissions/89876f20-780d-4160-87f4-0a21120abe1f

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrfcApplyWordAppendSingle
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_Phi_nil
import Theorems.Thm_Formalism_CohomologicalDescent_LR_lrfc_Phi_append_single
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable {R : Type*} [CommRing R] {r n : ℕ}
namespace Formalism.CohomologicalDescent.LR
theorem _root_.solution (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (hP : L.Pairwise fun l l' => l.2.2 ≠ l'.2.2 ∧ l.2.1 ≠ l'.1)
    (hM : ∀ l ∈ L, l.1.val = l.2.2.2.val ∧ l.2.2.1 = l.2.1) (v : Fin r × Fin n) :
    eval (lrf_idS R r n) (lrfc_Phi L (X v)) =
      C (idFrame R r n v) + if v ∈ L.map (·.2.2) then X v else 0 := by
  classical
  induction L using List.reverseRecOn generalizing v with
  | nil => simp [lrfc_Phi_nil, lrf_idS]
  | append_singleton w l ih =>
    rw [List.pairwise_append] at hP
    obtain ⟨hPw, -, hPl⟩ := hP
    have hMw : ∀ l ∈ w, l.1.val = l.2.2.2.val ∧ l.2.2.1 = l.2.1 := fun x hx => hM x (by simp [hx])
    have hMl := hM l (by simp)
    have ihw := ih hPw hMw
    have hlw : l.2.2 ∉ w.map (·.2.2) := by
      intro h
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
      exact (hPl x hx l (by simp)).1 hxe
    have hmem : ∀ u : Fin r × Fin n, u ∈ (w ++ [l]).map (·.2.2) ↔ (u ∈ w.map (·.2.2) ∨ u = l.2.2) := by
      intro u
      simp
    rw [lrfc_Phi_append_single, lrfc_tau, aeval_X]
    by_cases hv : v.1 = l.2.1
    · rw [if_pos hv, map_add, map_mul, map_add, map_mul, ihw v, ihw (l.1, v.2)]
      have hC : lrfc_Phi w (C (X l.2.2)) = C (X l.2.2 : MvPolynomial (Fin r × Fin n) R) :=
        (lrfc_Phi w).commutes (X l.2.2)
      rw [hC, eval_C]
      have hs : (l.1, v.2) ∉ w.map (·.2.2) := by
        intro h
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
        apply (hPl x hx l (by simp)).2
        rw [← (hMw x hx).2, hxe]
      rw [if_neg hs, add_zero]
      by_cases hc : l.1.val = v.2.val
      · have hvl : v = l.2.2 := by
          refine Prod.ext (by rw [hv, hMl.2]) (Fin.ext ?_)
          rw [← hc, hMl.1]
        have h1 : idFrame R r n (l.1, v.2) = 1 := by simp [idFrame, hc]
        rw [h1, if_neg (by rw [hvl]; exact hlw), if_pos ((hmem v).2 (Or.inr hvl)), ← hvl]
        simp
      · have hvl : v ≠ l.2.2 := by
          intro h
          apply hc
          rw [h, hMl.1]
        have h1 : idFrame R r n (l.1, v.2) = 0 := by simp [idFrame, hc]
        rw [h1]
        have e : (v ∈ (w ++ [l]).map (·.2.2)) ↔ v ∈ w.map (·.2.2) := by
          rw [hmem]
          exact or_iff_left hvl
        simp only [e]
        simp
    · have hvl : v ≠ l.2.2 := by
        intro h
        apply hv
        rw [h, hMl.2]
      have e : (v ∈ (w ++ [l]).map (·.2.2)) ↔ v ∈ w.map (·.2.2) := by
        rw [hmem]
        exact or_iff_left hvl
      rw [if_neg hv, add_zero, ihw v]
      simp only [e]
end Formalism.CohomologicalDescent.LR
