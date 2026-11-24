-- Prove2me | solution 1 for Formalism.L2.G.Model.TS.cw_foldl_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T09:58:12.426416+00:00
-- url     : https://prove2.me/submissions/54e0203c-ad05-4a15-8c69-671d3f674b3a

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
theorem _root_.solution (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (h1 : ∀ l ∈ L, l.2.2.1 = l.2.1 ∧ l.2.2.2.val = l.1.val ∧ l.1.val < l.2.1.val)
    (h2 : L.Pairwise fun l l' => l'.1.val ≤ l.1.val ∧ l.2.2 ≠ l'.2.2) :
    L.foldl (fun y l => cwUpd l y) (idFrame (MvPolynomial (Fin r × Fin n) R) r n) =
      fun v => idFrame (MvPolynomial (Fin r × Fin n) R) r n v + if v ∈ L.map (·.2.2) then X v else 0 := by
  classical
  induction L using List.reverseRecOn with
  | nil => funext v; simp
  | append_singleton w l ih =>
    have h1w : ∀ l ∈ w, l.2.2.1 = l.2.1 ∧ l.2.2.2.val = l.1.val ∧ l.1.val < l.2.1.val :=
      fun x hx => h1 x (by simp [hx])
    rw [List.pairwise_append] at h2
    obtain ⟨h2w, -, h2l⟩ := h2
    have hl := h1 l (by simp)
    rw [List.foldl_append, ih h1w h2w]
    funext v
    simp only [List.foldl_cons, List.foldl_nil, cwUpd]
    have hno : (l.1, v.2) ∉ w.map (·.2.2) := by
      intro hmem
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hmem
      have a1 := h1w x hx
      have a2 := (h2l x hx l (by simp)).1
      have a3 : x.2.2.1 = l.1 := by rw [hxe]
      have a4 : x.2.1 = l.1 := by rw [← a1.1, a3]
      rw [a4] at a1
      omega
    have hlw : l.2.2 ∉ w.map (·.2.2) := by
      intro hmem
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hmem
      exact (h2l x hx l (by simp)).2 hxe
    rw [if_neg hno, add_zero]
    by_cases hv : v = l.2.2
    · subst hv
      have e1 : l.2.2.1 = l.2.1 := hl.1
      have e2 : idFrame (MvPolynomial (Fin r × Fin n) R) r n (l.1, l.2.2.2) = 1 := by
        simp [idFrame, hl.2.1]
      rw [if_neg hlw, if_pos e1, e2]
      simp
    · have hcond : ¬ (v.1 = l.2.1 ∧ l.1.val = v.2.val) := by
        rintro ⟨c1, c2⟩
        apply hv
        apply Prod.ext
        · rw [c1, hl.1]
        · apply Fin.ext; rw [← c2, hl.2.1]
      have e3 : (if v.1 = l.2.1 then X l.2.2 * idFrame (MvPolynomial (Fin r × Fin n) R) r n (l.1, v.2) else 0) = 0 := by
        split_ifs with c1
        · have : ¬ l.1.val = v.2.val := fun c2 => hcond ⟨c1, c2⟩
          simp [idFrame, this]
        · rfl
      rw [e3, add_zero]
      simp [hv]
end Formalism.L2.G.Model.TS
