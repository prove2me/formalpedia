-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.initMinor_invariant
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:34:55.022026+00:00
-- url     : https://prove2.me/submissions/264078c0-7b1a-4cbb-bced-818f49aed6ee

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementA
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Theorems.Thm_Formalism_GradedWeylDivisibility_algHom_det_of
import Theorems.Thm_Formalism_GradedWeylDivisibility_colAddGen_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {R : Type*} [CommRing R] {r n s : ℕ}
    (I : Fin s → Fin r) (hs : s ≤ n) (l j : Fin n) (hlj : l < j) :
    colAddGen R l j (initMinor R I hs) = rename some (initMinor R I hs) := by
  unfold initMinor
  rw [algHom_det_of, algHom_det_of]
  simp only [colAddGen_X, rename_X]
  by_cases hj : j.val < s
  · have hl : l.val < s := Nat.lt_trans (show l.val < j.val from hlj) hj
    have hjl : (⟨j.val, hj⟩ : Fin s) ≠ ⟨l.val, hl⟩ := by
      intro h
      exact hlj.ne' (Fin.ext (Fin.mk.inj_iff.mp h))
    rw [← Matrix.det_updateCol_add_smul_self
      (Matrix.of fun p q : Fin s =>
        (X (some (I p, Fin.castLE hs q)) : MvPolynomial (Option (Fin r × Fin n)) R)) hjl (X none)]
    congr 1
    ext p q
    simp only [Matrix.updateCol_apply, Matrix.of_apply]
    by_cases hq : q = ⟨j.val, hj⟩
    · subst hq
      have e1 : Fin.castLE hs ⟨j.val, hj⟩ = j := Fin.ext rfl
      have e2 : Fin.castLE hs ⟨l.val, hl⟩ = l := Fin.ext rfl
      rw [e1, e2]
      simp
    · have hne : Fin.castLE hs q ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        exact hq (Fin.ext hv)
      rw [if_neg hne, if_neg hq]
  · congr 1
    ext p q
    simp only [Matrix.of_apply]
    have hne : Fin.castLE hs q ≠ j := by
      intro h
      apply hj
      rw [← h]
      exact q.isLt
    rw [if_neg hne]
end Formalism.GradedWeylDivisibility
