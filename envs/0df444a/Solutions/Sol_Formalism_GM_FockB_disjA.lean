-- Prove2me | solution 1 for Formalism.GM.FockB.disjA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:18:41.022868+00:00
-- url     : https://prove2.me/submissions/c72dfdb5-a2c1-4cf4-ae4d-2e3a9175d431

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelDecomp
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Theorems.Thm_Formalism_GM_FockB_pos_ne
import Theorems.Thm_Formalism_GM_FockB_pos_ne_succ
import Theorems.Thm_Formalism_GM_FockB_finPos_val

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FockB
open MvPolynomial Finset Formalism.GM.M
variable {N r : ℕ} {D : BlockData N}
namespace Formalism.GM.FockB
theorem _root_.solution (hB : D.BlockOK) {a b : Option (Fin D.T.t)} (hab : a ≠ b) :
    Disjoint (Va (wA (r := r) D) (eA D) (zA D) (sA D) a) (Va (wA D) (eA D) (zA D) (sA D) b) := by
  have h2 := hB.2.2.2
  rw [Set.disjoint_left]
  intro v hva hvb
  simp only [Va, V, Set.mem_union, Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff] at hva hvb
  rcases a with _ | i <;> rcases b with _ | i'
  · exact hab rfl
  · have h1 := hB.2.1 i'
    have hv0 : (finPos N (D.T.pos i') : ℕ) = D.T.pos i' := finPos_val (by omega)
    have hv1 : (finPos N (D.T.pos i' + 1) : ℕ) = D.T.pos i' + 1 := finPos_val (by omega)
    have hi := i'.isLt
    rcases hva with ((⟨c, rfl⟩ | ⟨c, rfl⟩) | rfl | rfl) <;> rcases hvb with ((⟨c', h⟩ | ⟨c', h⟩) | h | h) <;>
      simp only [wA, eA, zA, sA, xiVar, scalZ, scalS, Option.elim, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at h <;> omega
  · have h1 := hB.2.1 i
    have hv0 : (finPos N (D.T.pos i) : ℕ) = D.T.pos i := finPos_val (by omega)
    have hv1 : (finPos N (D.T.pos i + 1) : ℕ) = D.T.pos i + 1 := finPos_val (by omega)
    have hi := i.isLt
    rcases hva with ((⟨c, rfl⟩ | ⟨c, rfl⟩) | rfl | rfl) <;> rcases hvb with ((⟨c', h⟩ | ⟨c', h⟩) | h | h) <;>
      simp only [wA, eA, zA, sA, xiVar, scalZ, scalS, Option.elim, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at h <;> omega
  · have hii : i ≠ i' := fun h => hab (by rw [h])
    have hii' : (i : ℕ) ≠ i' := fun h => hii (Fin.ext h)
    have h1 := hB.2.1 i
    have h1' := hB.2.1 i'
    have q1 := pos_ne hB hii
    have q2 := pos_ne_succ hB i i'
    have q3 := pos_ne_succ hB i' i
    have hv0 : (finPos N (D.T.pos i) : ℕ) = D.T.pos i := finPos_val (by omega)
    have hv1 : (finPos N (D.T.pos i + 1) : ℕ) = D.T.pos i + 1 := finPos_val (by omega)
    have hv0' : (finPos N (D.T.pos i') : ℕ) = D.T.pos i' := finPos_val (by omega)
    have hv1' : (finPos N (D.T.pos i' + 1) : ℕ) = D.T.pos i' + 1 := finPos_val (by omega)
    rcases hva with ((⟨c, rfl⟩ | ⟨c, rfl⟩) | rfl | rfl) <;> rcases hvb with ((⟨c', h⟩ | ⟨c', h⟩) | h | h) <;>
      simp only [wA, eA, zA, sA, xiVar, scalZ, scalS, Option.elim, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        Prod.mk.injEq, Fin.ext_iff, Fin.val_castSucc, Fin.val_last] at h <;> omega
end Formalism.GM.FockB
