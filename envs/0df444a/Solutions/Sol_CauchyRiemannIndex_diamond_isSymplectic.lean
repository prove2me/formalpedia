-- Prove2me | solution 1 for CauchyRiemannIndex.diamond_isSymplectic
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T16:56:58.112669+00:00
-- url     : https://prove2.me/submissions/9d4cedfe-6b65-466b-8c01-f68913161194

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting

open Matrix

namespace CRLDiamond

/-- The coordinate equivalence used by `ConleyZehnder.diamond`. -/
abbrev dEquiv (n' n'' : ℕ) :
    ((Fin n' ⊕ Fin n') ⊕ (Fin n'' ⊕ Fin n'')) ≃ (Fin (n' + n'') ⊕ Fin (n' + n'')) :=
  (Equiv.sumSumSumComm (Fin n') (Fin n') (Fin n'') (Fin n'')).trans
    (Equiv.sumCongr finSumFinEquiv finSumFinEquiv)

lemma J_eq (n' n'' : ℕ) :
    Matrix.J (Fin (n' + n'')) ℝ = Matrix.reindex (dEquiv n' n'') (dEquiv n' n'')
      (Matrix.fromBlocks (Matrix.J (Fin n') ℝ) 0 0 (Matrix.J (Fin n'') ℝ)) := by
  ext i j
  obtain ⟨a, rfl⟩ := (dEquiv n' n'').surjective i
  obtain ⟨b, rfl⟩ := (dEquiv n' n'').surjective j
  rcases a with (a | a) | (a | a) <;> rcases b with (b | b) | (b | b) <;>
    simp [Matrix.J, Matrix.reindex_apply, Matrix.one_apply]
  all_goals
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

end CRLDiamond

namespace CauchyRiemannIndex

open CRLDiamond

theorem diamond_isSymplectic_aux {n' n'' : ℕ} (A : Mat n') (B : Mat n'') (hA : IsSymplectic A)
    (hB : IsSymplectic B) : IsSymplectic (ConleyZehnder.diamond A B) := by
  unfold IsSymplectic at *
  rw [SymplecticGroup.mem_iff] at *
  change Matrix.reindex (dEquiv n' n'') (dEquiv n' n'') (Matrix.fromBlocks A 0 0 B) *
      Matrix.J (Fin (n' + n'')) ℝ *
      (Matrix.reindex (dEquiv n' n'') (dEquiv n' n'') (Matrix.fromBlocks A 0 0 B))ᵀ = _
  rw [J_eq, Matrix.transpose_reindex, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [hA, hB]

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution {n' n'' : ℕ} (A : Mat n') (B : Mat n'') (hA : IsSymplectic A)
    (hB : IsSymplectic B) : IsSymplectic (ConleyZehnder.diamond A B) :=
  CauchyRiemannIndex.diamond_isSymplectic_aux A B hA hB
