-- Prove2me | solution 1 for CauchyRiemannIndex.isSymplectic_left_of_diamond
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T17:36:47.984738+00:00
-- url     : https://prove2.me/submissions/b3f4c73f-f21f-4d9b-bc4a-9a605f940c82

import Definitions.Def_CauchyRiemannIndex_Setting
import Definitions.Def_ConleyZehnder_Setting

open Matrix

namespace CRLK5L

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

end CRLK5L

namespace CauchyRiemannIndex

open CRLK5L

theorem isSymplectic_left_of_diamond_aux {n' n'' : ℕ} (M : Mat n') (B : Mat n'')
    (h : IsSymplectic (ConleyZehnder.diamond M B)) : IsSymplectic M := by
  unfold IsSymplectic at *
  replace h := SymplecticGroup.mem_iff.mp h
  apply SymplecticGroup.mem_iff.mpr
  change Matrix.reindex (dEquiv n' n'') (dEquiv n' n'') (Matrix.fromBlocks M 0 0 B) *
      Matrix.J (Fin (n' + n'')) ℝ *
      (Matrix.reindex (dEquiv n' n'') (dEquiv n' n'') (Matrix.fromBlocks M 0 0 B))ᵀ = _ at h
  rw [J_eq, Matrix.transpose_reindex] at h
  simp only [Matrix.reindex_apply] at h
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at h
  have h2 := congrArg (fun X => (X.submatrix (dEquiv n' n'') (dEquiv n' n'')).toBlocks₁₁) h
  simpa only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.transpose_zero] using h2

end CauchyRiemannIndex

open CauchyRiemannIndex in
theorem solution {n' n'' : ℕ} (A : Mat n') (B : Mat n'')
    (h : IsSymplectic (ConleyZehnder.diamond A B)) : IsSymplectic A :=
  CauchyRiemannIndex.isSymplectic_left_of_diamond_aux A B h
