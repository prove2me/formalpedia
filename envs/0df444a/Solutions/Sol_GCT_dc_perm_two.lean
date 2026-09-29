-- Prove2me | solution 1 for GCT.dc_perm_two
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T10:24:24.586276+00:00
-- url     : https://prove2.me/submissions/dc0093fa-594c-4ba9-a945-5bdead9be350

import Mathlib
import Definitions.Def_GCT_determinantal_complexity

set_option autoImplicit false
open GCT MvPolynomial
open scoped BigOperators Matrix

private theorem permanent_two_rep : HasLinearDetRep 2 (paddedPerm 2 2) := by
  classical
  let A : Matrix (Fin 2) (Fin 2) (MvPolynomial (PadVars 2) ℂ) :=
    !![X (some (0, 0)), -X (some (0, 1)); X (some (1, 0)), X (some (1, 1))]
  refine ⟨A, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j
    · exact isHomogeneous_X ℂ _
    · exact (isHomogeneous_X ℂ _).neg
    · exact isHomogeneous_X ℂ _
    · exact isHomogeneous_X ℂ _
  · have hu : (Finset.univ : Finset (Equiv.Perm (Fin 2))) =
        {1, Equiv.swap 0 1} := by decide
    have hne : (1 : Equiv.Perm (Fin 2)) ≠ Equiv.swap 0 1 := by decide
    simp [A, paddedPerm, permPolyPad, Matrix.det_fin_two, Matrix.permanent,
      hu, hne, Finset.sum_insert, Finset.sum_singleton, Fin.prod_univ_two,
      Equiv.swap_apply_def]
    <;> ring

private theorem permanent_two_border_rep : HasBorderLinearDetRep 2 (paddedPerm 2 2) := by
  obtain ⟨A, hA, hdet⟩ := permanent_two_rep
  refine ⟨fun _ => A, fun _ => hA, ?_⟩
  intro d
  change Filter.Tendsto (fun _ : ℕ => coeff d A.det) Filter.atTop
    (nhds (coeff d (paddedPerm 2 2)))
  simpa only [hdet] using (tendsto_const_nhds (x := coeff d A.det))

theorem solution : dc 2 = 2 ∧ dcBar 2 = 2 := by
  constructor
  · exact (show IsLeast {n : ℕ | 2 ≤ n ∧ HasLinearDetRep n (paddedPerm 2 n)} 2 from
      ⟨⟨le_rfl, permanent_two_rep⟩, fun n hn => hn.1⟩).csInf_eq
  · exact (show IsLeast {n : ℕ | 2 ≤ n ∧ HasBorderLinearDetRep n (paddedPerm 2 n)} 2 from
      ⟨⟨le_rfl, permanent_two_border_rep⟩, fun n hn => hn.1⟩).csInf_eq

#print axioms solution
