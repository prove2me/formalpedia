-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.mass_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:46.585804+00:00
-- url     : https://prove2.me/submissions/6cdb3e87-3916-4084-9f4e-0d7804ef3055

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_OneAddInvPowLeExpOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
private lemma sum_Ico_cast_eq_mul_add_triangular (k j : ℕ) :
    ∑ M ∈ Ico (k + 1) (k + j + 1), (M : ℝ) = (j : ℝ) * k + ((j : ℝ) + 1) * j / 2 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show k + (j + 1) + 1 = k + j + 1 + 1 by ring, Finset.sum_Ico_succ_top (by omega), ih]
    push_cast
    ring
end Formalism.HermitianLattices.GenusMassVolumes
end

set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : BracketCoefficients := by
  intro k m hk hm
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hk' : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hI : k - 1 + (j + 1) + 1 = k + j + 1 := by omega
  rw [hI, sum_Ico_cast_eq_mul_add_triangular]
  push_cast
  constructor
  · field_simp <;> ring
  · field_simp <;> ring
end Formalism.HermitianLattices.GenusMassVolumes
