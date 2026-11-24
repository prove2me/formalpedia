-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.relevant_pair_criterion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:44:09.067063+00:00
-- url     : https://prove2.me/submissions/cc9216ad-b979-4194-b05c-9b7b0c46d756

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.RelevantPair := by
  intro m w d hd a b hab hw x
  have hab' : a ≠ b := ne_of_lt hab
  have hw' : w a ≠ w b := ne_of_gt hw
  have hdb := hd b
  set c : ℂ := -(x * d a / d b) with hc
  have hE1P : C2.Eij (w a) (w b) c * C2.monoP w d = C2.Eij (w a) b (c * d b) := by
    ext i j
    simp only [Matrix.mul_apply, C2.Eij, C2.monoP, Matrix.of_apply]
    rw [Finset.sum_eq_single (w b)]
    · by_cases hi : i = w a <;> by_cases hj : j = b
      · subst hj; simp [hi]
      · simp [hi, hj, Equiv.apply_eq_iff_eq, Ne.symm hj]
      · simp [hi]
      · simp [hi]
    · intro l _ hl
      simp [hl]
    · simp
  have hPE2 : C2.monoP w d * C2.Eij a b x = C2.Eij (w a) b (d a * x) := by
    ext i j
    simp only [Matrix.mul_apply, C2.Eij, C2.monoP, Matrix.of_apply]
    rw [Finset.sum_eq_single a]
    · by_cases hi : i = w a <;> by_cases hj : j = b <;> simp [hi, hj]
    · intro l _ hl
      simp [hl]
    · simp
  have hEE : ∀ v : ℂ, C2.Eij (w a) b v * C2.Eij a b x = 0 := by
    intro v
    ext i j
    simp only [Matrix.mul_apply, C2.Eij, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : l = b
    · subst hl
      simp [Ne.symm hab']
    · simp [hl]
  have hsum : C2.Eij (w a) b (c * d b) + C2.Eij (w a) b (d a * x) = 0 := by
    ext i j
    simp only [C2.Eij, Matrix.of_apply, Matrix.add_apply, Matrix.zero_apply]
    split_ifs
    · rw [hc]
      field_simp
      ring
    · ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j hij
    simp only [Matrix.add_apply, Matrix.one_apply, C2.Eij, Matrix.of_apply]
    rw [if_neg (ne_of_lt hij), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩
      exact absurd hij (not_lt.2 hw.le)
  · intro i
    simp only [Matrix.add_apply, Matrix.one_apply_eq, C2.Eij, Matrix.of_apply]
    rw [if_neg]
    · simp
    · rintro ⟨h1, h2⟩
      exact hw' (h1.symm.trans h2)
  · intro i j hij
    simp only [Matrix.add_apply, Matrix.one_apply, C2.Eij, Matrix.of_apply]
    rw [if_neg (ne_of_gt hij), if_neg]
    · simp
    · rintro ⟨rfl, rfl⟩
      exact absurd hij (not_lt.2 hab.le)
  · intro i
    simp only [Matrix.add_apply, Matrix.one_apply_eq, C2.Eij, Matrix.of_apply]
    rw [if_neg]
    · simp
    · rintro ⟨h1, h2⟩
      exact hab' (h1.symm.trans h2)
  · have e : (1 + C2.Eij (w a) (w b) c) * C2.monoP w d * (1 + C2.Eij a b x) =
        C2.monoP w d + (C2.Eij (w a) (w b) c * C2.monoP w d + C2.monoP w d * C2.Eij a b x) +
          C2.Eij (w a) (w b) c * C2.monoP w d * C2.Eij a b x := by
      noncomm_ring
    rw [e, hE1P, hPE2, hsum, hEE, add_zero, add_zero]
  · have hL : C2.simpleLow (1 + C2.Eij (w a) (w b) c) =
        if (w a).val = (w b).val + 1 then c else 0 := by
      unfold C2.simpleLow
      rw [Finset.sum_eq_single (w b)]
      · by_cases hq : (w a).val = (w b).val + 1
        · have h : (w b).val + 1 < m := hq ▸ (w a).isLt
          rw [dif_pos h, if_pos hq]
          simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff, hq]
        · rw [if_neg hq]
          split_ifs with h
          · simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff]
            omega
          · rfl
      · intro l _ hl
        have hl' : l.val ≠ _ := fun h => hl (Fin.ext h)
        split_ifs with h
        · simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff, hl']
        · rfl
      · simp
    have hU : C2.simpleUp (1 + C2.Eij a b x) = if b.val = a.val + 1 then x else 0 := by
      unfold C2.simpleUp
      rw [Finset.sum_eq_single a]
      · by_cases hq : b.val = a.val + 1
        · have h : a.val + 1 < m := hq ▸ b.isLt
          rw [dif_pos h, if_pos hq]
          simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff, hq]
        · rw [if_neg hq]
          split_ifs with h
          · simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff]
            omega
          · rfl
      · intro l _ hl
        have hl' : l.val ≠ _ := fun h => hl (Fin.ext h)
        split_ifs with h
        · simp [C2.Eij, Matrix.add_apply, Matrix.one_apply, Fin.ext_iff, hl']
        · rfl
      · simp
    rw [hL, hU, hc]
    split_ifs <;> ring
end Formalism.FourierDecayAlt.P
