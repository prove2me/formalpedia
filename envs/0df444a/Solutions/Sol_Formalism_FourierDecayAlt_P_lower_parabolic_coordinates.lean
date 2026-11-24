-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.lower_parabolic_coordinates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:40:59.590868+00:00
-- url     : https://prove2.me/submissions/e4de2d64-3677-4c23-84e8-6bec1923f1a3

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_isUnit_det_monomialMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x2_monomialMatrix_conj_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x2_lowOf_sub

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
open C2x2
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : C2.LPCoords := by
  intro m w d hd
  have hPu := isUnit_det_monomialMatrix w d hd
  constructor
  · ext l
    simp only [Set.mem_range, C2.LPg, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨fun a b hab => ?_, fun a => ?_⟩⟩
      · rw [c2x2_lowOf_sub, Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), add_zero]
      · rw [c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), add_zero]
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub,
          Matrix.one_apply_ne (fun e => (ne_of_lt hab) (w.injective e)), dif_neg]
        · simp
        · intro h; simp at h; exact absurd h.2 (not_lt.mpr (le_of_lt hab))
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1)]
        simp [hd a]
    · rintro ⟨hl, hc⟩
      refine ⟨fun q => l q.1.1 q.1.2, ?_⟩
      ext i j
      rw [c2x2_lowOf_sub]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))),
          hl.1 i j hij, add_zero]
      · rw [Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), hl.2, add_zero]
      · rw [Matrix.one_apply_ne (ne_of_gt hij), zero_add]
        split_ifs with h
        · rfl
        · have hlt : w.symm i < w.symm j := by
            have hne : w.symm i ≠ w.symm j := fun e => (ne_of_gt hij) (w.symm.injective e)
            rcases lt_or_gt_of_ne hne with h' | h'
            · exact h'
            · exact absurd ⟨hij, h'⟩ h
          have := hc.1 _ _ hlt
          rw [monomialMatrix_conj_apply w d hd] at this
          simp only [Equiv.apply_symm_apply] at this
          have hdi := hd (w.symm i)
          have hdj := hd (w.symm j)
          rcases mul_eq_zero.mp this with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact absurd h2 (inv_ne_zero hdi)
            · exact h2.symm
          · exact absurd h1 hdj
  · ext l
    simp only [Set.mem_range, C2.Lstg, Set.mem_setOf_eq]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨⟨fun i j hij => ?_, fun i => ?_⟩, ⟨fun a b hab => ?_, fun a => ?_⟩⟩
      · rw [c2x2_lowOf_sub, Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))), add_zero]
      · rw [c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), add_zero]
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub,
          Matrix.one_apply_ne (fun e => (ne_of_gt hab) (w.injective e)), dif_neg]
        · simp
        · intro h; simp at h; exact absurd h.2 (not_lt.mpr (le_of_lt hab))
      · rw [monomialMatrix_conj_apply w d hd, c2x2_lowOf_sub, Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1)]
        simp [hd a]
    · rintro ⟨hl, hc⟩
      refine ⟨fun q => l q.1.1 q.1.2, ?_⟩
      ext i j
      rw [c2x2_lowOf_sub]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [Matrix.one_apply_ne (ne_of_lt hij), dif_neg (fun h => absurd h.1 (not_lt.mpr (le_of_lt hij))),
          hl.1 i j hij, add_zero]
      · rw [Matrix.one_apply_eq, dif_neg (fun h => lt_irrefl _ h.1), hl.2, add_zero]
      · rw [Matrix.one_apply_ne (ne_of_gt hij), zero_add]
        split_ifs with h
        · rfl
        · have hlt : w.symm j < w.symm i := by
            have hne : w.symm i ≠ w.symm j := fun e => (ne_of_gt hij) (w.symm.injective e)
            rcases lt_or_gt_of_ne hne with h' | h'
            · exact absurd ⟨hij, h'⟩ h
            · exact h'
          have := hc.1 _ _ hlt
          rw [monomialMatrix_conj_apply w d hd] at this
          simp only [Equiv.apply_symm_apply] at this
          have hdi := hd (w.symm i)
          have hdj := hd (w.symm j)
          rcases mul_eq_zero.mp this with h1 | h1
          · rcases mul_eq_zero.mp h1 with h2 | h2
            · exact absurd h2 (inv_ne_zero hdi)
            · exact h2.symm
          · exact absurd h1 hdj
end Formalism.FourierDecayAlt.P
