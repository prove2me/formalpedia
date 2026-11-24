-- Prove2me | solution 1 for Formalism.REAL.generator_commutator_quantumDet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:46:37.497778+00:00
-- url     : https://prove2.me/submissions/a82b2663-5e27-4ae8-9dd1-07e4fe17bf65

import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Theorems.Thm_Formalism_REAL_prod_ofFn_update_sub
import Theorems.Thm_Formalism_REAL_prod_ofFn_update_ite
import Theorems.Thm_Formalism_REAL_commutator_prod_ofFn_eq_sum_update
import Theorems.Thm_Formalism_REAL_shiftedGenerator_commutator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : GlRel E) (u : ℂ) (c d : Fin n) :
    E c d * qdet E u - qdet E u * E c d =
      qminor E (Function.update id d c) id u - qminor E id (Function.update id c d) u := by
  have hs : ∀ (z : ℤ) (X P : A), X * ((z : A) * P) - (z : A) * P * X = (z : A) * (X * P - P * X) := by
    intro z X P
    simp only [mul_sub, ← mul_assoc, (Int.cast_commute z X).eq]
  unfold qdet qminor
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [hs, ← mul_sub]
  congr 1
  rw [commutator_prod_ofFn_eq_sum_update]
  simp only [shiftedGenerator_commutator E hE, prod_ofFn_update_sub, prod_ofFn_update_ite,
    Finset.sum_sub_distrib, id_eq]
  congr 1
  · rw [Finset.sum_eq_single (σ.symm d)]
    · rw [if_pos (σ.apply_symm_apply d).symm]
      congr 1
      congr 1
      funext k
      rw [Function.update_apply, Function.update_apply]
      by_cases hk : k = σ.symm d
      · rw [if_pos hk, if_pos (show σ k = d by rw [hk, Equiv.apply_symm_apply])]
        subst hk
        rfl
      · rw [if_neg hk, if_neg (show ¬ σ k = d from fun h => hk (by rw [← h, Equiv.symm_apply_apply]))]
        try rfl
    · intro b _ hb
      rw [if_neg (show ¬ d = σ b from fun h => hb (by rw [h, Equiv.symm_apply_apply]))]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    congr 1
    funext k
    rw [Function.update_apply, Function.update_apply]
    by_cases hk : k = c
    · rw [if_pos hk, if_pos hk]
      subst hk
      rfl
    · rw [if_neg hk, if_neg hk]
      try rfl
end Formalism.REAL
