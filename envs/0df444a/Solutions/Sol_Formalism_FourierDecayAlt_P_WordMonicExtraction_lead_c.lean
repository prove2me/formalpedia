-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WordMonicExtraction.lead_c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:41.085792+00:00
-- url     : https://prove2.me/submissions/30a39417-7694-40b9-a044-2d612c6fe276

import Definitions.Def_Formalism_HermitianCurvature_LevelRecursionCondNeeded
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WordMonicExtraction
import Theorems.Thm_Formalism_FourierDecayAlt_P_WordMonicExtraction_moment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WordMonicExtraction
open Finset Polynomial Formalism.FourierDecayAlt.F7
namespace Formalism.FourierDecayAlt.P.WordMonicExtraction
theorem _root_.solution {V : Type} [AddCommGroup V] [Module ℂ V] (d : ℕ) (y : Fin (d + 1) → ℝ)
    (hy : Function.Injective y) (c : Fin (d + 1) → V) :
    c (Fin.last d) = ∑ j, ((lagCo y j : ℝ) : ℂ) • ∑ k : Fin (d + 1), ((y j : ℂ) ^ (k : ℕ)) • c k := by
  have hm : ∀ k : Fin (d + 1), (∑ j, ((lagCo y j : ℝ) : ℂ) * (y j : ℂ) ^ (k : ℕ)) =
      if (k : ℕ) = d then 1 else 0 := by
    intro k
    have h1 := moment d y hy k (Nat.lt_succ_iff.mp k.2)
    have h2 : (∑ j, ((lagCo y j : ℝ) : ℂ) * (y j : ℂ) ^ (k : ℕ)) =
        ((∑ j, lagCo y j * y j ^ (k : ℕ) : ℝ) : ℂ) := by
      push_cast
      try rfl
    rw [h2, h1]
    split_ifs <;> simp
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hm]
  rw [Finset.sum_eq_single (Fin.last d)]
  · simp
  · intro b _ hb
    have hbd : (b : ℕ) ≠ d := fun h => hb (Fin.ext (by simp [h]))
    simp [hbd]
  · intro h
    exact absurd (Finset.mem_univ _) h
end Formalism.FourierDecayAlt.P.WordMonicExtraction
