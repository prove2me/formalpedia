-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FlagSpanVanishing.wpart_uh
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:52:00.314129+00:00
-- url     : https://prove2.me/submissions/1876aabb-299c-472c-97fb-39d218540db9

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LinearChangeOfVariablesBis
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FlagSpanVanishing
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_sig_notW
import Theorems.Thm_Formalism_FourierDecayAlt_P_FlagSpanVanishing_sig_fixes_middle_block
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x6_Hpk_mul_apply
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_Hpk_eq
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_lo
import Theorems.Thm_Formalism_QuantumDeterminants_GBasic_sig_sig


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
open Formalism.FourierDecayAlt.P.FlagSpanVanishing
open C2x5 C2x7
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.FlagSpanVanishing
theorem _root_.solution (s : B.Mat k r) (hs : s ∈ B.GV k r)
    (hA : ∀ p j : Fin (2 * r + k + 1), r + k < p.val → r ≤ j.val → j.val ≤ r + k → s p j = 0) :
    wpart s ∈ UH (Hpk k r) := by
  have hU : sᴴ * Hpk k r * s = Hpk k r := hs
  show (wpart s)ᴴ * Hpk k r * wpart s = Hpk k r
  ext i j
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply]
  by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · have e := congrFun (congrFun hU i) j
      rw [Matrix.mul_assoc, Matrix.mul_apply] at e
      simp only [C2x6.Hpk_mul_apply, Matrix.conjTranspose_apply] at e
      rw [← e]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      by_cases hp : r ≤ p.val ∧ p.val ≤ r + k
      · rw [sig_fixes_middle_block p hp]
        simp only [wpart, if_pos (And.intro hp.1 (And.intro hp.2 (And.intro hi.1 hi.2))),
          if_pos (And.intro hp.1 (And.intro hp.2 (And.intro hj.1 hj.2)))]
      · have h1 : wpart s p i = 0 := by
          simp only [wpart]; rw [if_neg (fun h => hp ⟨h.1, h.2.1⟩), if_neg]
          intro e; rw [e] at hp; exact hp hi
        rw [h1, star_zero, zero_mul]
        by_cases hpr : p.val < r
        · have : r + k < (GBasic.sig k r p).val := by rw [GBasic.sig_lo _ _ _ hpr]; omega
          rw [hA _ j this hj.1 hj.2, mul_zero, mul_zero]
        · have : r + k < p.val := by omega
          rw [hA p i this hi.1 hi.2, star_zero, zero_mul]
    · rw [Finset.sum_eq_single (GBasic.sig k r j)]
      · have h1 : wpart s (GBasic.sig k r j) i = 0 := by
          simp only [wpart]
          rw [if_neg (fun h => sig_notW j hj ⟨h.1, h.2.1⟩), if_neg]
          intro e; rw [← e] at hi; exact sig_notW j hj hi
        rw [h1, star_zero, zero_mul, GBasic.Hpk_eq, if_neg]
        intro e; rw [sig_fixes_middle_block i hi] at e; rw [e] at hj; exact hj hi
      · intro p _ hp
        have : wpart s (GBasic.sig k r p) j = 0 := by
          simp only [wpart]; rw [if_neg (fun h => hj ⟨h.2.2.1, h.2.2.2⟩), if_neg]
          intro e; apply hp; rw [← e, GBasic.sig_sig]
        rw [this, mul_zero, mul_zero]
      · simp
  · rw [Finset.sum_eq_single i]
    · have h1 : wpart s i i = 1 := by
        simp only [wpart]; rw [if_neg (fun h => hi ⟨h.1, h.2.1⟩)]; simp
      have h2 : wpart s (GBasic.sig k r i) j = if GBasic.sig k r i = j then 1 else 0 := by
        simp only [wpart]; rw [if_neg (fun h => sig_notW i hi ⟨h.1, h.2.1⟩)]
      rw [h1, star_one, one_mul, h2, GBasic.Hpk_eq]
      by_cases e : GBasic.sig k r i = j
      · rw [if_pos e, if_pos e.symm, mul_one]
      · rw [if_neg e, if_neg (fun h => e h.symm), mul_zero]
    · intro p _ hp
      have : wpart s p i = 0 := by
        simp only [wpart]; rw [if_neg (fun h => hi ⟨h.2.2.1, h.2.2.2⟩), if_neg hp]
      rw [this, star_zero, zero_mul]
    · simp
end Formalism.FourierDecayAlt.P.FlagSpanVanishing
