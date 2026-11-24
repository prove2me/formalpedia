-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.C2x4.chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:19:09.061112+00:00
-- url     : https://prove2.me/submissions/04b28cf6-dbea-4e04-92c6-17a4ad8d1e93

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerFourthCondition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RelevantMonotoneOfParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_blk_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_C2x4_desc_in_block

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
open Formalism.FourierDecayAlt.P.C2x4
variable {m : ℕ}
namespace Formalism.FourierDecayAlt.P.C2x4
theorem _root_.solution (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (hC : Cond w d) (a : Fin m) :
    ∀ n : ℕ, ∀ b : Fin m, b.val = a.val + n + 1 → blk w a = blk w b → w b < w a ∧ d a = d b := by
  intro n
  induction n with
  | zero =>
    intro b hb hab
    obtain ⟨h, hd⟩ := desc_in_block w d hC a b hab a le_rfl (by omega)
    have hbe : b = ⟨a.val + 1, h⟩ := Fin.ext (by simp only; omega)
    subst hbe
    refine ⟨hd, ?_⟩
    exact (hC a _ (by rw [Fin.lt_def]; simp) hd).2 rfl
  | succ n ih =>
    intro b hb hab
    set j : Fin m := ⟨a.val + n + 1, by omega⟩ with hj
    have hmono := blk_mono w
    have haj : blk w a = blk w j := by
      apply le_antisymm (hmono (by rw [Fin.le_def]; simp only [hj]; omega))
      rw [hab]; exact hmono (by rw [Fin.le_def]; simp only [hj]; omega)
    obtain ⟨h1, h2⟩ := ih j rfl haj
    obtain ⟨h, hd⟩ := desc_in_block w d hC a b hab j (by rw [Fin.le_def]; simp only [hj]; omega)
      (by simp only [hj]; omega)
    have hbe : b = ⟨j.val + 1, h⟩ := Fin.ext (by simp only [hj]; omega)
    rw [hbe] at hab ⊢
    refine ⟨lt_trans hd h1, ?_⟩
    rw [h2]
    exact (hC j _ (by rw [Fin.lt_def]; simp) hd).2 rfl
end Formalism.FourierDecayAlt.P.C2x4
