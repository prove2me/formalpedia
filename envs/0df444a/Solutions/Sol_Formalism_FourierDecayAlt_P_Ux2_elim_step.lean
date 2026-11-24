-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Ux2.elim_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:15:46.535594+00:00
-- url     : https://prove2.me/submissions/ed01c7ab-a3df-49e1-a4bb-7297301c85ac

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kL_lt
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_kL_inj
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_uniK_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_uniK_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_uniK_one_add

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p : ℕ}
namespace Formalism.FourierDecayAlt.P.Ux2
theorem _root_.solution {κ : Fin p → ℤ} (hκ : Function.Injective κ) (m : Matrix (Fin p) (Fin p) ℂ) (hm : uniK κ m) :
    ∀ n : ℕ, ∃ L M : Matrix (Fin p) (Fin p) ℂ, uniK κ L ∧ uniK (kL p) L ∧ uniK κ M ∧
      (∀ a b : Fin p, b.val < n → b < a → M a b = 0) ∧ m = L * M := by
  intro n
  induction n with
  | zero => exact ⟨1, m, uniK_one κ, uniK_one _, hm, fun a b h => absurd h (Nat.not_lt_zero _), by rw [Matrix.one_mul]⟩
  | succ n ih =>
    obtain ⟨L, M, hLk, hLl, hMk, hMz, hm'⟩ := ih
    by_cases hn : n < p
    · let c : Fin p := ⟨n, hn⟩
      let Nm : Matrix (Fin p) (Fin p) ℂ := Matrix.of fun a b => if b = c ∧ c < a then M a c else 0
      have hNN : Nm * Nm = 0 := by
        ext a b
        rw [Matrix.mul_apply]
        refine Finset.sum_eq_zero fun e _ => ?_
        by_cases he : e = c
        · subst he; simp [Nm]
        · simp [Nm, he]
      have hEF : (1 + Nm) * (1 - Nm) = 1 := by
        rw [add_mul, mul_sub, mul_sub, hNN]; simp
      have hNd : ∀ a, Nm a a = 0 := fun a => by
        simp only [Nm, Matrix.of_apply]
        split_ifs with h
        · exact absurd (h.1 ▸ h.2) (lt_irrefl _)
        · rfl
      have hNk : ∀ a b, κ a < κ b → Nm a b = 0 := by
        intro a b hab
        simp only [Nm, Matrix.of_apply]
        split_ifs with h
        · rw [← h.1]; exact hMk.2 a b hab
        · rfl
      have hNl : ∀ a b, kL p a < kL p b → Nm a b = 0 := by
        intro a b hab
        rw [kL_lt] at hab
        simp only [Nm, Matrix.of_apply]
        split_ifs with h
        · exact absurd (h.1 ▸ h.2) (not_lt.mpr hab.le)
        · rfl
      have hNM : ∀ a b, (Nm * M) a b = (if c < a then M a c else 0) * M c b := by
        intro a b
        rw [Matrix.mul_apply, Finset.sum_eq_single c]
        · simp [Nm]
        · intro e _ he; simp [Nm, he]
        · simp
      refine ⟨L * (1 + Nm), (1 - Nm) * M, uniK_mul hκ hLk (uniK_one_add hNd hNk).1,
        uniK_mul kL_inj hLl (uniK_one_add hNd hNl).1, uniK_mul hκ (uniK_one_add hNd hNk).2 hMk, ?_, ?_⟩
      · intro a b hb hba
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_apply, hNM]
        rcases Nat.lt_or_ge b.val n with h | h
        · have hcb : b < c := Fin.lt_def.mpr h
          rw [hMz a b h hba, hMz c b h hcb]; simp
        · have hbc : b = c := Fin.ext (by simp [c]; omega)
          rw [hbc] at hba ⊢
          rw [if_pos hba, hMk.1 c]; ring
      · rw [hm', Matrix.mul_assoc L, ← Matrix.mul_assoc (1 + Nm), hEF, Matrix.one_mul]
    · exact ⟨L, M, hLk, hLl, hMk, fun a b hb hba => hMz a b (by have := b.isLt; omega) hba, hm'⟩
end Formalism.FourierDecayAlt.P.Ux2
