-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RF.rowShift_minor_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:19:58.061958+00:00
-- url     : https://prove2.me/submissions/fc39644a-9a6e-415b-9753-d0092654470a

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemC
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowInvariant
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCInv
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_shift_same
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_shift_add
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
variable {T : Type} {r : T → ℕ} {n : ℕ} {C : Type} [Field C]
variable {N N' : ℕ} (Φ : MvPolynomial (Fin N × Fin N') C →ₐ[C] MvPolynomial (Letter T r n) C) (σ0 : T)
  (w : Fin N → Fin 2 → C) (lt : Fin N × Fin N' → Fin 2 → Letter T r n) (colf : Fin N → Fin 2 → Fin n)
namespace Formalism.L2.FormalSeriesBounds.RF
theorem _root_.solution (hΦ : ∀ x, Φ (X x) = ∑ q, MvPolynomial.C (w x.1 q) * X (lt x q))
    (hlt : ∀ ρ c q, keyL (lt (ρ, c) q) = (σ0, c.val, colf ρ q)) (σ : T) (i i' : Fin (r σ)) (hi : i' < i) (t : C) (k : ℕ) :
    rowShift r n C σ i i' t (Φ (minorK C N N' k)) = Φ (minorK C N N' k) := by
  unfold minorK
  split_ifs with h
  · set A : Matrix (Fin k) (Fin k) (MvPolynomial (Letter T r n) C) :=
      Matrix.of fun b c => Φ (X (Fin.castLE h.1 b, Fin.castLE h.2 c)) with hA
    have e1 : Φ (Matrix.of fun b c : Fin k =>
        (X (Fin.castLE h.1 b, Fin.castLE h.2 c) : MvPolynomial (Fin N × Fin N') C)).det = A.det := by
      rw [AlgHom.map_det]
      congr 1
    rw [e1, AlgHom.map_det]
    by_cases hc : σ = σ0 ∧ i.val < k
    · obtain ⟨rfl, hik⟩ := hc
      have hi' : i'.val < i.val := hi
      let ci : Fin k := ⟨i.val, hik⟩
      let ci' : Fin k := ⟨i'.val, lt_trans hi' hik⟩
      have hne : ci ≠ ci' := by
        intro e
        have h3 : ci.val = ci'.val := congrArg Fin.val e
        have h4 : i.val = i'.val := h3
        omega
      have e2 : (rowShift r n C σ i i' t).mapMatrix A =
          A.updateCol ci (fun b => A b ci + (MvPolynomial.C t : MvPolynomial (Letter T r n) C) • A b ci') := by
        refine Matrix.ext fun b c => ?_
        rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.updateCol_apply]
        simp only [hA, Matrix.of_apply]
        by_cases hcc : c = ci
        · subst hcc
          rw [if_pos rfl, smul_eq_mul]
          exact shift_add Φ σ w lt colf hΦ hlt i i' t _ _ _ rfl rfl
        · rw [if_neg hcc]
          refine shift_same Φ σ w lt colf hΦ hlt σ i i' t _ _ ?_
          rintro ⟨_, e⟩
          exact hcc (Fin.ext e)
      rw [e2, Matrix.det_updateCol_add_smul_self A hne]
    · have e2 : (rowShift r n C σ i i' t).mapMatrix A = A := by
        refine Matrix.ext fun b c => ?_
        rw [AlgHom.mapMatrix_apply, Matrix.map_apply]
        simp only [hA, Matrix.of_apply]
        refine shift_same Φ σ0 w lt colf hΦ hlt σ i i' t _ _ ?_
        rintro ⟨e0, e⟩
        apply hc
        refine ⟨e0, ?_⟩
        have : c.val = i.val := e
        omega
      rw [e2]
  · simp
end Formalism.L2.FormalSeriesBounds.RF
