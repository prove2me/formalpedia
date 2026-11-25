-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.gram_product_identity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:42:47.346346+00:00
-- url     : https://prove2.me/submissions/0dc05b01-4e22-47a1-b9e4-5f74dbc0062f

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LowerParabolicCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Theorems.Thm_Formalism_FourierDecayAlt_P_c2x3_w2core

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
theorem _root_.solution : C2.GramProductIdentity := by
  intro k r x Gv hk hx0 hxpos hG
  obtain ⟨y, hyx, hypos⟩ : ∃ y : ℕ → ℝ, (∀ i (h : i < r + 1), y i = x ⟨i, h⟩) ∧ ∀ i, 0 < y i :=
    ⟨fun i => if h : i < r + 1 then x ⟨i, h⟩ else 1, fun i h => dif_pos h,
     fun i => by dsimp only; split_ifs; exacts [hxpos _, one_pos]⟩
  have hy0 : y 0 = 1 := by
    rw [hyx 0 (Nat.succ_pos r)]
    have : (⟨0, Nat.succ_pos r⟩ : Fin (r + 1)) = 0 := Fin.ext (by simp)
    rw [this, hx0]
  have hsucc : ∀ l : Fin r, x l.succ = y (l.val + 1) := by
    intro l; rw [hyx _ (by omega)]; rfl
  have hcast : ∀ l : Fin r, x l.castSucc = y l.val := by
    intro l; rw [hyx _ (by omega)]; rfl
  have hlast : x (Fin.last r) = y r := by rw [hyx _ (Nat.lt_succ_self r)]; rfl
  have hexp : ∀ l : Fin r, 2 * (C2.Ml k r (l.val + 1) - 2) = 4 * (r - l.val) + 2 * (k - 1) := by
    intro l; unfold C2.Ml; have := l.isLt; omega
  simp only [hsucc, hcast, hexp, hlast]
  rw [Fin.prod_univ_eq_prod_range (fun l => (y (l + 1) / y l) ^ (4 * (r - l) + 2 * (k - 1))) r,
    Fin.prod_univ_eq_prod_range (fun l => y (l + 1) ^ 4) r, c2x3_w2core y hypos hy0 (2 * (k - 1)) r]
  have := (hypos r).ne'
  rw [div_pow, pow_mul]
  field_simp
end Formalism.FourierDecayAlt.P
