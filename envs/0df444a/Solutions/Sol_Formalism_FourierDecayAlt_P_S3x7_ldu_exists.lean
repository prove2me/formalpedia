-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.S3x7.ldu_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:29:21.199272+00:00
-- url     : https://prove2.me/submissions/3fa2621f-4185-403a-a087-bcaeba2ee63f

import Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LduDecompositionExists
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_cl
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_lc
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ll
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_eta
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_diagonal
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_low
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_up
import Theorems.Thm_Formalism_FourierDecayAlt_P_S3x7_border_ldu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_cl
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_lc
attribute [local simp] Formalism.FourierDecayAlt.P.S3x7.border_ll

set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.S3x7
open Matrix Finset
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni isUpUni_mul isLowUni_mul isUpUni_inv isLowUni_inv isUpUni_one isLowUni_one
  isUpUni_det isLowUni_det)
open Formalism.FourierDecayAlt.S3
variable {A : Type} [CommRing A]
namespace Formalism.FourierDecayAlt.P.S3x7
theorem _root_.solution : ∀ (r : ℕ) (M : Matrix (Fin r) (Fin r) A),
    (∀ (l : ℕ) (hl : l < r), IsUnit (lead M l hl.le)) →
    ∃ (L U : Matrix (Fin r) (Fin r) A) (d : Fin r → A), IsLowUni L ∧ IsUpUni U ∧
      M = L * Matrix.diagonal d * U := by
  intro r
  induction r with
  | zero =>
    intro M _
    exact ⟨1, 1, fun i => i.elim0, isLowUni_one A, isUpUni_one A, by ext i; exact i.elim0⟩
  | succ r ih =>
    intro M hM
    have hlead : ∀ (l : ℕ) (hl : l ≤ r), lead (M.submatrix Fin.castSucc Fin.castSucc) l hl =
        lead M l (hl.trans (Nat.le_succ r)) := by
      intro l hl; rfl
    obtain ⟨L₀, U₀, d₀, hL₀, hU₀, e₀⟩ := ih (M.submatrix Fin.castSucc Fin.castSucc)
      (fun l hl => by rw [hlead]; exact hM l (by omega))
    have uB : IsUnit (M.submatrix Fin.castSucc Fin.castSucc).det := hM r (Nat.lt_succ_self r)
    have key := border_ldu _ L₀ (Matrix.diagonal d₀) U₀ (fun i => M i.castSucc (Fin.last r))
      (fun j => M (Fin.last r) j.castSucc) (M (Fin.last r) (Fin.last r)) uB e₀
    rw [← border_eta M, ← border_diagonal] at key
    exact ⟨_, _, _, border_low hL₀ _, border_up hU₀ _, key⟩
end Formalism.FourierDecayAlt.P.S3x7
