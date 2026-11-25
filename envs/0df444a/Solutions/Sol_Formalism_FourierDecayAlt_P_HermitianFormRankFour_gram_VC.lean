-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HermitianFormRankFour.gram_VC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:48:06.99191+00:00
-- url     : https://prove2.me/submissions/a4c02467-5f58-4bdf-b4e1-95d72ff349d5

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormRankFour
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_herm_e_left
import Theorems.Thm_Formalism_FourierDecayAlt_P_HermitianFormRankFour_herm_es_left
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Finset Filter Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
namespace HermitianFormRankFour
section L2
open scoped Matrix.Norms.L2Operator
end L2
section Core
variable {N K J : Type} [Fintype N] [Fintype K] [Fintype J] [DecidableEq N] [DecidableEq K] [DecidableEq J]
variable {V : Matrix N K ℂ} {C : Matrix N J ℂ} {Vd : Matrix K N ℂ} {Cd : Matrix J N ℂ}
end Core
section Geo
variable {k r : ℕ}
private theorem hpk_symm_lemma_3 (k r : ℕ) (t u : Fin (2 * r + k + 1)) : Hpk k r u t = Hpk k r t u := by
  have := t.isLt
  have := u.isLt
  simp only [Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | omega
private theorem hpk_star_lemma_4 (k r : ℕ) (t u : Fin (2 * r + k + 1)) : star (Hpk k r t u) = Hpk k r t u := by
  simp only [Hpk]
  split_ifs <;> simp
private theorem herm_symm_lemma_5 (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply, star_sum, star_mul', star_star, hpk_star_lemma_4, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => ?_
  rw [hpk_symm_lemma_3]
  ring
private theorem wb_es_lemma_7 {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (c : Fin r) : v (esI k r c) = 0 :=
  hv _ (Or.inr (by have := c.isLt; show r + k < 2 * r + k - c.val; omega))
private theorem wb_e_lemma_8 {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (c : Fin r) : v (eI k r c) = 0 :=
  hv _ (Or.inl c.isLt)
end Geo
end HermitianFormRankFour
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
end
end

set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD
open Formalism.FourierDecayAlt.P.HermitianFormRankFour
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.HermitianFormRankFour
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {m : ℕ} {Bs : Fin m → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z] Bs) (a : Fin m) (j : JJ r) : herm (Hpk k r) (cvec k r z j) (Bs a) = 0 := by
  obtain ⟨hw, _, ho⟩ := hB
  rcases j with c | c | u <;> simp only [cvec]
  · rw [herm_e_left, wb_es_lemma_7 (hw a) c, star_zero]
  · rw [herm_es_left, wb_e_lemma_8 (hw a) c, star_zero]
  · rw [herm_symm_lemma_5, ho a z (by simp), star_zero]
end Formalism.FourierDecayAlt.P.HermitianFormRankFour
