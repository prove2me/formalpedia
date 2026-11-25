-- Prove2me | solution 1 for Formalism.L2.SG.Pf.StabilizerIndexVolumes.ptMat_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:01:21.411186+00:00
-- url     : https://prove2.me/submissions/387e4ebe-f388-4a4e-a849-3e6e16793334

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_StabilizerIndexVolumes_PtMatIsUnit
import Theorems.Thm_Formalism_L2_SG_Pf_StabilizerIndexVolumes_antiB_det
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Matrix
namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes
variable {K : Type*} [Field K]
private theorem det_ptEntry_ne_zero_of_blocks : ∀ (bs : List (K × ℕ)), (∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) →
    ∀ (n : ℕ), (bs.map Prod.snd).sum = n →
    (Matrix.of fun (a b : Fin n) => Formalism.MainNotions.S.ptEntry bs a.val b.val).det ≠ 0 := fun
  | [], _, n, hn => by
    simp only [List.map_nil, List.sum_nil] at hn
    subst hn
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  | (t, s) :: rest, hb, n, hn => by
    simp only [List.map_cons, List.sum_cons] at hn
    subst hn
    have ht : t ≠ 0 := (hb (t, s) (List.mem_cons_self ..)).1
    have hrest : ∀ b ∈ rest, b.1 ≠ 0 ∧ 1 ≤ b.2 := fun b hb' => hb b (List.mem_cons_of_mem _ hb')
    have ih := det_ptEntry_ne_zero_of_blocks rest hrest _ rfl
    have hM : (Matrix.of fun (a b : Fin (s + (rest.map Prod.snd).sum)) =>
        Formalism.MainNotions.S.ptEntry ((t, s) :: rest) a.val b.val).submatrix finSumFinEquiv finSumFinEquiv =
        Matrix.fromBlocks (antiB t s) 0 0
          (Matrix.of fun (a b : Fin (rest.map Prod.snd).sum) => Formalism.MainNotions.S.ptEntry rest a.val b.val) := by
      ext (i | i) (j | j)
      all_goals
        have hi := i.isLt
        have hj := j.isLt
        simp only [Matrix.submatrix_apply, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          Fin.val_castAdd, Fin.val_natAdd, Matrix.of_apply, Matrix.fromBlocks_apply₁₁,
          Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
          Matrix.zero_apply, Formalism.MainNotions.S.ptEntry, antiB, Nat.add_sub_cancel_left]
        split_ifs <;> first | rfl | omega
    rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv, hM, Matrix.det_fromBlocks_zero₂₁]
    exact mul_ne_zero (antiB_det t ht s) ih
end Formalism.L2.SG.Pf.StabilizerIndexVolumes
end
end

set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.StabilizerIndexVolumes
variable {K : Type*} [Field K]
namespace Formalism.L2.SG.Pf.StabilizerIndexVolumes
theorem _root_.solution {n : ℕ} (w : Formalism.MainNotions.S.Point K n) : (Formalism.MainNotions.S.ptMat w).det ≠ 0 := by
  have h := det_ptEntry_ne_zero_of_blocks w.1 w.2.1 n w.2.2
  exact h
end Formalism.L2.SG.Pf.StabilizerIndexVolumes
