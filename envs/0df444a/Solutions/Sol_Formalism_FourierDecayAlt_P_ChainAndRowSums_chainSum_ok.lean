-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ChainAndRowSums.chainSum_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:06:22.693802+00:00
-- url     : https://prove2.me/submissions/bbb67c59-cfb8-42ca-a6bc-0c13d82e53ce

import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainAndRowSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_cm_two
import Theorems.Thm_Formalism_FourierDecayAlt_P_ChainAndRowSums_cm_one

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChainAndRowSums
open Formalism.FourierDecayAlt.crystallineComparison
namespace Formalism.FourierDecayAlt.P.ChainAndRowSums
theorem _root_.solution : ChainSum := by
  intro W X Wd s c caa Nd N0 T hs h1 htr hfin
  have key : ∀ n, 1 ≤ n → n ≤ s - 1 → ∀ w ∈ Wd, ∀ t,
      Nd n w t ≤ ∑ w'' ∈ Wd, chainMat Wd c n w w'' * N0 w'' := by
    intro n
    induction n with
    | zero => intro h; omega
    | succ m ih =>
      intro _ hns w hw t
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simpa [cm_one] using h1 w hw t
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        have ih' := ih (by omega) (by omega)
        have h := htr (k + 1 + 1) (by omega) hns
          (fun w' => ∑ w'' ∈ Wd, chainMat Wd c (k + 1) w' w'' * N0 w'')
          (by intro w' hw' t'; simpa using ih' w' hw' t') w hw t
        calc Nd (k + 1 + 1) w t
            ≤ ∑ w' ∈ Wd, c (k + 1 + 1) w w' *
                ∑ w'' ∈ Wd, chainMat Wd c (k + 1) w' w'' * N0 w'' := h
          _ = ∑ w'' ∈ Wd, chainMat Wd c (k + 1 + 1) w w'' * N0 w'' := by
            rw [show k + 1 + 1 = k + 2 from rfl]
            simp only [cm_two, Finset.mul_sum, Finset.sum_mul]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  intro w hw
  have h := hfin (fun w' => ∑ w'' ∈ Wd, chainMat Wd c (s - 1) w' w'' * N0 w'')
    (fun w' hw' t => key (s - 1) (by omega) le_rfl w' hw' t) w hw
  calc T w ≤ ∑ w' ∈ Wd, caa w w' * ∑ w'' ∈ Wd, chainMat Wd c (s - 1) w' w'' * N0 w'' := h
    _ = ∑ w'' ∈ Wd, coMat Wd c caa s w w'' * N0 w'' := by
      simp only [coMat, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
end Formalism.FourierDecayAlt.P.ChainAndRowSums
