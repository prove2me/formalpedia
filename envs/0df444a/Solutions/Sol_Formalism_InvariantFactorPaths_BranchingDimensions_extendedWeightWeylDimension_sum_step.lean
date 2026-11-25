-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.sum_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:05:45.896381+00:00
-- url     : https://prove2.me/submissions/98296820-7695-472e-a072-44c3ae35c541

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_finsum_prop_congr
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_pieriDual
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_frame_sum
import Theorems.Thm_Formalism_InvariantFactorPaths_BranchingDimensions_extendedWeightWeylDimension_twG_early

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
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
namespace Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
theorem _root_.solution (hP : PieriDim) (hBr : BranchDim) (D : Letters) (hW : D.Wf) (j : ℕ) (x : Fin D.k → ℤ)
    (hj : j < D.Ns) (hg : D.twGood j x) :
    ∑ᶠ (y : Fin D.k → ℤ) (_ : D.twStep (j + 1) x y), D.twG (j + 1) y = D.twG j x * D.twC (j + 1) := by
  obtain ⟨hr1, hK1, h3r, hvec1, hvec2⟩ := hW
  have hk : D.k = D.r + D.K := rfl
  have hn0 : D.n0 = D.Ns - D.r := rfl
  by_cases hn : j + 1 ≤ D.n0
  · have hc : D.twC (j + 1) = ((D.B (j + 1) + D.k - 1).choose (D.k - 1) : ℝ) := by
      unfold Letters.twC; rw [if_pos hn]
    rw [twG_early D (by omega : j ≤ D.n0), hc]
    by_cases hv : D.vec (j + 1) = true
    · rw [← hP D.k x (D.B (j + 1)) (by omega) hg.1]
      refine finsum_prop_congr (fun y => ?_) (fun y _ => twG_early D hn y)
      constructor
      · intro h; exact ⟨h.2.1 hv, h.2.2.2.1 hn hv⟩
      · rintro ⟨s, sz⟩
        refine ⟨fun m hm => le_trans (s.2 m hm) (s.1 m (by omega)), fun _ => s,
          fun hf => by rw [hv] at hf; exact absurd hf (by simp), fun _ _ => sz,
          fun _ hf => by rw [hv] at hf; exact absurd hf (by simp), fun m hm => by omega⟩
    · have hv' : D.vec (j + 1) = false := by simpa using hv
      rw [← pieriDual hP D.k x (D.B (j + 1)) (by omega) hg.1]
      refine finsum_prop_congr (fun y => ?_) (fun y _ => twG_early D hn y)
      constructor
      · intro h; exact ⟨h.2.2.1 hv', h.2.2.2.2.1 hn hv'⟩
      · rintro ⟨s, sz⟩
        refine ⟨fun m hm => le_trans (s.1 (m + 1) hm) (s.2 m hm),
          fun hf => absurd hf hv, fun _ => s,
          fun _ hf => absurd hf hv, fun _ _ => sz, fun m hm => by omega⟩
  · have hv : D.vec (j + 1) = true := hvec2 (j + 1) (by omega) (by omega)
    have hc : D.twC (j + 1) = 1 := by
      unfold Letters.twC; rw [if_neg hn]
    have e1 : j + 1 - D.n0 = (j - D.n0) + 1 := by omega
    have e2 : D.k - (j - D.n0) = D.k - ((j - D.n0) + 1) + 1 := by omega
    have h0 : extW x 0 ≤ (D.be : ℤ) := by
      have := hg.2.1
      have e3 : min j D.n0 = D.n0 := by omega
      rw [e3] at this
      exact this
    have hfr := frame_sum hBr D.k (D.k - ((j - D.n0) + 1)) (j - D.n0) (by omega) (D.be : ℤ) x hg.1 h0 hg.2.2
    rw [hc, mul_one]
    have hgx : D.twG j x = weylDim (D.k - ((j - D.n0) + 1) + 1) (fun l => extW x (l + (j - D.n0))) := by
      unfold Letters.twG; rw [← e2]
    rw [hgx, ← hfr]
    refine finsum_prop_congr (fun y => ?_) (fun y _ => ?_)
    · constructor
      · intro h
        refine ⟨h.1, h.2.1 hv, ?_⟩
        have := h.2.2.2.2.2
        rw [e1] at this
        exact this
      · rintro ⟨hd, s, hh⟩
        refine ⟨hd, fun _ => s, fun hf => by rw [hv] at hf; exact absurd hf (by simp),
          fun h => absurd h hn, fun h => absurd h hn, ?_⟩
        rw [e1]; exact hh
    · unfold Letters.twG; rw [e1]
end Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
