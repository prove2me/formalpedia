-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.localStepClosedQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:10:33.301337+00:00
-- url     : https://prove2.me/submissions/30a9b4e7-5f7c-4ea5-ac0a-7ec976b5c6a8

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_localStepLevelsQ
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_leadingTermLength
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_levelsLengthSum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.T0
open Module Formalism.LatticeBaseChangeAlt Formalism.LatticeBaseChangeAlt.BQuot
namespace Formalism.MainNotions.Gaps.T0
theorem _root_.solution : LocalStepClosedQ := by
  intro ι _ ep f ν v νs c' T R I hep hT hc' hv hν O K V W _ _ _ _ _ _ _ _ _ _ _ _ _
    ϖ hϖ M Θ N₁ Z Zm N' Mgg e n q th AA AA' N₁' ρ hM hΘ h1 h2 h3 h4 h5 h6 h8 h9
    h10 h11 h12 h13 h14 h15 h16 h17 hcase
    Rr Aq _ _ _ _ _ _ _ _ xq nq Fq rq hF0 hFn hFd hFi hFl hsum hres hequiv
    A0 _ _ n1 F1 ι1 _ _ deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind hspan hcard hI V'
  obtain ⟨eqv⟩ := hequiv
  set mmz : ι → ℕ := fun z => (max 0 ⌈(ep z : ℝ) * ((T : ℝ) * ν z - (e : ℝ))⌉).toNat with hmmz
  have hL := levelsLengthSum O ι Rr Aq xq mmz nq Fq rq R hF0 hFn hFd hFi hFl hsum
  have hA : Module.length O (↥AA' ⧸ AA.comap AA'.subtype) ≤
      ((R * ∑ z, mmz z * f z : ℕ) : ℕ∞) := by
    rw [eqv.length_eq, hL]
    refine le_of_eq ?_
    simp only [hres]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  have hN : Module.length O (↥AA ⧸ N₁'.comap AA.subtype) ≤ ((R * I : ℕ) : ℕ∞) := by
    rw [hspan, leadingTermLength O (↥AA) A0 n1 F1 ι1 deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind,
      hcard, hI]
    push_cast
    exact le_rfl
  exact localStepLevelsQ ι ep f ν v νs c' T R I hep hT hc' hv hν O K V W ϖ hϖ M Θ N₁ Z Zm N' Mgg e
    n q th AA AA' N₁' ρ hM hΘ h1 h2 h3 h4 h5 h6 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17
    hcase hA hN V'
end Formalism.MainNotions.Gaps.T0
