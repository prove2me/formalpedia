-- Prove2me | solution 1 for Formalism.MainNotions.Gaps.T0.localStepClosedQDescUp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:26:45.546261+00:00
-- url     : https://prove2.me/submissions/241b8416-ef19-474b-8127-92b22587d433

import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepClosed
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LocalStepDescent
import Definitions.Def_Formalism_SharpRestriction_GenusPolyhedralBounds_RelativeIndexClassSets_LengthLeOfSemilinear
import Theorems.Thm_Formalism_MainNotions_Gaps_T0_localStepClosedQ
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_isLattice_span_image_alt
import Theorems.Thm_Formalism_LatticeBaseChangeAlt_localStepDescent


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
theorem _root_.solution : LocalStepClosedQDescUp := by
  intro ι _ ep f ν v νs c' T R I hep hT hc' hv hν O O' K K' V V₁ W
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j hj ϖ hϖ hϖ'
    M Θ N₁ Z Zm N' Mgg e n q th AA AA' N₁' ρ hM hΘ h1 h2 h3 h4 h5 h6 h8 h9
    h10 h11 h12 h13 h14 h15 h16 h17 hcase
    Rr Aq _ _ _ _ _ _ _ _ xq nq Fq rq hF0 hFn hFd hFi hFl hsum hres hequiv
    A0 _ _ n1 F1 ι1 _ _ deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind hspan hcard hI V'
  have : FiniteDimensional K' V₁ := Module.Finite.equiv hj.equiv
  have h := localStepClosedQ ι ep f ν v νs c' T R I hep hT hc' hv hν O' K' V₁ W (algebraMap O O' ϖ) hϖ'
    (Submodule.span O' (j '' (M : Set V))) (Submodule.span O' (j '' (Θ : Set V))) N₁ Z Zm N' Mgg e n q
    th AA AA' N₁' ρ (isLattice_span_image_alt O O' K K' V V₁ j hj M hM)
    (isLattice_span_image_alt O O' K K' V V₁ j hj Θ hΘ) h1 h2 h3 h4 h5 h6 h8 h9
    h10 h11 h12 h13 h14 h15 h16 h17 hcase
    Rr Aq xq nq Fq rq hF0 hFn hFd hFi hFl hsum hres hequiv
    A0 n1 F1 ι1 deg δ t σ u hG0 hGn hGd hker hsurj hdeg hlead hind hspan hcard hI
    (Submodule.span K' (j '' (V' : Set V)))
  have hd := localStepDescent O O' K K' V V₁ j hj ϖ hϖ hϖ' M Θ V' hM hΘ 1
    ((R : ℝ) * ((T : ℝ) * c' * ∑ z, ((ep z : ℝ) * f z) * v z) + (R : ℝ) * (I : ℝ) +
      ((Module.length O' (↥Zm ⧸ Z.comap Zm.subtype)).toNat : ℝ) + (q : ℝ)) 0 e (by linarith)
  linarith
end Formalism.MainNotions.Gaps.T0
