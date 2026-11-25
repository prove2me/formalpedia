-- Prove2me | solution 1 for CompanionTheory.D.Upq.Sm.IsSm.exists_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:54:24.532517+00:00
-- url     : https://prove2.me/submissions/60d69b76-23b4-4b0e-9dcb-7bc7015b36d1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_QuotInv
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_IntegralMemOfIsClosed
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_UniformCoefficientBounds_CoefBoundUniform
import Theorems.Thm_CompanionTheory_D_Upq_Sm_hasDerivAt_ex


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.Upq CompanionTheory.D.Upq.Sm
open PI
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {G K : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}
namespace CompanionTheory.D.Upq.Sm
namespace IsSm
theorem _root_.solution (h : RepOn G σ) {v : H} (hv : IsSm G σ v) :
    ∃ D : Mat n →L[ℝ] H, ∀ X, (∀ t, ex X t ∈ G) → ds σ X v = D X := by
  obtain ⟨U, F, hU, h1, hF, hfF⟩ := hv 1 h.one_mem
  refine ⟨fderiv ℝ F 1, fun X hX => ?_⟩
  have h0 : HasDerivAt (ex X) X 0 := by simpa [ex_zero] using hasDerivAt_ex X 0
  exact (hasDerivAt_local hX (ex_zero X) h0 hU h1 hF hfF).deriv
end IsSm
end CompanionTheory.D.Upq.Sm
