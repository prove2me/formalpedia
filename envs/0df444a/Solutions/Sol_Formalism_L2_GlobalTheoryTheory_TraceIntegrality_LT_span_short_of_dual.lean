-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT.span_short_of_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:01:04.075375+00:00
-- url     : https://prove2.me/submissions/cd13aefe-48d1-45b8-8f08-bdbbb6b2f09c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_Transference
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TransferenceCover
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PLemTGeo
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_LT_span_short_of_cover
import Theorems.Thm_transference_covering


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open scoped InnerProductSpace
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
theorem _root_.solution {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (Λ : Submodule ℤ W) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ) (hlam : 0 < lam)
    (hd : ∀ y : W, y ≠ 0 → (∀ x ∈ Λ, ∃ n : ℤ, ⟪x, y⟫_ℝ = (n : ℝ)) → lam ≤ ‖y‖) :
    Submodule.span ℝ {l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * ((finrank ℝ W : ℝ) / 2 / lam + 1)} = ⊤ := by
  have hμ : 0 < (finrank ℝ W : ℝ) / 2 / lam + 1 := by positivity
  refine span_short_of_cover Λ _ hμ fun x ↦ ?_
  obtain ⟨l, hl, hle⟩ := transference_covering W Λ lam hlam hd x
  refine ⟨l, hl, ?_⟩
  rw [← le_div_iff₀ hlam] at hle
  have : (finrank ℝ W : ℝ) / 2 / lam = (finrank ℝ W : ℝ) / 2 / lam := rfl
  linarith
end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
