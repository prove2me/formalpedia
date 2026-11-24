-- Prove2me | solution 1 for CompanionTheory.Rg.Fl.hasPI_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:05:57.26619+00:00
-- url     : https://prove2.me/submissions/151bbd85-0f62-4f40-a0f9-a18a5e2313d5

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CompanionTheory.D.gk.admitted (stdPoly)
open scoped InnerProductSpace
open CompanionTheory CompanionTheory.Rg CompanionTheory.Rg.Fl
namespace CompanionTheory.Rg.Fl
theorem _root_.solution (h2 : StSimple) (h3 : StStar) (h4 : StHecke) (h5 : StMod) (h7 : StTransfer)
    {G : Type} [Group G] {K : Subgroup G} {d l : ℕ} (hp : IsHeckePair K) (hc : IsCartan K d l) (hs : IsSep K) :
    ∃ M, HasPI K M := by
  obtain ⟨C, hC⟩ := h2 d l
  refine ⟨C ^ 2 + 1, h7 G K _ hp fun b => ?_⟩
  obtain ⟨N, ρ, hρ, h0⟩ := h5 G K hp hs (stdPoly 1 b)
  exact h0 (h3 C _ (hC _ (h4 G K d l hp hc)) _ ρ hρ b)
end CompanionTheory.Rg.Fl
