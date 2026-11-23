-- Prove2me | solution 1 for CompanionTheory.D.gk.admitted.FinOfPIAux.schur
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:01:47.913809+00:00
-- url     : https://prove2.me/submissions/95d48180-73bd-4e97-9632-28f1c5ded593

import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_MapStdPoly
import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_FinOfPI
import Theorems.Thm_CompanionTheory_D_gk_admitted_FinOfPIAux_mem_unitary
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_IsIrreducible_exists_eq_smul_one
import Theorems.Thm_CompanionTheory_LimBd_URep_UnitaryRep_mem_unitary


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.gk CompanionTheory.D.gk.admitted
open CompanionTheory.D.gk.admitted.FinOfPIAux
variable {G : Type} [Group G] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
namespace CompanionTheory.D.gk.admitted.FinOfPIAux
theorem _root_.solution (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g v, ‖σ g v‖ = ‖v‖)
    (hirr : ∀ S : Submodule ℂ H, IsClosed (S : Set H) → (∀ g, ∀ v ∈ S, σ g v ∈ S) → S = ⊥ ∨ S = ⊤)
    (T : H →L[ℂ] H) (hT : ∀ g v, T (σ g v) = σ g (T v)) : ∃ c : ℂ, ∀ v, T v = c • v := by
  rcases subsingleton_or_nontrivial H with h | h
  · exact ⟨0, fun v => Subsingleton.elim _ _⟩
  let _ : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  let π : CompanionTheory.LimBd.URep.UnitaryRep G H :=
    { toHom := σ.codRestrict (unitary (H →L[ℂ] H)) (mem_unitary σ hσ)
      continuous_orbit' := fun v => continuous_of_discreteTopology }
  have hπ : π.IsIrreducible := ⟨h, fun S hS hinv => hirr S hS fun g v hv => hinv g v hv⟩
  obtain ⟨c, hc⟩ := hπ.exists_eq_smul_one (T := T) (fun g v => hT g v)
  exact ⟨c, fun v => by rw [hc]; rfl⟩
end CompanionTheory.D.gk.admitted.FinOfPIAux
