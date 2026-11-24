-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.existsStableLattice_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:40:59.008854+00:00
-- url     : https://prove2.me/submissions/2b39c6e4-d53d-4da3-a7d8-895752885a3e

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_ExLattice

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : ExLattice := by
  intro G _ LL _ O _ _ _ hinj
  have hli : LinearIndependent O (fun _ : Unit => (1 : LL)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    cases i
    simp only [Finset.univ_unique, Finset.sum_singleton, Algebra.smul_def, mul_one] at hg
    exact (map_eq_zero_iff _ hinj).mp (by simpa using hg)
  refine ⟨⟨Submodule.span O (Set.range fun _ : Unit => (1 : LL)), ?_, ?_, ?_, ?_⟩⟩
  · intro g x hx
    simpa using hx
  · exact Submodule.fg_span (Set.finite_range _)
  · exact Module.Free.of_basis (Module.Basis.span hli)
  · rw [eq_top_iff]
    intro x _
    have h1 : (1 : LL) ∈ (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL) :=
      Submodule.subset_span ⟨(), rfl⟩
    have h2 := Submodule.smul_mem (Submodule.span LL (Submodule.span O (Set.range fun _ : Unit => (1 : LL)) : Set LL)) x
      (Submodule.subset_span h1)
    simpa using h2
end Formalism.WeaklyAdmissibleFiltrations
