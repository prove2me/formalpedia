-- Prove2me | solution 1 for Formalism.G0.ManyOrbitsP.allBut_comap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:38.604902+00:00
-- url     : https://prove2.me/submissions/f1e086f8-af15-4f89-a1e6-edd0db1f0286

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_LengthLayers
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_WalkSharp
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits

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
open Formalism Formalism.G0
open Formalism.G0.ManyOrbitsP
variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]
namespace Formalism.G0.ManyOrbitsP
theorem _root_.solution (π : R) (M P : Submodule R X) (g E : ℕ) (h : AllButLE π M P g E) :
    AllButLE π (⊤ : Submodule R M) (P.comap M.subtype) g E := by
  classical
  obtain ⟨C, hCM, hcard, hC⟩ := h
  refine ⟨C.subtype (· ∈ M), fun _ _ => Submodule.mem_top, ?_, fun x _ => ?_⟩
  · exact (Finset.card_subtype _ _).le.trans ((Finset.card_filter_le _ _).trans hcard)
  · obtain ⟨p, hp, c, hc, hpc⟩ := Submodule.mem_sup.mp (hC x x.2)
    have hspanle : Submodule.span R (↑C : Set X) ≤ M := Submodule.span_le.mpr hCM
    have hcM : c ∈ M := hspanle hc
    have hpM : p ∈ M := by
      have e : p = π ^ E • (x : X) - c := by rw [← hpc]; abel
      rw [e]; exact M.sub_mem (M.smul_mem _ x.2) hcM
    refine Submodule.mem_sup.mpr ⟨⟨p, hpM⟩, hp, ⟨c, hcM⟩, ?_, ?_⟩
    · have hmap : Submodule.map M.subtype (Submodule.span R (↑(C.subtype (· ∈ M)) : Set M)) =
          Submodule.span R (↑C : Set X) := by
        rw [Submodule.map_span]
        congr 1
        ext y
        constructor
        · rintro ⟨z, hz, rfl⟩
          simpa using hz
        · intro hy
          exact ⟨⟨y, hCM hy⟩, by simpa using hy, rfl⟩
      rw [← hmap] at hc
      obtain ⟨y, hy, hyc⟩ := Submodule.mem_map.mp hc
      have hy' : y = ⟨c, hcM⟩ := Subtype.ext hyc
      rwa [← hy']
    · ext
      simp [hpc]
end Formalism.G0.ManyOrbitsP
