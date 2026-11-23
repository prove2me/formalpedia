-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.sdiff1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:52.033582+00:00
-- url     : https://prove2.me/submissions/1b9c3d79-fae9-4382-b169-5fb50bcca22a

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_LatticeHerglotzBound
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AverageOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Finset
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.BoxAverageLimits
open Formalism.FourierDecayAlt.crystallineComparison
variable {Λ : Type} [AddCommGroup Λ] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace Formalism.FourierDecayAlt.P.BoxAverageLimits
theorem _root_.solution (R : ℕ) (j : ι) :
    box ι R \ (box ι R).image (fun m => m + Pi.single j 1) ⊆
      Fintype.piFinset (Function.update (fun _ : ι => range R) j {0}) := by
  intro m hm
  rw [Finset.mem_sdiff] at hm
  obtain ⟨hbox, hnot⟩ := hm
  have hb := Fintype.mem_piFinset.mp hbox
  rw [Fintype.mem_piFinset]
  intro i
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self, Finset.mem_singleton]
    by_contra h0
    apply hnot
    rw [Finset.mem_image]
    refine ⟨m - Pi.single i 1, ?_, ?_⟩
    · rw [box, Fintype.mem_piFinset]
      intro k
      have := hb k
      simp only [Finset.mem_range] at this ⊢
      simp only [Pi.sub_apply]
      omega
    · funext k
      simp only [Pi.add_apply, Pi.sub_apply]
      by_cases hk : k = i
      · subst hk; simp; omega
      · simp [hk]
  · simp only [Function.update_apply, hij, if_false]
    exact hb i
end Formalism.FourierDecayAlt.P.BoxAverageLimits
