-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.BoxAverageLimits.sdiff2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:03:52.255798+00:00
-- url     : https://prove2.me/submissions/ff4fbc3b-5fc2-4b0f-ba53-1e0319d4618c

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
    (box ι R).image (fun m => m + Pi.single j 1) \ box ι R ⊆
      Fintype.piFinset (Function.update (fun _ : ι => range R) j {R}) := by
  intro m hm
  rw [Finset.mem_sdiff, Finset.mem_image] at hm
  obtain ⟨⟨m', hm', rfl⟩, hnot⟩ := hm
  have hb := Fintype.mem_piFinset.mp hm'
  rw [Fintype.mem_piFinset]
  intro i
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self, Finset.mem_singleton, Pi.add_apply, Pi.single_eq_same]
    have h1 := hb i
    simp only [Finset.mem_range] at h1
    by_contra hne
    apply hnot
    rw [box, Fintype.mem_piFinset]
    intro k
    simp only [Finset.mem_range, Pi.add_apply]
    by_cases hk : k = i
    · subst hk; simp; omega
    · have := hb k; simp only [Finset.mem_range] at this; simp [hk, this]
  · simp only [Function.update_apply, hij, if_false, Pi.add_apply]
    simp [hij]
    simpa using hb i
end Formalism.FourierDecayAlt.P.BoxAverageLimits
