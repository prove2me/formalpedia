-- Prove2me | solution 1 for CompanionTheory.RgFd.momW_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:37:03.189507+00:00
-- url     : https://prove2.me/submissions/68664b6f-cb91-4ed7-88a8-2f425ecc5075

import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomB
import Definitions.Def_CompanionTheory_RealGroups_FormalDegrees_ArchimedeanFormalDegrees_MomentRecursion_MomStep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open CompanionTheory CompanionTheory.RgFd
namespace CompanionTheory.RgFd
theorem _root_.solution : MomA → MomB → MomW := by
  intro hA hB Ω _ P h U I _ α β c t0 hh hU h01 hα hβ hc hm
  obtain ⟨ν', U', m', p', e'⟩ := hB I α β c hα hβ hc
  have e : ∀ j : ℕ, 1 ≤ j → ∫⁻ x, ENNReal.ofReal (U x ^ (j * (t0 + 1))) ∂(P.withDensity h) =
      ENNReal.ofReal (c / ∏ i, (α i + (j * (t0 + 1) : ℕ) * β i)) := fun j hj => by
    rw [lintegral_withDensity_eq_lintegral_mul _ hh (by fun_prop)]
    exact hm _ (by nlinarith)
  have r := hA Ω _ (P.withDensity h) ν' U U' (t0 + 1) hU m' h01 (fun y => ⟨(p' y).1.le, (p' y).2⟩) (by omega)
    (fun j hj => (e j hj).trans (e' _).symm) fun j hj => by rw [e j hj]; exact ENNReal.ofReal_ne_top
  rw [withDensity_apply _ (measurableSet_lt measurable_const hU)] at r
  rw [r, show {y | 0 < U' y} = univ from eq_univ_of_forall fun y => (p' y).1]
  simpa using e' 0
end CompanionTheory.RgFd
