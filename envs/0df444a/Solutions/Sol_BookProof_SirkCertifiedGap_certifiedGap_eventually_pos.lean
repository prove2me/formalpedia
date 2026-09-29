-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.certifiedGap_eventually_pos
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:41:50.233658+00:00
-- url     : https://prove2.me/submissions/f863319c-3035-491d-b5e8-61f3addb2a22

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certifiedGap_eventually_pos
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {thetaE thetaO deltaE deltaO : ℕ → ℝ} {lamE lamO : ℝ}
    (hE : Tendsto thetaE atTop (𝓝 lamE)) (hO : Tendsto thetaO atTop (𝓝 lamO))
    (hdE : Tendsto deltaE atTop (𝓝 0)) (hdO : Tendsto deltaO atTop (𝓝 0))
    (hmu : 0 < lamO - lamE) :
    ∃ m0 : ℕ, ∀ m ≥ m0, 0 < certifiedGap thetaE thetaO deltaE deltaO m := by
  have ht : Tendsto (certifiedGap thetaE thetaO deltaE deltaO)
      atTop (𝓝 (lamO - lamE)) := by
    change Tendsto (fun m => thetaO m - thetaE m - (deltaO m + deltaE m))
      atTop (𝓝 (lamO - lamE))
    simpa only [zero_add, sub_zero] using (hO.sub hE).sub (hdO.add hdE)
  exact Filter.eventually_atTop.mp (Filter.Tendsto.eventually_const_lt hmu ht)

#print axioms solution
