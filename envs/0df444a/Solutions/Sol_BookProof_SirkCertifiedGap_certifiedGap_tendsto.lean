-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.certifiedGap_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:39:33.937061+00:00
-- url     : https://prove2.me/submissions/3c2c552c-958f-470d-8543-662fec8b2837

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certifiedGap_tendsto
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
    (hdE : Tendsto deltaE atTop (𝓝 0)) (hdO : Tendsto deltaO atTop (𝓝 0)) :
    Tendsto (certifiedGap thetaE thetaO deltaE deltaO) atTop (𝓝 (lamO - lamE)) := by
  change Tendsto (fun m => thetaO m - thetaE m - (deltaO m + deltaE m))
    atTop (𝓝 (lamO - lamE))
  simpa only [zero_add, sub_zero] using (hO.sub hE).sub (hdO.add hdE)

#print axioms solution
