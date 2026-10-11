-- Prove2me | solution 1 for BookProof.RadialMollifier.radialBump_integrable
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:49:34.347243+00:00
-- url     : https://prove2.me/submissions/aeee0897-0c84-4fbf-8623-b425ec2ef739

-- Generated from ChapterRadialMollifier.lean — solution of BookProof.RadialMollifier.radialBump_integrable
import Mathlib
import Definitions.Def_ChapterRadialMollifier
import Theorems.Thm_BookProof_RadialMollifier_radialBump_continuous
import Theorems.Thm_BookProof_RadialMollifier_radialBump_hasCompactSupport
open BookProof.RadialMollifier




open MeasureTheory Metric Set Complex intervalIntegral Real
open scoped Convolution Topology ContDiff Real

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : Integrable radialBump := radialBump_continuous.integrable_of_hasCompactSupport radialBump_hasCompactSupport
