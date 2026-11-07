-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.pderiv_comm_poly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-06T14:03:56.710767+00:00
-- url     : https://prove2.me/submissions/7fc3b67f-3047-4921-bead-b050caff3030

-- Generated from ChapterQuantumGravity3DGauge.lean — solution of BookProof.QuantumGravity3DGauge.pderiv_comm_poly
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravity3DGauge




open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution {d : ℕ} (j k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    pderiv j (pderiv k p) = pderiv k (pderiv j p) := by
  -- Second partials commute: both sides are additive, so it suffices to check
  -- constants and the one-variable multiplication step of `induction_on`.
  classical
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp only [pderiv_mul, MvPolynomial.pderiv_X, Pi.single_apply, map_add, hp]
      split_ifs with h1 h2 h2 <;> (simp; try ring)
