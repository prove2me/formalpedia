-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.ccr_poly
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T20:29:38.644717+00:00
-- url     : https://prove2.me/submissions/14612075-961c-434e-a9aa-7bd5c8f56944

-- Generated from ChapterQuantumGravity3DGauge.lean — solution of BookProof.QuantumGravity3DGauge.ccr_poly
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Theorems.Thm_BookProof_YangMillsHermite_commutator_coord_mom
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterF7
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterLeafGaps
open BookProof.QuantumGravity3DGauge

open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {d : ℕ}

-- `mulOp_apply`/`momOp_apply` live in BookProof.YangMillsHermite but that chapter's
-- published bundle does not carry them (leaf selection); local `rfl` copies.
theorem mulOp_apply' (f p : MvPolynomial (Fin d) ℂ) : mulOp f p = f * p := rfl

theorem momOp_apply' (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j p = (-Complex.I) • (pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p)) := rfl

set_option maxHeartbeats 1000000 in
theorem solution (j k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulOp (X j) (momOp k p) - momOp k (mulOp (X j) p) = (if j = k then Complex.I else 0) • p := by
  by_cases h : j = k
  · subst h
    simpa using commutator_coord_mom j p
  · have hX : (pderiv k) (X j * p) = X j * pderiv k p := by
      rw [Derivation.leibniz]
      simp [MvPolynomial.pderiv_X, Ne.symm h]
    simp only [mulOp_apply', momOp_apply', hX, if_neg h, zero_smul, neg_smul, smul_eq_C_mul]
    ring

end
