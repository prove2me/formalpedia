-- Prove2me | solution 1 for BookProof.Qg3DGaugeEsa.qgSigned_eq_fqOp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T10:23:55.157721+00:00
-- url     : https://prove2.me/submissions/7e4fcc23-9759-4e4d-8534-a9616bee4717

-- Generated from ChapterQg3DGaugeEsa.lean — solution of BookProof.Qg3DGaugeEsa.qgSigned_eq_fqOp
import Mathlib
import Definitions.Def_ChapterQg3DGaugeEsa
import Theorems.Thm_BookProof_Qg3DGaugeEsa_torsionOps_eq
import Theorems.Thm_BookProof_Qg3DGaugeEsa_qgSignedPoly_eq_fqPoly
import Theorems.Thm_BookProof_Qg3DGaugeEsa_coreRepPoly_equiv
import Theorems.Thm_BookProof_Qg3DGaugeEsa_pgLp_qgSignedPoly
import Theorems.Thm_BookProof_NavierStokesFlow_DifferentialL2_coreOp_coe
import Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_apply
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_coe_op
import Theorems.Thm_BookProof_YangMillsHermite_CoreRep_op_apply
open BookProof.Qg3DGaugeEsa




open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.FullQuadratic
open BookProof.QuantumGravity3DGauge
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (kappa : Fin 84 → ℝ) :
    signedOp kappa (qgMom (coreRepPoly 84)) (torsionOps (coreRepPoly 84))
      = fqOp (qgFqP kappa) qgFqQ 0 0 0 := by

  refine LinearMap.ext fun x => ?_
  obtain ⟨p, rfl⟩ := (coreEquiv (d := 84)).surjective x
  have hx : ((coreRepPoly 84).equiv.symm (coreEquiv p) : MvPolynomial (Fin 84) ℂ) = p := by
    rw [← coreRepPoly_equiv p, LinearEquiv.symm_apply_apply]
  have hmom : ∀ j : Fin 84,
      ((qgMom (coreRepPoly 84) j (qgMom (coreRepPoly 84) j (coreEquiv p))
        : polyGaussCore (d := 84)) : L2d 84) = pgLp (pmom j (pmom j p)) := by
    intro j
    rw [qgMom, CoreRep.coe_op, CoreRep.op_apply, LinearEquiv.symm_apply_apply, hx]
  have htor : ∀ m : Fin 64,
      ((torsionOps (coreRepPoly 84) m (torsionOps (coreRepPoly 84) m (coreEquiv p))
        : polyGaussCore (d := 84)) : L2d 84) = pgLp (torsionP m * (torsionP m * p)) := by
    intro m
    rw [torsionOps_eq, CoreRep.coe_op, CoreRep.op_apply, LinearEquiv.symm_apply_apply, hx]
    rfl
  rw [signedOp_apply]
  simp only [hmom, htor]
  rw [fqOp, LinearMap.comp_apply, Submodule.subtype_apply, coreOp_coe,
    ← qgSignedPoly_eq_fqPoly kappa, pgLp_qgSignedPoly]
