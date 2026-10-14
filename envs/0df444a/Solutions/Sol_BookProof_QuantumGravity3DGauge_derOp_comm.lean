-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.derOp_comm
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T13:33:09.87654+00:00
-- url     : https://prove2.me/submissions/af32ada9-4b64-40b7-900e-13ea8cced5ba

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.derOp_comm
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterYangMillsHermite
open BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

variable {d : ℕ}
open BookProof.QuantumGravity3DGauge

theorem solution(j k : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    derOp j (derOp k p) = derOp k (derOp j p) := by
  by_cases hjk : j = k
  · subst hjk
    rfl
  have hc : ∀ q : MvPolynomial (Fin d) ℂ, MvPolynomial.pderiv j (MvPolynomial.pderiv k q) = MvPolynomial.pderiv k (MvPolynomial.pderiv j q) := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p n hp =>
      simp only [MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, map_add, hp, Pi.single_apply]
      split_ifs <;> simp_all <;> ring
  simp [derOp, mulOp, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X, hc, Pi.single_apply, hjk, Ne.symm hjk, MvPolynomial.smul_eq_C_mul]
  ring
