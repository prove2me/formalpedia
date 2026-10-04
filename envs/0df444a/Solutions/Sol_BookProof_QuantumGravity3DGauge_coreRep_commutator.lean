-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.coreRep_commutator
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:04:44.31455+00:00
-- url     : https://prove2.me/submissions/9a48ab71-8daa-4e1e-8054-b2d7682dca20

-- Generated from ChapterQuantumGravity3DGauge.lean — theorem BookProof.QuantumGravity3DGauge.coreRep_commutator
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsHermite
open BookProof.HermiteProductCore
open BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

set_option autoImplicit false

universe u



open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized

noncomputable section

open BookProof.QuantumGravity3DGauge BookProof.YangMillsFriedrichs in
theorem solution {F : Type u} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
    {n m : ℕ} {kappa : Fin n → ℝ} (hk : ∀ i, 0 ≤ kappa i)
    (pi : Fin n → D →ₗ[ℂ] D) (Bf : Fin m → D →ₗ[ℂ] D) :
    signedOp kappa pi Bf
      = weylOp (fun i => ((Real.sqrt (kappa i) : ℝ) : ℂ) • pi i) Bf := by
  have h : ∀ i, (((Real.sqrt (kappa i) : ℝ) : ℂ) • pi i).comp
      (((Real.sqrt (kappa i) : ℝ) : ℂ) • pi i) = ((kappa i : ℝ) : ℂ) • (pi i).comp (pi i) := by
    intro i
    rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_smul, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hk i)]
  unfold signedOp weylOp signedOpDom weylOpDom
  simp only [h]

end
