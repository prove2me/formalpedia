-- Prove2me | solution 1 for BookProof.QuantumGravity3DGauge.qg3DElliptic_hashimoto_selects
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T20:29:30.863981+00:00
-- url     : https://prove2.me/submissions/73dd03c5-2d0d-4812-9086-d2be10ec40a1

-- Generated from ChapterQuantumGravity3DGauge.lean — solution of BookProof.QuantumGravity3DGauge.qg3DElliptic_hashimoto_selects
import Mathlib
import Definitions.Def_ChapterQuantumGravity3DGauge
import Theorems.Thm_BookProof_QuantumGravity3DGauge_torsionOps_symmetricOn
import Theorems.Thm_BookProof_QuantumGravity3DGauge_signedOp_eq_weylOp
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterFriedrichsExtension
import Theorems.Thm_BookProof_FriedrichsExtension_weyl_hashimoto_selects_friedrichs
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterQuantumGravityDensitized
import Definitions.Def_ChapterHashimotoShiftInvert
import Definitions.Def_ChapterHermiteGalerkinFriedrichs
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterYangMillsFriedrichs
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterLeafGaps
open BookProof.QuantumGravity3DGauge




open MeasureTheory Complex MvPolynomial Filter Topology
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.YangMillsFriedrichs
open BookProof.FarisLavine BookProof.FriedrichsExtension BookProof.HermiteGalerkin
open BookProof.HashimotoShiftInvert BookProof.QuantumGravityDensitized
open BookProof.HermiteGalerkin
open BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs
open BookProof.YangMillsHermite

noncomputable section

variable {d : ℕ}
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}
variable {D : Submodule ℂ (L2d 84)}

set_option maxHeartbeats 1000000 in

theorem solution (e : ℕ ≃ (Fin 84 →₀ ℕ)) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ (L2d 84)) (A : Dom →ₗ[ℂ] L2d 84) (R : L2d 84 →L[ℂ] L2d 84),
      IsPositiveSelfAdjointExtension (qg3DEllipticHamiltonian (coreRepBasis e)) A ∧
        IsShiftInvert A γ R ∧ IsSelfAdjoint R ∧
        (∀ u : L2d 84, Filter.Tendsto (fun k : ℕ => galerkinCompression R (coreBasis e) k u)
          Filter.atTop (nhds (R u))) ∧
        (∀ (Dom' : Submodule ℂ (L2d 84)) (A' : Dom' →ₗ[ℂ] L2d 84),
          IsShiftInvert A' γ R → Dom' = Dom) := by
  -- The platform's `Thm_…_qg3DElliptic_eq_weylOp` statement is corrupted (it
  -- carries a `SymmetricOn …` type instead of the operator equality), so the
  -- equality is derived inline from the published `signedOp_eq_weylOp`.
  rw [show qg3DEllipticHamiltonian (coreRepBasis e)
        = weylOp (fun j => ((Real.sqrt (qgKappaElliptic j) : ℝ) : ℂ) • qgMom (coreRepBasis e) j)
            (torsionOps (coreRepBasis e)) from
      signedOp_eq_weylOp (fun j => by norm_num [qgKappaElliptic]) _ _]
  exact weyl_hashimoto_selects_friedrichs (coreBasis e)
    (qgMomScaled_symmetricOn (coreRepBasis e)) (torsionOps_symmetricOn (coreRepBasis e)) hγ
