-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TwoBlockPoint.pert_latZ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:40.734945+00:00
-- url     : https://prove2.me/submissions/ea535ad4-6908-4168-b65c-59e542facce3

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoBlockPoint
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_fib
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_gl_coe
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_left_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_m_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_mem_int
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x8_sec_right_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6
open scoped ComplexConjugate
open Formalism.FourierDecayAlt.P.A5x8 (sec_m sec_m_ext sec_gl sec_gl_coe sec_fib sec_right_eq sec_left_eq sec_mem_int toCos)
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TwoBlockPoint
variable {K : Type} [CommRing K] (R : Subring K)
namespace Formalism.FourierDecayAlt.P.TwoBlockPoint
theorem _root_.solution {N : ℕ} (Z : Matrix (Fin N) (Fin N) K) (g g' : Matrix (Fin N) (Fin N) R)
    (h1 : g * g' = 1) : latZ R (Z * g.map R.subtype) = latZ R Z := by
  unfold latZ
  have hc : ∀ w : Fin N → R, coeLin R w = fun i => ((w i : R) : K) := fun w => rfl
  have hmv : ∀ (A : Matrix (Fin N) (Fin N) R) (w : Fin N → R),
      (A.map R.subtype) *ᵥ (coeLin R w) = coeLin R (A *ᵥ w) := by
    intro A w
    rw [hc, hc]
    funext i
    exact (RingHom.map_mulVec R.subtype A w i).symm
  congr 1
  apply le_antisymm
  · intro x hx
    rw [LinearMap.mem_range] at hx ⊢
    obtain ⟨w, rfl⟩ := hx
    refine ⟨g *ᵥ w, ?_⟩
    show Z *ᵥ coeLin R (g *ᵥ w) = (Z * g.map R.subtype) *ᵥ coeLin R w
    rw [← Matrix.mulVec_mulVec, hmv]
  · intro x hx
    rw [LinearMap.mem_range] at hx ⊢
    obtain ⟨w, rfl⟩ := hx
    refine ⟨g' *ᵥ w, ?_⟩
    show (Z * g.map R.subtype) *ᵥ coeLin R (g' *ᵥ w) = Z *ᵥ coeLin R w
    rw [← Matrix.mulVec_mulVec, hmv, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
end Formalism.FourierDecayAlt.P.TwoBlockPoint
