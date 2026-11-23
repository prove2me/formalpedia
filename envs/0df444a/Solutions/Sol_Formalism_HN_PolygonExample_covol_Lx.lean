-- Prove2me | solution 1 for Formalism.HN.PolygonExample.covol_Lx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:00:44.968973+00:00
-- url     : https://prove2.me/submissions/e79634bf-3aa4-479d-8ff1-b23533388fb2

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HNSlopes
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Example
import Theorems.Thm_Formalism_HN_PolygonExample_discrete_of_le
import Theorems.Thm_Formalism_HN_PolygonExample_vx_li
import Theorems.Thm_Formalism_HN_PolygonExample_Lx_eq
import Theorems.Thm_Formalism_F_covolEqGram


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
open Formalism.HN.PolygonExample
namespace Formalism.HN.PolygonExample
theorem _root_.solution : Formalism.F.covol Lx = 2 := by
  haveI := discrete_of_le Lx le_rfl
  let b : Basis (Fin 2) ℤ Lx := (Basis.span vx_li).map (LinearEquiv.ofEq _ _ Lx_eq.symm)
  have hb : ∀ i, (b i : E2) = vx i := fun i => by simp [b, Basis.span_apply]
  rw [Formalism.F.covolEqGram E2 Lx (Fin 2) b]
  have hg : Matrix.gram ℝ (fun i => (b i : E2)) = !![1, 0; 0, 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.gram_apply, hb, vx, e₀, e₁, inner_smul_left, inner_smul_right,
        EuclideanSpace.inner_single_left, norm_smul, EuclideanSpace.norm_single] <;> norm_num
  rw [hg, Matrix.det_fin_two_of, show (1 : ℝ) * 4 - 0 * 0 = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
end Formalism.HN.PolygonExample
