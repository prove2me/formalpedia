-- Prove2me | solution 1 for Formalism.UG.P.csCovol_sq_eq_det_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:38:13.455457+00:00
-- url     : https://prove2.me/submissions/268b67cf-bd94-4dbc-aa74-5a296e5166e4

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsCovol

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module NumberField Matrix
open Formalism Formalism.UG Formalism.UG.P
namespace Formalism.UG.P
theorem _root_.solution {N : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin N)))
    [DiscreteTopology L] [IsZLattice ℝ L] (b : Basis (Fin N) ℤ L) :
    ZLattice.covolume L ^ 2 =
      (Matrix.of fun i j : Fin N => inner ℝ ((b i : EuclideanSpace ℝ (Fin N))) (b j)).det := by
  classical
  let b₀ := (EuclideanSpace.basisFun (Fin N) ℝ).toBasis
  have hc := ZLattice.covolume_eq_det_mul_measureReal L MeasureTheory.volume b b₀
  have hvol : MeasureTheory.volume.real (ZSpan.fundamentalDomain b₀) = 1 := by
    rw [MeasureTheory.measureReal_def,
      MeasureTheory.measure_congr (ZSpan.fundamentalDomain_ae_parallelepiped b₀ MeasureTheory.volume)]
    rw [OrthonormalBasis.coe_toBasis, OrthonormalBasis.volume_parallelepiped]
    simp
  rw [hc, hvol, mul_one, sq_abs, Module.Basis.det_apply]
  have hG : (Matrix.of fun i j : Fin N => inner ℝ ((b i : EuclideanSpace ℝ (Fin N))) (b j)) =
      (b₀.toMatrix (Subtype.val ∘ b))ᵀ * b₀.toMatrix (Subtype.val ∘ b) := by
    ext i j
    simp [b₀, Matrix.mul_apply, Module.Basis.toMatrix_apply, PiLp.inner_apply, mul_comm]
  rw [hG, Matrix.det_mul, Matrix.det_transpose, sq]
end Formalism.UG.P
