-- Prove2me | solution 1 for Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas.frameMat_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:34:46.449954+00:00
-- url     : https://prove2.me/submissions/4e827c6e-2d6f-4416-9db2-d2fe4341836c

import Mathlib
import Definitions.Def_Formalism_MeanHeightDescent_MuMaxMinkowski
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.ExtensionFiltration
open Formalism.HN
open Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (e : V →ₗ[K] V) (v : InfinitePlace K) (hee : e ∘ₗ e = e) :
    ((X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v) *
      ((X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v) =
      (X v)⁻¹ * (LinearMap.toMatrix b b e).map v.embedding * X v := by
  set M := (LinearMap.toMatrix b b e).map v.embedding with hMdef
  have hM : M * M = M := by
    rw [hMdef, ← Matrix.map_mul, ← LinearMap.toMatrix_comp, hee]
  have hXinv : X v * (X v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (hX v)
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (X v) (X v)⁻¹, hXinv, Matrix.one_mul, ← Matrix.mul_assoc M M, hM]
end Formalism.ExtensionFiltration.HermitianIdempotentFrameLemmas
