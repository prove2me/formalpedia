-- Prove2me | solution 1 for Formalism.L2.LamCM.A2.detSub_free
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:24:36.268808+00:00
-- url     : https://prove2.me/submissions/b27316ae-6714-42b7-b40d-ed82a2f2613b

import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_StatementA
import Definitions.Def_Formalism_LocalToGlobal_CMDeterminantIdeals_CMIdealValuations_ProdMulLeDetIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.LamCM
open NumberField IsDedekindDomain
open scoped nonZeroDivisors ComplexOrder
open Formalism.L2.LamCM.A2
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.L2.LamCM.A2
theorem _root_.solution {m : ℕ} (L : MLat K m) (b : Fin m → Fin m → K)
    (hb : L.M = Submodule.span (𝓞 K) (Set.range b)) :
    L.detSub = Submodule.span (𝓞 K) {(Matrix.of b).det} := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro d ⟨x, hx, rfl⟩
    have : ∀ i, ∃ c : Fin m → 𝓞 K, ∑ j, c j • b j = x i := fun i => by
      have := hx i
      rw [hb] at this
      exact (Submodule.mem_span_range_iff_exists_fun _).1 this
    choose c hc using this
    have hx' : Matrix.of x = (Matrix.of c).map (algebraMap (𝓞 K) K) * Matrix.of b := by
      ext i j
      simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply]
      rw [← hc i]
      simp [Finset.sum_apply, Algebra.smul_def]
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨(Matrix.of c).det, ?_⟩
    rw [Algebra.smul_def, RingHom.map_det, hx', Matrix.det_mul]
    rfl
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    refine Submodule.subset_span ⟨b, fun i => ?_, rfl⟩
    rw [hb]
    exact Submodule.subset_span ⟨i, rfl⟩
end Formalism.L2.LamCM.A2
