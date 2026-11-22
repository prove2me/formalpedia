-- Prove2me | solution 1 for Formalism.FN.SuccessiveMinima.mem_smul_iff_gauge
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T17:01:18.674821+00:00
-- url     : https://prove2.me/submissions/047230a9-e486-46e7-8fc0-e8e4b3eefec5

import Definitions.Def_Formalism_SuccessiveMinima_DefsMink
import Definitions.Def_Formalism_SuccessiveMinima_SuccessiveMinimaProofs_SuccMin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Module Metric Set
open scoped Pointwise
noncomputable section
open Formalism Formalism.FN Formalism.FN.SuccessiveMinima
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
namespace Formalism.FN.SuccessiveMinima
theorem _root_.solution {K : Set E} (hKc : IsCompact K) (hKv : Convex ℝ K)
    (hK0 : (0 : E) ∈ interior K) {t : ℝ} (ht : 0 ≤ t) (u : E) :
    u ∈ t • K ↔ gauge K u ≤ t := by
  have hK : K ∈ nhds (0 : E) := mem_interior_iff_mem_nhds.mp hK0
  have hKabs : Absorbent ℝ K := absorbent_nhds_zero hK
  rcases ht.eq_or_lt with rfl | htpos
  ·
    have hne : K.Nonempty := ⟨0, interior_subset hK0⟩
    rw [Set.zero_smul_set hne, Set.mem_zero]
    constructor
    · rintro rfl
      simp
    · intro hg
      by_contra hu
      have := (gauge_pos hKabs ((NormedSpace.isVonNBounded_iff ℝ).mpr hKc.isBounded)).mpr hu
      linarith
  · have h1 : t⁻¹ • u ∈ K ↔ gauge K (t⁻¹ • u) ≤ 1 := by
      rw [gauge_le_one_iff_mem_closure hKv hK, hKc.isClosed.closure_eq]
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ htpos.ne', h1,
      gauge_smul_of_nonneg (inv_nonneg.mpr htpos.le), smul_eq_mul, inv_mul_le_iff₀ htpos, mul_one]
end Formalism.FN.SuccessiveMinima
