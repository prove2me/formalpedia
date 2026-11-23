-- Prove2me | solution 1 for Formalism.DivisionValues.indexChangeLocal_transvection
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:51.289952+00:00
-- url     : https://prove2.me/submissions/1b29bf0e-9a12-43f3-8511-9936b78e65f5

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_one
import Theorems.Thm_Formalism_DivisionValues_idxChange_lidx_self
import Theorems.Thm_Formalism_DivisionValues_indexChangeAction_transvection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module IsDedekindDomain Formalism.HermitianLatticesTheory
open scoped Matrix nonZeroDivisors
noncomputable section
open Formalism Formalism.DivisionValues
variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] {d : ℕ}
namespace Formalism.DivisionValues
theorem _root_.solution (v : HeightOneSpectrum R) {i j : Fin d} (hij : i ≠ j) :
    IdxChangeP v (Matrix.transvection i j (1 : K)) := by
  intro e he
  rw [Matrix.det_transvection_of_ne i j hij, idxChange_cnt_one, indexChangeAction_transvection e hij]
  have hspan : Submodule.span R (Set.range (Function.update e j (e j + e i))) =
      Submodule.span R (Set.range e) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = j
      · subst hk
        simp only [Function.update_self]
        exact Submodule.add_mem _ (Submodule.subset_span ⟨k, rfl⟩)
          (Submodule.subset_span ⟨i, rfl⟩)
      · rw [Function.update_of_ne hk]; exact Submodule.subset_span ⟨k, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = j
      · subst hk
        have h1 : Function.update e k (e k + e i) k ∈
            Submodule.span R (Set.range (Function.update e k (e k + e i))) :=
          Submodule.subset_span ⟨k, rfl⟩
        have h2 : Function.update e k (e k + e i) i ∈
            Submodule.span R (Set.range (Function.update e k (e k + e i))) :=
          Submodule.subset_span ⟨i, rfl⟩
        rw [Function.update_self] at h1
        rw [Function.update_of_ne hij] at h2
        have := Submodule.sub_mem _ h1 h2
        simpa using this
      · have h1 : Function.update e j (e j + e i) k ∈
            Submodule.span R (Set.range (Function.update e j (e j + e i))) :=
          Submodule.subset_span ⟨k, rfl⟩
        rwa [Function.update_of_ne hk] at h1
  rw [hspan, idxChange_lidx_self]
end Formalism.DivisionValues
