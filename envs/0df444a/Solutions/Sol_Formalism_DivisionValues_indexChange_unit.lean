-- Prove2me | solution 1 for Formalism.DivisionValues.indexChange_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:42:57.909593+00:00
-- url     : https://prove2.me/submissions/89370480-dbc2-48e9-babd-56912dd40e3a

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_ProdFormula
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Theorems.Thm_Formalism_DivisionValues_idxChange_cnt_unit
import Theorems.Thm_Formalism_DivisionValues_idxChange_lidx_congr
import Theorems.Thm_Formalism_DivisionValues_idxChange_lidx_self
import Theorems.Thm_Formalism_DivisionValues_idxChange_det_Dg
import Theorems.Thm_Formalism_DivisionValues_idxChange_act_Dg_alg
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_le_locS
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_idem
import Theorems.Thm_Formalism_HermitianLatticesTheory_locBasic_locS_mono


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
theorem _root_.solution (v : HeightOneSpectrum R) (i : Fin d) {s : R} (hs : s ∉ v.asIdeal) :
    IdxChangeP v (idxChangeDg i (algebraMap R K s)) := by
  intro e he
  rw [idxChange_act_Dg_alg, idxChange_det_Dg, idxChange_cnt_unit v hs]
  have hloc : localization₂ v.asIdeal (Submodule.span R (Set.range e)) =
      localization₂ v.asIdeal (Submodule.span R (Set.range (Function.update e i (s • e i)))) := by
    unfold localization₂
    apply le_antisymm
    · have hsub : Submodule.span R (Set.range e) ≤
          locS v.asIdeal.primeCompl (Submodule.span R (Set.range (Function.update e i (s • e i)))) := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        by_cases hk : k = i
        · subst hk
          exact ⟨s, hs, Submodule.subset_span ⟨k, by simp⟩⟩
        · exact locBasic_le_locS _ _ (Submodule.subset_span ⟨k, by simp [Function.update_of_ne hk]⟩)
      calc locS v.asIdeal.primeCompl (Submodule.span R (Set.range e))
          ≤ locS v.asIdeal.primeCompl (locS v.asIdeal.primeCompl
              (Submodule.span R (Set.range (Function.update e i (s • e i))))) :=
            locBasic_locS_mono _ hsub
        _ = _ := locBasic_locS_idem _ _
    · apply locBasic_locS_mono
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      by_cases hk : k = i
      · subst hk
        simp only [Function.update_self]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
      · rw [Function.update_of_ne hk]
        exact Submodule.subset_span ⟨k, rfl⟩
  rw [idxChange_lidx_congr v.asIdeal hloc rfl, idxChange_lidx_self]
end Formalism.DivisionValues
