-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.bc_index
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:21.312928+00:00
-- url     : https://prove2.me/submissions/ac0ebc2b-2a9b-4aeb-bdc1-9dd0ef89f01e

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeLattice_mono
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeLattice_span
import Theorems.Thm_Formalism_HermiteSiegelSlopes_relIndex_baseChange_dvd_pow
import Theorems.Thm_Formalism_HermiteSiegelSlopes_relIndex_scaled_span_eq_pow
import Theorems.Thm_Formalism_HermiteSiegelSlopes_exists_nat_mul_mem_span_finset
import Theorems.Thm_Formalism_HermiteSiegelSlopes_eq_of_dvd_of_mul_eq
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_linearIndependent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
open Formalism Formalism.HermiteSiegelSlopes
open Formalism.HN
open scoped nonZeroDivisors
open IsDedekindDomain
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution {j : ℕ} (e : Fin j → ι → F) (he : LinearIndependent F e)
    (M : Submodule (𝓞 F) (ι → F)) (hM : M.FG) (hle : Submodule.span (𝓞 F) (Set.range e) ≤ M)
    (hsp : (M : Set (ι → F)) ⊆ Submodule.span F (Set.range e)) :
    (Submodule.span (𝓞 E) (Set.range fun a => bcMap (E := E) (e a))).toAddSubgroup.relIndex
        (bcLat (E := E) M).toAddSubgroup =
      ((Submodule.span (𝓞 F) (Set.range e)).toAddSubgroup.relIndex M.toAddSubgroup) ^ finrank F E := by
  have heE := baseChangeMap_linearIndependent (E := E) e he
  obtain ⟨s, hs⟩ := hM
  obtain ⟨m, hm, hmM⟩ := exists_nat_mul_mem_span_finset e s (by
    intro x hx; exact hsp (hs ▸ Submodule.subset_span hx))
  rw [hs] at hmM
  have hmF : (m : F) ≠ 0 := Nat.cast_ne_zero.2 hm
  set L0 := Submodule.span (𝓞 F) (Set.range e) with hL0
  set L1 := Submodule.span (𝓞 F) (Set.range fun a => (m : F)⁻¹ • e a) with hL1
  have hML1 : M ≤ L1 := by
    intro x hx
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 F)).1 (hmM x hx)
    rw [hL1, Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c, ?_⟩
    have : x = (m : F)⁻¹ • (m • x) := by
      rw [← Nat.cast_smul_eq_nsmul F, smul_smul, inv_mul_cancel₀ hmF, one_smul]
    rw [this, ← hc, Finset.smul_sum]
    exact Finset.sum_congr rfl fun a _ => smul_comm _ _ _
  have hL0E : bcLat (E := E) L0 = Submodule.span (𝓞 E) (Set.range fun a => bcMap (E := E) (e a)) := by
    rw [hL0, baseChangeLattice_span, ← Set.range_comp]; rfl
  have hL1E : bcLat (E := E) L1 =
      Submodule.span (𝓞 E) (Set.range fun a => (m : E)⁻¹ • bcMap (E := E) (e a)) := by
    rw [hL1, baseChangeLattice_span, ← Set.range_comp]
    congr 2
    funext a i
    simp [bcMap]
  have hL1fg : L1.FG := Submodule.fg_span (Set.finite_range _)
  have d1 := relIndex_baseChange_dvd_pow (E := E) hle ⟨s, hs⟩
  have d2 := relIndex_baseChange_dvd_pow (E := E) hML1 hL1fg
  have tF := relIndex_scaled_span_eq_pow e he m hm
  have tE := relIndex_scaled_span_eq_pow (fun a => bcMap (E := E) (e a)) heE m hm
  rw [← hL0E, ← hL1E] at tE
  rw [← hL0, ← hL1] at tF
  rw [← AddSubgroup.relIndex_mul_relIndex _ M.toAddSubgroup _
    ((Submodule.toAddSubgroup_le _ _).2 hle) ((Submodule.toAddSubgroup_le _ _).2 hML1)] at tF
  rw [← AddSubgroup.relIndex_mul_relIndex _ (bcLat (E := E) M).toAddSubgroup _
    ((Submodule.toAddSubgroup_le _ _).2 (baseChangeLattice_mono hle))
    ((Submodule.toAddSubgroup_le _ _).2 (baseChangeLattice_mono hML1))] at tE
  rw [← hL0E]
  refine eq_of_dvd_of_mul_eq d1 d2 ?_ ?_
  · rw [tE, ← mul_pow, tF, ← pow_mul, ← Module.finrank_mul_finrank ℚ F E]
    congr 1; ring
  · rw [← mul_pow, tF]
    exact pow_ne_zero _ (pow_ne_zero _ hm)
end Formalism.HermiteSiegelSlopes
