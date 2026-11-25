-- Prove2me | solution 1 for Formalism.HermiteSiegelSlopes.base_change_slope
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:01:57.357802+00:00
-- url     : https://prove2.me/submissions/483e37f0-e4e6-4247-bf2d-15d27efa7222

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
import Theorems.Thm_Formalism_HermiteSiegelSlopes_bc_prod
import Theorems.Thm_Formalism_HermiteSiegelSlopes_bc_nPl
import Theorems.Thm_Formalism_HermiteSiegelSlopes_bc_linIndep
import Theorems.Thm_Formalism_HermiteSiegelSlopes_bc_gram_det
import Theorems.Thm_Formalism_HermiteSiegelSlopes_bc_index
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeMap_mem_span_field
import Theorems.Thm_Formalism_HermiteSiegelSlopes_baseChangeLattice_fg
import Theorems.Thm_Formalism_HermiteSiegelSlopes_exists_linearIndependent_spanning
import Theorems.Thm_Formalism_HN_htGram
import Theorems.Thm_Formalism_HN_plLat


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
namespace Formalism.HermiteSiegelSlopes
theorem _root_.solution : BaseChange := by
  intro F E ι _ _ _ _ _ _ _ _ _ _ _ XF XE hXF hXE hn M hM
  change rkK (bcLat (E := E) M) = rkK M ∧
    degT (Pi.basisFun E ι) XE (bcLat (E := E) M) = degT (Pi.basisFun F ι) XF M
  obtain ⟨j, e, he, heM, hsp⟩ := exists_linearIndependent_spanning M
  have he' := bc_linIndep (E := E) e he
  set e' : Fin j → ι → E := fun a => bcMap (E := E) (e a) with he'def
  have hle : Submodule.span (𝓞 F) (Set.range e) ≤ M := by
    rw [Submodule.span_le]; rintro _ ⟨a, rfl⟩; exact heM a
  have hle' : Submodule.span (𝓞 E) (Set.range e') ≤ bcLat (E := E) M := by
    rw [Submodule.span_le]; rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span ⟨e a, heM a, rfl⟩
  have hrF : rkK M = j := by
    unfold rkK
    have : Submodule.span F (M : Set (ι → F)) = Submodule.span F (Set.range e) := by
      apply le_antisymm
      · rw [Submodule.span_le]; exact hsp
      · apply Submodule.span_mono; rintro _ ⟨a, rfl⟩; exact heM a
    rw [this, finrank_span_eq_card he, Fintype.card_fin]
  have hrE : rkK (bcLat (E := E) M) = j := by
    unfold rkK
    have : Submodule.span E (bcLat (E := E) M : Set (ι → E)) = Submodule.span E (Set.range e') := by
      apply le_antisymm
      · rw [Submodule.span_le]
        have hres : bcLat (E := E) M ≤ (Submodule.span E (Set.range e')).restrictScalars (𝓞 E) := by
          unfold bcLat
          rw [Submodule.span_le]
          rintro _ ⟨m, hm, rfl⟩
          exact baseChangeMap_mem_span_field e m (hsp hm)
        exact hres
      · apply Submodule.span_mono; rintro _ ⟨a, rfl⟩; exact hle' (Submodule.subset_span ⟨a, rfl⟩)
    rw [this, finrank_span_eq_card he', Fintype.card_fin]
  refine ⟨hrE.trans hrF.symm, ?_⟩
  obtain ⟨hF1, hF2⟩ := htGram F (ι → F) ι (Pi.basisFun F ι) XF hXF j e he
  obtain ⟨hE1, hE2⟩ := htGram E (ι → E) ι (Pi.basisFun E ι) XE hXE j e' he'
  have hF := hF2 M hM hle hrF
  have hE := hE2 (bcLat (E := E) M) (baseChangeLattice_fg M hM) hle' hrE
  have hidx := bc_index (E := E) e he M hM hle hsp
  have hpos : 0 < ht (Pi.basisFun F ι) XF (Submodule.span (𝓞 F) (Set.range e)) :=
    (plLat F (ι → F) ι (Pi.basisFun F ι) XF hXF _ (Submodule.fg_span (Set.finite_range e))).2.2
  have hposM : 0 < ht (Pi.basisFun F ι) XF M :=
    (plLat F (ι → F) ι (Pi.basisFun F ι) XF hXF _ hM).2.2
  set d := finrank F E with hd
  have hdpos : 0 < d := finrank_pos
  set iF : ℕ := (Submodule.span (𝓞 F) (Set.range e)).toAddSubgroup.relIndex M.toAddSubgroup with hiF
  have hiF0 : (iF : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hF
    exact hpos.ne hF
  have hprod : ∏ w : InfinitePlace E, (gramPl (Pi.basisFun E ι) XE w e').det.re =
      (∏ v : InfinitePlace F, (gramPl (Pi.basisFun F ι) XF v e).det.re) ^ d := by
    rw [← bc_prod (E := E) (fun v => (gramPl (Pi.basisFun F ι) XF v e).det.re)]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [bc_gram_det XF XE hn w e]
  have hht : ht (Pi.basisFun E ι) XE (bcLat (E := E) M) = ht (Pi.basisFun F ι) XF M ^ d := by
    rw [hE1, hprod, ← hF1, ← hF, hidx, mul_pow] at hE
    push_cast at hE
    exact mul_right_cancel₀ (pow_ne_zero _ hiF0) hE
  unfold degT
  rw [hht, Real.log_pow, bc_nPl (F := F) (E := E)]
  push_cast
  rw [← hd]
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  rw [show -((d : ℝ) * Real.log (ht (Pi.basisFun F ι) XF M)) = d * -Real.log (ht (Pi.basisFun F ι) XF M) by ring,
    show 2 * ((d : ℝ) * (nPl F : ℝ)) = d * (2 * (nPl F : ℝ)) by ring, mul_div_mul_left _ _ hd0]
end Formalism.HermiteSiegelSlopes
