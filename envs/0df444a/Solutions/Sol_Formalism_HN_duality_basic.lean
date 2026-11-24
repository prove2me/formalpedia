-- Prove2me | solution 1 for Formalism.HN.duality_basic
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:21.479173+00:00
-- url     : https://prove2.me/submissions/d8ff967d-8809-4965-844d-908182ce4bd4

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Theorems.Thm_Formalism_HN_duality_expand
import Theorems.Thm_Formalism_HN_duality_dualZ_span
import Theorems.Thm_Formalism_HN_duality_linIndep
import Theorems.Thm_Formalism_HN_duality_exists_dual
import Theorems.Thm_Formalism_F_discreteTopology_span_range_and_covol
import Theorems.Thm_Formalism_F_linearIndependent_coe_basis
import Theorems.Thm_Formalism_F_rank_eq_finrank_span
import Theorems.Thm_P2M_Formalism_F_span_range_coe_basis__24da96608575

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module Submodule
noncomputable section
namespace Formalism.HN
section Dual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [FiniteDimensional ℝ E]
private theorem rk_span_range_eq_card_of_linearIndependent (u : ι → E) (hu : LinearIndependent ℝ u) :
    Formalism.F.rk (span ℤ (Set.range u)) = Fintype.card ι := by
  have := (Formalism.F.discreteTopology_span_range_and_covol u hu).1
  rw [Formalism.F.rank_eq_finrank_span (span ℤ (Set.range u)), Submodule.span_span_of_tower,
    finrank_span_eq_card hu]
end Dual
universe u
end Formalism.HN
end
end

set_option autoImplicit false
open Module Submodule
noncomputable section
open Formalism Formalism.HN
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable [FiniteDimensional ℝ E]
namespace Formalism.HN
theorem _root_.solution (L : Submodule ℤ E) [DiscreteTopology L] :
    DiscreteTopology (dualZ L) ∧ Formalism.F.rk (dualZ L) = Formalism.F.rk L ∧
    Formalism.F.deg (dualZ L) = - Formalism.F.deg L ∧ dualZ (dualZ L) = L := by
  obtain ⟨v, hv, hL⟩ : ∃ v : Fin (Module.finrank ℤ L) → E,
      LinearIndependent ℝ v ∧ span ℤ (Set.range v) = L :=
    ⟨fun i => ((Module.finBasis ℤ L i : L) : E),
      Formalism.F.linearIndependent_coe_basis L (Module.finBasis ℤ L),
      Formalism.F.span_range_coe_basis' L (Module.finBasis ℤ L)⟩
  obtain ⟨w, hw, hvw, hdet⟩ := duality_exists_dual v hv
  have hwli := duality_linIndep v w hvw
  have hdual : dualZ L = span ℤ (Set.range w) := by
    rw [← duality_dualZ_span v w hw hvw, hL]
  have hwv : ∀ k i, inner ℝ (w k) (v i) = if k = i then 1 else 0 := by
    intro k i
    rw [real_inner_comm, hvw]
    by_cases h : k = i
    · subst h
      simp
    · rw [if_neg (Ne.symm h), if_neg h]
  have hv' : ∀ i, v i ∈ span ℝ (Set.range w) := by
    intro i
    rw [duality_expand v w hw hvw (Submodule.subset_span (Set.mem_range_self i))]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self k))
  have hrkL := rk_span_range_eq_card_of_linearIndependent v hv
  rw [hL] at hrkL
  have hcv := (Formalism.F.discreteTopology_span_range_and_covol v hv).2
  rw [hL] at hcv
  have hcw := Formalism.F.discreteTopology_span_range_and_covol w hwli
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdual]
    exact hcw.1
  · rw [hdual, rk_span_range_eq_card_of_linearIndependent w hwli, hrkL]
  · rw [hdual]
    unfold Formalism.F.deg
    rw [hcw.2, hcv, hdet, Real.sqrt_inv, Real.log_inv]
  · rw [hdual, duality_dualZ_span w v hv' hwv, hL]
end Formalism.HN
