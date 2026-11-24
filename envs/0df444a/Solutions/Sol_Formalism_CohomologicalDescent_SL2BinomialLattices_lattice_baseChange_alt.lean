-- Prove2me | solution 1 for Formalism.CohomologicalDescent.SL2BinomialLattices.lattice_baseChange_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:12.349128+00:00
-- url     : https://prove2.me/submissions/673b5291-c091-42ef-89ab-20214e4733a5

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_map_baseChange_polyBC_eq_span
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_map_algebraMap_smul_alt
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_map_mem_weyl_alt
import Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_lattice_tensor
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_dualWeylMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'
namespace Formalism.CohomologicalDescent.SL2BinomialLattices
theorem _root_.solution : LatticeBaseChange := by
  intro R O _ _ _ _ _ r n hn ν t e
  obtain ⟨hW, hD⟩ := lattice_tensor R O r n hn ν
  have hD := hD inferInstance
  rw [map_baseChange_polyBC_eq_span] at hD
  constructor
  · intro h x hx
    rw [← hD] at hx
    induction hx using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f, hf, rfl⟩ := hg
      rw [← map_pow, ← map_algebraMap_smul_alt]
      exact map_mem_weyl_alt R O hn ν _ (h f hf)
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  · intro h
    set p : Submodule R (MvPolynomial (Fin r × Fin n) R) :=
      (dualWeyl R r n ν).map (LinearMap.lsmul R _ (t ^ e)) with hp
    have h1 : p.baseChange O ≤ (weyl R r n hn ν).baseChange O := by
      rw [← Submodule.map_le_map_iff_of_injective (polyBC R O r n).injective, hW,
        map_baseChange_polyBC_eq_span]
      apply Submodule.span_le.2
      rintro _ ⟨_, ⟨f, hf, rfl⟩, rfl⟩
      have h2 := h _ (dualWeylMap R O (algebraMap R O) r n ν f hf)
      rw [← map_pow, ← map_algebraMap_smul_alt] at h2
      exact h2
    have h3 : p ≤ weyl R r n hn ν := Submodule.baseChange_le_iff.1 h1
    intro x hx
    exact h3 ⟨x, hx, rfl⟩
end Formalism.CohomologicalDescent.SL2BinomialLattices
