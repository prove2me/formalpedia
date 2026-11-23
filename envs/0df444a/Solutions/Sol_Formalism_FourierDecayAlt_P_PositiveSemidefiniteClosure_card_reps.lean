-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.card_reps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:27.458441+00:00
-- url     : https://prove2.me/submissions/9d3dd17a-b46e-43cd-a4b1-05021bf8a264

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedVectorChoices
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply



set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
namespace Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
theorem _root_.solution {K : Type} [CommRing K] (L M : AddSubgroup K) (S : Finset K) (h : IsReps S L M) :
    S.card = M.relIndex L := by
  classical
  obtain ⟨h1, h2⟩ := h
  let f : S → L ⧸ M.addSubgroupOf L := fun a => ((⟨a.1, h1 a.1 a.2⟩ : L) : L ⧸ M.addSubgroupOf L)
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      have haa' : ((⟨a.1, h1 a.1 a.2⟩ : L) : L ⧸ M.addSubgroupOf L) =
        ((⟨a'.1, h1 a'.1 a'.2⟩ : L) : L ⧸ M.addSubgroupOf L) := haa
      rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at haa'
      have hm : a'.1 - a.1 ∈ M := by simpa [sub_eq_add_neg, add_comm] using haa'
      obtain ⟨b, _, hb⟩ := h2 a'.1 (h1 a'.1 a'.2)
      have e1 := hb a.1 ⟨a.2, hm⟩
      have e2 := hb a'.1 ⟨a'.2, by simp⟩
      exact Subtype.ext (e1.trans e2.symm)
    · intro q
      induction q using QuotientAddGroup.induction_on with
      | H l =>
        obtain ⟨a, ⟨ha, hm⟩, _⟩ := h2 l.1 l.2
        refine ⟨⟨a, ha⟩, ?_⟩
        show ((⟨a, h1 a ha⟩ : L) : L ⧸ M.addSubgroupOf L) = (l : L ⧸ M.addSubgroupOf L)
        rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        simpa [sub_eq_add_neg, add_comm] using hm
  have := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at this
  rw [this]; rfl
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
