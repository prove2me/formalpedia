-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:39:27.411977+00:00
-- url     : https://prove2.me/submissions/19090cc6-1a82-475b-ada3-0ccac0fe7f5e

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
theorem _root_.solution {K : Type} [CommRing K] (L M : AddSubgroup K) (h : M.relIndex L ≠ 0) :
    ∃ S : Finset K, IsReps S L M := by
  classical
  have hfi : (M.addSubgroupOf L).FiniteIndex := ⟨h⟩
  have hfin : Finite (L ⧸ M.addSubgroupOf L) := AddSubgroup.finite_quotient_of_finiteIndex
  let _ : Fintype (L ⧸ M.addSubgroupOf L) := Fintype.ofFinite _
  refine ⟨Finset.univ.image (fun q : L ⧸ M.addSubgroupOf L => ((Quotient.out q : L) : K)), ?_, ?_⟩
  · intro a ha
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
    exact (Quotient.out q : L).2
  · intro l hl
    have key : ∀ q : L ⧸ M.addSubgroupOf L, l - ((Quotient.out q : L) : K) ∈ M ↔
        q = ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) := by
      intro q
      have e : q = ((Quotient.out q : L) : L ⧸ M.addSubgroupOf L) := (QuotientAddGroup.out_eq' q).symm
      constructor
      · intro hm
        rw [e, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
        simpa [sub_eq_add_neg, add_comm] using hm
      · intro hq
        rw [e, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at hq
        simpa [sub_eq_add_neg, add_comm] using hq
    refine ⟨((Quotient.out ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) : L) : K),
      ⟨Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, (key _).2 rfl⟩, ?_⟩
    rintro a ⟨ha, hm⟩
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ha
    rw [(key q).1 hm]
end Formalism.FourierDecayAlt.P.PositiveSemidefiniteClosure
