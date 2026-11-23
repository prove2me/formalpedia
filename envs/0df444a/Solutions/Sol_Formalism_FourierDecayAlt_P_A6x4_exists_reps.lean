-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.exists_reps
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:59.828968+00:00
-- url     : https://prove2.me/submissions/5fbd7b7d-f644-4d8c-a67f-a75d94efe632

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution {L M : AddSubgroup K} (hL : IsCompact (L : Set K)) (hM : IsOpen (M : Set K)) :
    ∃ S : Finset K, IsReps S L M := by
  classical
  have : CompactSpace L := isCompact_iff_compactSpace.1 hL
  have ho : IsOpen ((M.addSubgroupOf L : AddSubgroup L) : Set L) :=
    hM.preimage continuous_subtype_val
  have : Finite (L ⧸ M.addSubgroupOf L) := AddSubgroup.quotient_finite_of_isOpen _ ho
  have : Fintype (L ⧸ M.addSubgroupOf L) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun y : L ⧸ M.addSubgroupOf L => ((Quotient.out y : L) : K), ?_, ?_⟩
  · intro a ha
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 ha
    exact (Quotient.out y : L).2
  · intro l hl
    have hrel : ∀ y : L ⧸ M.addSubgroupOf L,
        l - ((Quotient.out y : L) : K) ∈ M ↔ y = ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) := by
      intro y
      have h1 : y = ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) ↔
          ((Quotient.out y : L) : L ⧸ M.addSubgroupOf L) = ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) := by
        rw [QuotientAddGroup.out_eq']
      rw [h1, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
      have e : ((-(Quotient.out y : L) + ⟨l, hl⟩ : L) : K) = l - ((Quotient.out y : L) : K) := by
        push_cast
        ring
      rw [e]
    refine ⟨((Quotient.out ((⟨l, hl⟩ : L) : L ⧸ M.addSubgroupOf L) : L) : K),
      ⟨Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, (hrel _).2 rfl⟩, ?_⟩
    rintro a ⟨ha, hal⟩
    obtain ⟨y, _, rfl⟩ := Finset.mem_image.1 ha
    rw [(hrel y).1 hal]
end Formalism.FourierDecayAlt.P.A6x4
