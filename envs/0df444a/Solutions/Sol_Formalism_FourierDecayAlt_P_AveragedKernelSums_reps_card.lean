-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AveragedKernelSums.reps_card
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:01:56.785661+00:00
-- url     : https://prove2.me/submissions/ecbaa0f4-047a-4c46-b5a9-0843f5cf35f9

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelPropertiesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AveragedKernelSums
import Theorems.Thm_Formalism_FourierDecayAlt_P_AveragedKernelSums_relIndex_eq_card_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Matrix
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.AveragedKernelSums
open Formalism.FourierDecayAlt.P.A5x6
variable {K : Type} [CommRing K] {R : Subring K} {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.AveragedKernelSums
theorem _root_.solution (L M : AddSubgroup K) (S : Finset K) (h : IsReps S L M) :
    M.relIndex L = S.card := by
  rw [relIndex_eq_card_map]
  let f : S → L.map (QuotientAddGroup.mk' M) := fun a => ⟨(a : K), ⟨a, h.1 a a.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a a' haa
      have h1 : ((a : K) : K ⧸ M) = ((a' : K) : K ⧸ M) := congrArg Subtype.val haa
      have h2 := QuotientAddGroup.eq.mp h1
      obtain ⟨b, _, hb⟩ := h.2 a' (h.1 a' a'.2)
      have e1 : (a : K) = b := hb a ⟨a.2, by rwa [sub_eq_neg_add]⟩
      have e2 : (a' : K) = b := hb a' ⟨a'.2, by rw [sub_self]; exact M.zero_mem⟩
      exact Subtype.ext (e1.trans e2.symm)
    · rintro ⟨_, l, hl, rfl⟩
      obtain ⟨b, ⟨hb1, hb2⟩, _⟩ := h.2 l hl
      refine ⟨⟨b, hb1⟩, Subtype.ext ?_⟩
      show ((b : K) : K ⧸ M) = ((l : K) : K ⧸ M)
      rw [QuotientAddGroup.eq, ← sub_eq_neg_add]
      exact hb2
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]
end Formalism.FourierDecayAlt.P.AveragedKernelSums
