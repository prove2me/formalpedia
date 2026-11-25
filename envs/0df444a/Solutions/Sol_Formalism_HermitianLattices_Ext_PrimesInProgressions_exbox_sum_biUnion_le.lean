-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exbox_sum_biUnion_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:49:13.309479+00:00
-- url     : https://prove2.me/submissions/fe742995-ec1b-4304-94a8-ebf67fe90d8e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplLocL
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTExplBox

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {ι : Type*} (s : Finset ι) (f : ι → Finset ℂ) (w : ℂ → ℕ) :
    ∑ x ∈ s.biUnion f, w x ≤ ∑ i ∈ s, ∑ x ∈ f i, w x := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert ha]
    have h := Finset.sum_union_inter (s₁ := f a) (s₂ := s.biUnion f) (f := w)
    omega
end Formalism.HermitianLattices.Ext.PrimesInProgressions
