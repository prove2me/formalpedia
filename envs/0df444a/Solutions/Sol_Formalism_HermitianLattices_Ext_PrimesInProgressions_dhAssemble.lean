-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhAssemble
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:02.446083+00:00
-- url     : https://prove2.me/submissions/7d95487d-2f75-4a74-b152-b3035d407d59

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHIneqB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {β : Type*} [AddCommGroup β] (F1 F2 F3 F4 : Multiset ℂ) (b2 b3 b4 : ℂ)
    (c3 c4 : Prop) [Decidable c3] [Decidable c4] (h2 : b2 ∈ F2) (h3 : c3 → b3 ∈ F3) (h4 : c4 → b4 ∈ F4)
    (g : ℂ → β) :
    ((F1 + F2.erase b2 + (if c3 then F3.erase b3 else F3) + (if c4 then F4.erase b4 else F4)).map g).sum
      = (F1.map g).sum + (F2.map g).sum + (F3.map g).sum + (F4.map g).sum - g b2
        - (if c3 then g b3 else 0) - (if c4 then g b4 else 0) := by
  classical
  have e : ∀ (F : Multiset ℂ) (b : ℂ), b ∈ F → ((F.erase b).map g).sum = (F.map g).sum - g b := by
    intro F b hb
    rw [← Multiset.sum_map_erase hb]
    abel
  simp only [Multiset.map_add, Multiset.sum_add, e _ _ h2]
  by_cases hc3 : c3 <;> by_cases hc4 : c4
  · simp only [if_pos hc3, if_pos hc4, e _ _ (h3 hc3), e _ _ (h4 hc4)]
    abel
  · simp only [if_pos hc3, if_neg hc4, e _ _ (h3 hc3)]
    abel
  · simp only [if_neg hc3, if_pos hc4, e _ _ (h4 hc4)]
    abel
  · simp only [if_neg hc3, if_neg hc4]
    abel
end Formalism.HermitianLattices.Ext.PrimesInProgressions
