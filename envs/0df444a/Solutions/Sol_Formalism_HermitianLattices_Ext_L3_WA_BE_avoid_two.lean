-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.WA.BE.avoid_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:16.683596+00:00
-- url     : https://prove2.me/submissions/ef26865e-db1b-4e04-bdda-c66deaf2a2c0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AlgebraMapNeZeroOfMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsHermSemilocalLocRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.WA
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.HermitianLattices.Ext.L3.WA.BE
namespace Formalism.HermitianLattices.Ext.L3.WA.BE
theorem _root_.solution {R : Type*} [CommRing R] {P Q : Ideal R} (hQ : Q.IsPrime) {a s m : R} (k : R)
    (ha : a ∈ P) (hsP : s ∉ P) (hsQ : s ∉ Q) (hm : m ∉ Q) :
    (s - k * a ∉ P ∧ s - k * a ∉ Q) ∨ (s - (k + m) * a ∉ P ∧ s - (k + m) * a ∉ Q) := by
  have hP : ∀ c : R, s - c * a ∉ P := fun c hc => hsP (by
    have := P.add_mem hc (P.mul_mem_left c ha)
    simpa using this)
  by_cases h1 : s - k * a ∈ Q
  · right
    refine ⟨hP _, fun h2 => ?_⟩
    have hma : m * a ∈ Q := by
      have := Q.sub_mem h1 h2
      have e : s - k * a - (s - (k + m) * a) = m * a := by ring
      rwa [e] at this
    rcases hQ.mem_or_mem hma with h | h
    · exact hm h
    · exact hsQ (by
        have := Q.add_mem h1 (Q.mul_mem_left k h)
        simpa using this)
  · left
    exact ⟨hP _, h1⟩
end Formalism.HermitianLattices.Ext.L3.WA.BE
