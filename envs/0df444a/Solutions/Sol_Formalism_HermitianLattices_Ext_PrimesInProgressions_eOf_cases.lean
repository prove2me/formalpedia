-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.eOf_cases
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T06:37:42.455852+00:00
-- url     : https://prove2.me/submissions/160cd533-28b8-4ea6-bab7-e0f534ddbcc0

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) [NeZero M] :
    (∃ p : DirichletCharacter ℂ M × ℝ, eOf M = some p ∧ IsExcPair p.1 p.2 ∧ InRegion cZ M (p.2 : ℂ)) ∨
    (∃ p : DirichletCharacter ℂ M × ℝ, eOf M = some p ∧ IsExcPair p.1 p.2 ∧
      ∀ p' : DirichletCharacter ℂ M × ℝ, IsExcPair p'.1 p'.2 → ¬ InRegion cZ M (p'.2 : ℂ)) ∨
    (eOf M = none ∧ ∀ p' : DirichletCharacter ℂ M × ℝ, ¬ IsExcPair p'.1 p'.2) := by
  unfold eOf
  split_ifs with h h'
  · exact Or.inl ⟨h.choose, rfl, h.choose_spec.1, h.choose_spec.2⟩
  · exact Or.inr (Or.inl ⟨h'.choose, rfl, h'.choose_spec, fun p' hp' hr => h ⟨p', hp', hr⟩⟩)
  · exact Or.inr (Or.inr ⟨rfl, fun p' hp' => h' ⟨p', hp'⟩⟩)
end Formalism.HermitianLattices.Ext.PrimesInProgressions
