-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.zero_in_region
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:18:47.668798+00:00
-- url     : https://prove2.me/submissions/3c110505-a055-4f88-baf1-8cb079b5589d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_zfr_cZ
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_eOf_cases
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_isExcPair_of_region

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
theorem _root_.solution (M : ℕ) [NeZero M] (hM : 2 ≤ M) (χ : DirichletCharacter ℂ M) (s : ℂ)
    (hs : InRegion cZ M s) (hz : IsLZero χ s) :
    ∃ β₁ : ℝ, eOf M = some (χ, β₁) ∧ s = (β₁ : ℂ) ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 := by
  obtain ⟨h2, h1, him, hder, huniq⟩ := zfr_cZ M χ s hs hz
  have hs' : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hzr : DirichletCharacter.LFunction χ ((s.re : ℝ) : ℂ) = 0 := by rw [← hs']; exact hz.2
  have hrr : InRegion cZ M ((s.re : ℝ) : ℂ) := by rw [← hs']; exact hs
  have hex : IsExcPair χ s.re := isExcPair_of_region M hM χ s.re h2 h1 hzr hrr
  rcases eOf_cases M with ⟨p, hp, hpex, hpr⟩ | ⟨p, hp, hpex, hno⟩ | ⟨hn, hno⟩
  · have hz' : IsLZero p.1 (p.2 : ℂ) := ⟨Or.inl hpex.2.1, hpex.2.2.1⟩
    obtain ⟨e1, e2⟩ := huniq p.1 (p.2 : ℂ) hpr hz'
    refine ⟨p.2, ?_, e2.symm, hder⟩
    rw [hp, ← e1]
  · exact absurd hrr (hno (χ, s.re) hex)
  · exact absurd hex (hno (χ, s.re))
end Formalism.HermitianLattices.Ext.PrimesInProgressions
