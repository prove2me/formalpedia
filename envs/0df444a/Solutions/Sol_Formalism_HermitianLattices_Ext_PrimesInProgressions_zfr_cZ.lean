-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.zfr_cZ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:02:24.083446+00:00
-- url     : https://prove2.me/submissions/5e5685c3-7b9f-423e-b997-5f44be4e7c04

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DeuringHeilbronnM
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_inRegion_mono
import Theorems.Thm_Formalism_ZeroFreeDirichlet_zFRDirichlet


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
theorem _root_.solution (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : InRegion cZ q s)
    (hz : IsLZero χ s) :
    χ ^ 2 = 1 ∧ χ ≠ 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
      ∀ (χ' : DirichletCharacter ℂ q) (s' : ℂ), InRegion cZ q s' → IsLZero χ' s' → χ' = χ ∧ s' = s := by
  have hZ := Classical.choose_spec Formalism.ZeroFreeDirichlet.zFRDirichlet
  have hle : cZ ≤ Classical.choose Formalism.ZeroFreeDirichlet.zFRDirichlet := min_le_left _ _
  obtain ⟨h1, h2, h3, h4, h5⟩ := hZ.2 q χ s (inRegion_mono hle q s hs) hz
  exact ⟨h1, h2, h3, h4, fun χ' s' hs' hz' => h5 χ' s' (inRegion_mono hle q s' hs') hz'⟩
end Formalism.HermitianLattices.Ext.PrimesInProgressions
