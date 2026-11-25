-- Prove2me | solution 1 for Claim.zeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:07.411656+00:00
-- url     : https://prove2.me/submissions/ea9b993f-67ae-4b3a-bc5e-fb0de95690b2

import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_HalfPlane
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ClaimStrip
import Theorems.Thm_Claim_strip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open Claim
namespace Claim
theorem _root_.solution (h : HalfPlane) : Zeta := by
  intro s hz htriv hs1
  have hs0 : s ≠ 0 := fun e => by rw [e, riemannZeta_zero] at hz; norm_num at hz
  rcases lt_or_ge 0 s.re with hpos | hnpos
  · rcases lt_or_ge s.re 1 with hlt1 | hge1
    · have hL : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) s = 0 := by
        rw [DirichletCharacter.LFunction_modOne_eq]; exact hz
      exact strip h 1 1 s hpos hlt1 hL
    · exact absurd hz (riemannZeta_ne_zero_of_one_le_re hge1)
  · exfalso
    have hG : Gammaℝ s ≠ 0 := by
      intro hg
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hg
      rcases n with _ | n
      · exact hs0 (by simpa using hn)
      · exact htriv ⟨n, by rw [hn]; push_cast; ring⟩
    have hc : completedRiemannZeta s = 0 := by
      rw [riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff] at hz
      exact hz.resolve_right hG
    have h1s : 1 - s ≠ 0 := fun e => by
      have := congrArg Complex.re e
      rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
      linarith
    have hz' : riemannZeta (1 - s) = 0 := by
      rw [riemannZeta_def_of_ne_zero h1s, completedRiemannZeta_one_sub, hc, zero_div]
    exact riemannZeta_ne_zero_of_one_le_re (by rw [Complex.sub_re, Complex.one_re]; linarith) hz'
end Claim
