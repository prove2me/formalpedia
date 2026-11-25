-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhFam_re
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:30:25.614301+00:00
-- url     : https://prove2.me/submissions/21e2c1ed-2796-4915-ab32-3d3aa6023a6c

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
theorem _root_.solution (Z : Finset ℂ) (m : ℂ → ℕ) (s x : ℂ) (η : ℝ) (hZ : ∀ ρ ∈ Z, ρ.re < 1)
    (hs : s.re = 1 + η) (hx : x ∈ dhFam Z m s) : η ≤ x.re := by
  unfold dhFam at hx
  rw [Multiset.mem_bind] at hx
  obtain ⟨ρ, hρ, hx⟩ := hx
  rw [Multiset.eq_of_mem_replicate hx, Complex.sub_re, hs]
  linarith [hZ ρ hρ]
end Formalism.HermitianLattices.Ext.PrimesInProgressions
