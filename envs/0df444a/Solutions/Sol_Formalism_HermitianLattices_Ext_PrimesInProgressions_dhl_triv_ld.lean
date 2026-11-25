-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.dhl_triv_ld
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:23:27.0147+00:00
-- url     : https://prove2.me/submissions/16b86de5-8865-448e-b0e0-fbc6c3d04014

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHLocalB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHLocal
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_dhl_ne_one

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
theorem _root_.solution (M : ℕ) [NeZero M] (z : ℂ) (hz : 1 < z.re) :
    -(deriv (DirichletCharacter.LFunctionTrivChar₁ M) z / DirichletCharacter.LFunctionTrivChar₁ M z)
      = negLD (1 : DirichletCharacter ℂ M) z - 1 / (z - 1) := by
  have hz1 : z ≠ 1 := dhl_ne_one hz
  have hf : ∀ w : ℂ, w ≠ 1 → DirichletCharacter.LFunctionTrivChar₁ M w =
      (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    intro w hw
    simp [DirichletCharacter.LFunctionTrivChar₁, hw]
  have hev : DirichletCharacter.LFunctionTrivChar₁ M =ᶠ[nhds z]
      fun w => (w - 1) * DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) w := by
    filter_upwards [eventually_ne_nhds hz1] with w hw
    exact hf w hw
  have hd := DirichletCharacter.differentiableAt_LFunction (1 : DirichletCharacter ℂ M) z (Or.inl hz1)
  have hL0 := DirichletCharacter.LFunction_ne_zero_of_one_le_re (1 : DirichletCharacter ℂ M)
    (Or.inr hz1) hz.le
  have hlin : DifferentiableAt ℂ (fun w : ℂ => w - 1) z := differentiableAt_id.sub_const 1
  have hder : deriv (DirichletCharacter.LFunctionTrivChar₁ M) z =
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M) z +
        (z - 1) * deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ M)) z := by
    rw [hev.deriv_eq, deriv_fun_mul hlin hd]
    simp
  rw [hder, hf z hz1]
  unfold negLD
  have hz1' : z - 1 ≠ 0 := sub_ne_zero.mpr hz1
  field_simp
  ring
end Formalism.HermitianLattices.Ext.PrimesInProgressions
