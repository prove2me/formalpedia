-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2b2.PfN.chi_eight_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:52:04.904643+00:00
-- url     : https://prove2.me/submissions/f2596e59-f911-4008-a573-a6e482d6918b

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_WeightedSumIntegralFormula
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_ZetaNonvanishing_ZetaRealNonvanish
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_NoExceptionalOfNoRealZero
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2b2
open Formalism.HermitianLattices.GL2b2.PfN
open Complex
namespace Formalism.HermitianLattices.GL2b2.PfN
theorem _root_.solution : ZeroFreeRegionGL2.chi8 ≠ 1 := by
  intro h
  have h1 := congrArg (fun χ : DirichletCharacter ℂ 8 => χ (3 : ZMod 8)) h
  have h3 : IsUnit (3 : ZMod 8) := by decide
  simp only [MulChar.one_apply h3] at h1
  have h2 : ZeroFreeRegionGL2.chi8 (3 : ZMod 8) = -1 := by
    unfold ZeroFreeRegionGL2.chi8
    simp only [MulChar.ringHomComp_apply]
    have : ZMod.χ₈ 3 = -1 := by decide
    rw [this]; simp
  rw [h2] at h1
  norm_num at h1
end Formalism.HermitianLattices.GL2b2.PfN
