-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.exists_absNorm_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:36.035188+00:00
-- url     : https://prove2.me/submissions/52f43689-b2d8-47af-a67c-cb9f3626f0c0

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_span_resChar
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_resChar_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) :
    ∃ k : ℕ, 1 ≤ k ∧ Ideal.absNorm P = resChar P ^ k := by

  have hp := resChar_prime hP
  haveI : P.LiesOver (Ideal.span {((resChar P : ℕ) : ℤ)}) := ⟨span_resChar P⟩
  have h1 := Ideal.absNorm_eq_pow_inertiaDeg P (Nat.prime_iff_prime_int.mp hp)
  rw [show (((resChar P : ℕ) : ℤ)).natAbs = resChar P by simp] at h1
  refine ⟨_, ?_, h1⟩
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [h0, pow_zero, Ideal.absNorm_eq_one_iff] at h1
  exact hP.ne_top h1
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
