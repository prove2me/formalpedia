-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.resChar_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:12.715641+00:00
-- url     : https://prove2.me/submissions/eeb9abb3-0fd2-416e-a952-07bb9006cfbf

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_span_resChar
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_under_ne_bot
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_under_isMaximal

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
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) : (resChar P).Prime := by

  have h1 := span_resChar P
  have hmax := under_isMaximal hP
  rw [← h1] at hmax
  have hne : ((resChar P : ℕ) : ℤ) ≠ 0 := by
    intro h0
    apply under_ne_bot hP
    rw [← h1, h0]
    simp
  have hpr := (Ideal.span_singleton_prime hne).mp hmax.isPrime
  exact Nat.prime_iff_prime_int.mpr hpr
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
