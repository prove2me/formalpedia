-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.IdealNormInequalities.resChar_le_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:18:36.221859+00:00
-- url     : https://prove2.me/submissions/3c278b02-bc2d-44a0-b447-d950ec900a01

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFilterResCharLe
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_resChar_prime
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_IdealNormInequalities_exists_absNorm_eq_pow

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
theorem _root_.solution {P : Ideal (𝓞 K)} (hP : P.IsMaximal) {q : ℕ}
    (hq : Ideal.absNorm P = q ^ 2) : resChar P ≤ q := by

  obtain ⟨k, hk, hk2⟩ := exists_absNorm_eq_pow hP
  have hp := resChar_prime hP
  have hdvd : resChar P ∣ q ^ 2 := by
    rw [← hq, hk2]
    exact dvd_pow_self _ (by omega)
  have hq0 : q ≠ 0 := by
    rintro rfl
    have h0 : resChar P ^ k = 0 := by rw [← hk2, hq]; simp
    exact hp.ne_zero (pow_eq_zero_iff (by omega) |>.mp h0)
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) (hp.dvd_of_dvd_pow hdvd)
end Formalism.HermitianLattices.Ext.L3.IdealNormInequalities
