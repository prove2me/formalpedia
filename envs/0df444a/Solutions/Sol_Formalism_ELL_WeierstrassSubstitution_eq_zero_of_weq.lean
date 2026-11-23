-- Prove2me | solution 1 for Formalism.ELL.WeierstrassSubstitution.eq_zero_of_weq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:21:16.175031+00:00
-- url     : https://prove2.me/submissions/899f8d35-71b5-48d0-9170-aa32e139504d

import Definitions.Def_Formalism_EllipticTorsion_WChordSeries
import Definitions.Def_Formalism_EllipticTorsion_EllipticTorsionProofs_WSubst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.ELL Formalism.ELL.WeierstrassSubstitution
namespace Formalism.ELL.WeierstrassSubstitution
theorem _root_.solution {K : Type u} [Field K] {W : WeierstrassCurve K} {σ : Type}
    {s : MvPowerSeries σ K} (h : Formalism.ELL.WEqAt W s 0) : s = 0 := by
  unfold Formalism.ELL.WEqAt at h
  simp only [mul_zero, smul_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h
  exact pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h.symm
end Formalism.ELL.WeierstrassSubstitution
