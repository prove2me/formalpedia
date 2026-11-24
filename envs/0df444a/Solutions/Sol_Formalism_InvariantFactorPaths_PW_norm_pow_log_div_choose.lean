-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.norm_pow_log_div_choose
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:01:17.767088+00:00
-- url     : https://prove2.me/submissions/12bceb9f-cff6-4830-b6ca-aa6fde1fc84a

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset
variable {p : ℕ} [Fact p.Prime]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {n k N : ℕ} (hk : k ≤ n) (hn : n ≤ N) :
    ‖(p : ℚ_[p]) ^ (Nat.log p N) / (n.choose k : ℚ_[p])‖ ≤ 1 := by
  have hp : p.Prime := Fact.out
  have hC : n.choose k ≠ 0 := (Nat.choose_pos hk).ne'
  have hv : (n.choose k).factorization p ≤ Nat.log p N :=
    Nat.factorization_choose_le_log.trans (Nat.log_mono_right hn)
  have hdecomp : ((n.choose k : ℕ) : ℚ_[p]) = (p : ℚ_[p]) ^ ((n.choose k).factorization p) *
      ((n.choose k / p ^ ((n.choose k).factorization p) : ℕ) : ℚ_[p]) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self]
  have hr : ‖((n.choose k / p ^ ((n.choose k).factorization p) : ℕ) : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr (Nat.not_dvd_ordCompl hp hC))
  rw [hdecomp, norm_div, norm_mul, hr, mul_one, Padic.norm_p_pow, Padic.norm_p_pow,
    div_le_one (zpow_pos (by exact_mod_cast hp.pos) _)]
  exact zpow_le_zpow_right₀ (by exact_mod_cast hp.one_lt.le) (by omega)
end Formalism.InvariantFactorPaths.PW
