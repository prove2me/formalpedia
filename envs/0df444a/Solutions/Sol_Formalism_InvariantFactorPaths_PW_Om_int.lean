-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.PW.Om_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:11:41.78763+00:00
-- url     : https://prove2.me/submissions/8a2e6c82-ae0a-4795-ad65-3086e2687d7e

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementA
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_Om_insert
import Theorems.Thm_Formalism_InvariantFactorPaths_PW_norm_pow_log_div_choose

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
variable {W ι : Type} [AddCommGroup W] [Module ℚ_[p] W] [DecidableEq ι]
namespace Formalism.InvariantFactorPaths.PW
theorem _root_.solution {E : ι → ι → Module.End ℚ_[p] W} (hE : GlRel E) {M : AddSubgroup W} (hZ : ZpClosed p M)
    (hD : DivStable E M) (z : ι) (N : ℕ) (S : Finset ι) : z ∉ S → ∀ c q : ℕ, q + c ≤ N → ∀ u ∈ M,
      ((p : ℚ_[p]) ^ (S.card * Nat.log p N) *
        ((c.factorial : ℚ_[p]) / (((q + c).factorial : ℚ_[p]) * (q.factorial : ℚ_[p])))) • Om E S z q u ∈ M := by
  induction S using Finset.induction_on with
  | empty =>
    intro _ c q _ u hu
    cases q with
    | zero => simpa [Om, Nat.factorial_ne_zero] using hu
    | succ q => simpa [Om] using M.zero_mem
  | insert i S hi ih =>
    intro hz c q hqc u hu
    have hzi : z ≠ i := fun e => hz (e ▸ Finset.mem_insert_self _ _)
    have hzS : z ∉ S := fun e => hz (Finset.mem_insert_of_mem e)
    rw [Om_insert hE hz hi q, LinearMap.sum_apply, Finset.smul_sum]
    refine AddSubgroup.sum_mem _ fun k hk => ?_
    have hkq : k ≤ q := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hu' : ((k.factorial : ℚ_[p]))⁻¹ • ((E i z) ^ k) u ∈ M := hD i z (Ne.symm hzi) k u hu
    have hY := ih hzS (c + k) (q - k) (by omega) _ hu'
    have hDY := hD z i hzi k _ hY
    have hnorm := norm_pow_log_div_choose (p := p) (n := c + k) (k := k) (N := N) (by omega)
      (by omega)
    have key := hZ _ hnorm _ hDY
    convert key using 1
    simp only [LinearMap.smul_apply, Module.End.mul_apply, map_smul, smul_smul]
    congr 1
    have hqk : q - k + (c + k) = q + c := by omega
    rw [hqk, Finset.card_insert_of_notMem hi, Nat.cast_choose ℚ_[p] hkq,
      Nat.cast_choose ℚ_[p] (Nat.le_add_left k c), Nat.add_sub_cancel]
    have h1 : (c.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : (k.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h3 : ((q - k).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h4 : ((q + c).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h5 : (q.factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h6 : ((c + k).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    ring
end Formalism.InvariantFactorPaths.PW
