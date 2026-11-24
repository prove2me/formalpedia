-- Prove2me | solution 1 for Formalism.FG.CongrVAux.fwd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:10.064439+00:00
-- url     : https://prove2.me/submissions/38d9a81f-a769-4e32-9f07-18899c237247

import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CoeffV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_IntegralSubstVector
import Definitions.Def_Formalism_TorsionNormIteration_InverseIntegralClasses_SigmaNormLeOne
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_CongrV
import Theorems.Thm_Formalism_FG_CongrVAux_norm_finsum_le
import Theorems.Thm_Formalism_FG_CongrVAux_divBy_prod_sub
import Theorems.Thm_Formalism_FG_coeff_bound_vector
import Theorems.Thm_Formalism_LT_PowCongr_valid


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.CongrVAux
open MvPowerSeries Formalism.G Formalism.LT Formalism.FG.SolveVAux
variable {K : Type u} [NormedField K] [IsUltrametricDist K] {τ : Type w}
namespace Formalism.FG.CongrVAux
theorem _root_.solution [CharZero K] {p q : ℕ} {hq : q ≠ 0} {σ : K →+* K} (hS : FunctionalEquationSetting K p q σ)
    {ι : Type v} [Fintype ι] {M : ι → ι → K} (hM : IntegralMat M) {f : ι → MvPowerSeries ι K}
    (hf0 : ∀ j, constantCoeff (f j) = 0) (hfe : IsFunEqTypeV p q hq σ M f)
    {α β : ι → MvPowerSeries τ K} (hα0 : ∀ i, constantCoeff (α i) = 0)
    (hβ0 : ∀ i, constantCoeff (β i) = 0) (hα : ∀ i, IntegralMv (α i)) (hβ : ∀ i, IntegralMv (β i))
    {r : ℕ} (hr : 1 ≤ r) (hd : ∀ i, DivByMv ((p : K) ^ r) (α i - β i)) (j : ι) :
    DivByMv ((p : K) ^ r) (subst α (f j) - subst β (f j)) := by
  intro d
  have hsα := hasSubst_of_constantCoeff_zero hα0
  have hsβ := hasSubst_of_constantCoeff_zero hβ0
  rw [map_sub, coeff_subst hsα, coeff_subst hsβ,
    ← finsum_sub_distrib (coeff_subst_finite hsα _ d) (coeff_subst_finite hsβ _ d)]
  refine norm_finsum_le (norm_nonneg _) fun e => ?_
  rw [← smul_sub, ← map_sub, smul_eq_mul, norm_mul]
  obtain ⟨k, hk, hkb⟩ := coeff_bound_vector K p q hq σ hS ι M hM ι f hf0 hfe j e
  obtain ⟨h, hh0, hqh⟩ := hS.2.1
  choose m hm using hk
  have hp1 : ‖(p : K)‖ ≤ 1 := hS.2.2.1.le
  have hpow : ∀ i, DivByMv ((p : K) ^ (r + h * k)) (α i ^ e i - β i ^ e i) := by
    intro i
    rw [hm i, hqh, ← pow_mul]
    exact PowCongr_valid K τ p hS.1 (α i) (β i) (hα i) (hβ i) r hr (hd i) (h * k) (m i)
  have hpc := divBy_prod_sub hα hβ e hpow e.support d
  have hpc' : ‖coeff d ((e.prod fun s n => α s ^ n) - e.prod fun s n => β s ^ n)‖ ≤
      ‖(p : K)‖ ^ (r + h * k) := by
    simpa only [Finsupp.prod, norm_pow] using hpc
  have hkk : ‖(p : K)‖ ^ (r + h * k) ≤ ‖(p : K)‖ ^ k * ‖(p : K)‖ ^ r := by
    rw [pow_add, mul_comm]
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg (norm_nonneg _) _)
    exact pow_le_pow_of_le_one (norm_nonneg _) hp1 (Nat.le_mul_of_pos_left k hh0)
  calc ‖coeff e (f j)‖ * ‖coeff d ((e.prod fun s n => α s ^ n) - e.prod fun s n => β s ^ n)‖
      ≤ ‖coeff e (f j)‖ * (‖(p : K)‖ ^ k * ‖(p : K)‖ ^ r) :=
        mul_le_mul_of_nonneg_left (hpc'.trans hkk) (norm_nonneg _)
    _ = (‖coeff e (f j)‖ * ‖(p : K)‖ ^ k) * ‖(p : K)‖ ^ r := by ring
    _ ≤ 1 * ‖(p : K)‖ ^ r := mul_le_mul_of_nonneg_right hkb (pow_nonneg (norm_nonneg _) _)
    _ = ‖(p : K) ^ r‖ := by rw [one_mul, norm_pow]
end Formalism.FG.CongrVAux
