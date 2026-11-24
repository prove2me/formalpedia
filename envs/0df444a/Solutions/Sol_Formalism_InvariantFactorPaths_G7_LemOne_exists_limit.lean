-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G7.LemOne.exists_limit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:28:37.395765+00:00
-- url     : https://prove2.me/submissions/649f3533-2965-4b59-a24d-122377fabf71

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FirstDeriv
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_TopsChoicePartA
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_NotDvdChoosePowMul
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_coeff_rem
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_good_zero
import Theorems.Thm_Formalism_InvariantFactorPaths_G7_LemOne_good_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7
open Formalism.DworkPowerSeriesWeights (Integral mvExp)
open Formalism.InvariantFactorPaths.G7.LemOne
variable {K : Type} [NormedField K] [IsUltrametricDist K]
namespace Formalism.InvariantFactorPaths.G7.LemOne
theorem _root_.solution [CompleteSpace K] {p : ℕ} (hp : p.Prime) (hnp : ‖(p : K)‖ = (p : ℝ)⁻¹)
    {F : MvPowerSeries (Fin 2) K}
    (hF0 : MvPowerSeries.constantCoeff F = 0) (hFi : Integral F)
    (hF1 : ∀ n : Fin 2 →₀ ℕ, n.degree = 1 → MvPowerSeries.coeff n F = 1)
    (hFl : cob F (lgF K p) = 0) (hde : Integral (cob F (g0F K p)))
    {f : PowerSeries K} (hf0 : PowerSeries.constantCoeff f = 0) (hcob : Integral (cob F f)) :
    ∃ a b : K, ‖a‖ ≤ 1 ∧ ∀ n, ‖PowerSeries.coeff n (rem p f a b)‖ ≤ 1 := by
  have hstep := good_succ hp hnp hF0 hFi hF1 hFl hde hcob
  choose! fa fb hfab using hstep
  obtain ⟨s, hs0, hs1⟩ : ∃ s : ℕ → K × K, s 0 = (0, PowerSeries.coeff 1 f) ∧
      ∀ j, s (j + 1) = (fa j (s j).1 (s j).2, fb j (s j).1 (s j).2) :=
    ⟨fun j => Nat.rec (0, PowerSeries.coeff 1 f) (fun j t => (fa j t.1 t.2, fb j t.1 t.2)) j,
      rfl, fun _ => rfl⟩
  have hgood : ∀ j, Good p f j (s j).1 (s j).2 := by
    intro j
    induction j with
    | zero => rw [hs0]; exact good_zero hp hnp hF0 hFi hF1 hFl hde hf0 hcob
    | succ j ih => rw [hs1]; exact (hfab j _ _ ih).1
  have hr : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have hca : CauchySeq fun j => (s j).1 := by
    refine cauchySeq_of_le_geometric ((p : ℝ)⁻¹) 1 hr fun j => ?_
    rw [dist_eq_norm, norm_sub_rev, one_mul, hs1]
    exact (hfab j _ _ (hgood j)).2.1
  have hcb : CauchySeq fun j => (s j).2 := by
    refine cauchySeq_of_le_geometric ((p : ℝ)⁻¹) 1 hr fun j => ?_
    rw [dist_eq_norm, norm_sub_rev, one_mul, hs1]
    exact (hfab j _ _ (hgood j)).2.2
  obtain ⟨a, hat⟩ := cauchySeq_tendsto_of_complete hca
  obtain ⟨b, hbt⟩ := cauchySeq_tendsto_of_complete hcb
  refine ⟨a, b, le_of_tendsto hat.norm (Filter.Eventually.of_forall fun j => (hgood j).1),
    fun n => ?_⟩
  have hlim : Filter.Tendsto (fun j => PowerSeries.coeff n (rem p f (s j).1 (s j).2)) Filter.atTop
      (nhds (PowerSeries.coeff n (rem p f a b))) := by
    simp only [coeff_rem]
    exact (tendsto_const_nhds.sub (hat.mul_const _)).sub (hbt.mul_const _)
  refine le_of_tendsto hlim.norm (Filter.eventually_atTop.2 ⟨n, fun j hj => (hgood j).2 n ?_⟩)
  have : 2 * j + 1 < p ^ (2 * j + 1) := Nat.lt_pow_self hp.one_lt
  omega
end Formalism.InvariantFactorPaths.G7.LemOne
