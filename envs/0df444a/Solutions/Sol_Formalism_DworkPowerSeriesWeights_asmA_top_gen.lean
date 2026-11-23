-- Prove2me | solution 1 for Formalism.DworkPowerSeriesWeights.asmA_top_gen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:05:43.71185+00:00
-- url     : https://prove2.me/submissions/2aa90461-6aa8-407b-a4c4-fa3257ae7eda

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementA
import Definitions.Def_Formalism_IncomingBounds_FlowDegreeBounds_PadicValFactorialRatioProd
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_CapacityLeReachCapacity
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_odd_hasSum
import Theorems.Thm_Formalism_DworkPowerSeriesWeights_asmA_top_choice

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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
namespace Formalism.DworkPowerSeriesWeights
theorem _root_.solution (l : ℕ) (hl : 2 ≤ l) (A : ℝ) (hA : 0 ≤ A) (cap : ℕ → ℝ)
    (hcap : ∀ j, 0 ≤ cap j) (D : ℕ∞) (hDodd : ∀ e : ℕ, D = e → Odd e) (R : Finset ℕ)
    (hR : ∀ j ∈ R, Odd j) :
    ∃ ε : ℝ, 0 ≤ ε ∧ (∀ e : ℕ, D = e → ((l : ℝ) ^ e)⁻¹ ≤ ε) ∧
      (∑' e, asmA_f l A cap D e) + (A * ε + ∑ j ∈ R, cap j * max (1 - (l : ℝ) ^ j * ε) 0) ≤
        A * gam l := by
  have hx : ∀ e : ℕ, 0 ≤ A / (l : ℝ) ^ e := fun e => div_nonneg hA (by positivity)
  have hf0 : ∀ e, 0 ≤ asmA_f l A cap D e := by
    intro e
    unfold asmA_f
    split_ifs
    · exact le_max_right _ _
    · exact hx e
    · exact le_rfl
  have hfg : ∀ e, asmA_f l A cap D e ≤ asmA_g l A e := by
    intro e
    unfold asmA_f asmA_g
    by_cases ho : Odd e
    · rw [if_pos ho]
      split_ifs
      · exact max_le (by linarith [hcap e]) (hx e)
      · exact le_rfl
      · exact hx e
    · rw [if_neg ho, if_neg (fun h' => ho h'.1), if_neg (fun h' => ho h'.1)]
  have hgs : HasSum (asmA_g l A) (A * gam l) := by
    have hfun : asmA_g l A = fun i => A * (if Odd i then ((l : ℝ) ^ i)⁻¹ else 0) := by
      funext e
      unfold asmA_g
      split_ifs
      · rw [div_eq_mul_inv]
      · rw [mul_zero]
    rw [hfun]
    exact (asmA_odd_hasSum l hl).mul_left A
  have hfs : Summable (asmA_f l A cap D) :=
    Summable.of_nonneg_of_le hf0 hfg hgs.summable
  have hhs : Summable (fun e => asmA_g l A e - asmA_f l A cap D e) := hgs.summable.sub hfs
  have hmin : ∀ e : ℕ, Odd e → (e : ℕ∞) < D →
      min (A / (l : ℝ) ^ e) (cap e) ≤ asmA_g l A e - asmA_f l A cap D e := by
    intro e ho he
    unfold asmA_f asmA_g
    rw [if_pos ho, if_pos ⟨ho, he⟩]
    rcases le_total (A / (l : ℝ) ^ e) (cap e) with h1 | h1
    · rw [min_eq_left h1, max_eq_right (by linarith)]
      linarith
    · rw [min_eq_right h1, max_eq_left (by linarith)]
      linarith
  have hDv : ∀ e : ℕ, D = e → A / (l : ℝ) ^ e ≤ asmA_g l A e - asmA_f l A cap D e := by
    intro e he
    have ho := hDodd e he
    unfold asmA_f asmA_g
    rw [if_pos ho, if_neg (fun h' => by rw [he] at h'; exact lt_irrefl _ h'.2),
      if_neg (fun h' => by rw [he] at h'; exact lt_irrefl _ h'.2)]
    linarith
  obtain ⟨ε, hε0, hεD, hε⟩ := asmA_top_choice l hl A cap (fun e => asmA_g l A e - asmA_f l A cap D e)
    hcap (fun e => by linarith [hfg e]) hhs R D hR hmin hDv
  refine ⟨ε, hε0, hεD, ?_⟩
  have htot : ∑' e, asmA_f l A cap D e + ∑' e, (asmA_g l A e - asmA_f l A cap D e) = A * gam l := by
    rw [← Summable.tsum_add hfs hhs]
    simp only [add_sub_cancel]
    exact hgs.tsum_eq
  linarith
end Formalism.DworkPowerSeriesWeights
