-- Prove2me | solution 1 for Formalism.GM.root_discs_disjoint_progression
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:28.354809+00:00
-- url     : https://prove2.me/submissions/e9c5c5e4-41e1-486f-bed8-cbf89bf4d458

import Definitions.Def_Formalism_MahlerMeasure_QuotientUpperBoundsOfPowerBounds
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WindowAP
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_norm_int
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_norm_sub_le_max
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_dvd_of_norm_lt
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_dvd_cancel
import Theorems.Thm_Formalism_GM_ArithmeticProgressionDivisibility_progr_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset
open ArithmeticProgressionDivisibility
open Classical
namespace Formalism.GM
theorem _root_.solution : DiscsDisjointAP := by
  intro p _ K _ _ _ roots t₀ d Y₀ h hd hY
  have key : ∀ (s : Multiset K) (P : ℕ → K → Prop) [∀ j, DecidablePred (P j)] (Y : Finset ℕ),
      (∀ a, ∀ j ∈ Y, ∀ j' ∈ Y, P j a → P j' a → j = j') →
      ∑ j ∈ Y, Multiset.card (s.filter (P j)) ≤ Multiset.card s := by
    intro s P _ Y huq
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      have hstep : ∀ j ∈ Y, Multiset.card ((a ::ₘ s).filter (P j))
          = Multiset.card (s.filter (P j)) + (if P j a then 1 else 0) := by
        intro j _
        rw [Multiset.filter_cons]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Multiset.card_cons]
      have hle : ∑ j ∈ Y, (if P j a then 1 else 0) ≤ 1 := by
        simp only [Finset.sum_boole, Nat.cast_id]
        apply Finset.card_le_one.mpr
        intro j hj j' hj'
        rw [Finset.mem_filter] at hj hj'
        exact huq a j hj.1 j' hj'.1 hj.2 hj'.2
      omega
  have hpP : p.Prime := Fact.out
  have huniq : ∀ ζ : K, ∀ j ∈ range Y₀, ∀ j' ∈ range Y₀,
      ‖((progr t₀ d j : ℤ) : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)) →
      ‖((progr t₀ d j' : ℤ) : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ)) → j = j' := by
    intro ζ j hj j' hj' h1 h2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpP.one_lt
    have h3 : ‖((progr t₀ d j : ℤ) : K) - ((progr t₀ d j' : ℤ) : K)‖ < (p : ℝ) ^ (1 - (h : ℤ)) := by
      have h0 := norm_sub_le_max (((progr t₀ d j : ℤ) : K) - ζ) (((progr t₀ d j' : ℤ) : K) - ζ)
      rw [sub_sub_sub_cancel_right] at h0
      have h4 : (p : ℝ) ^ (-(h : ℤ)) < (p : ℝ) ^ (1 - (h : ℤ)) := zpow_lt_zpow_right₀ hp1 (by omega)
      exact lt_of_le_of_lt h0 (lt_of_le_of_lt (max_le h1 h2) h4)
    rw [← Int.cast_sub, progr_sub, norm_int (p := p)] at h3
    have h5 := dvd_cancel hd h (dvd_of_norm_lt _ h h3)
    rw [Finset.mem_range] at hj hj'
    obtain ⟨c, hc⟩ := h5
    have hph : (Y₀ : ℤ) ≤ (p : ℤ) ^ h := by exact_mod_cast hY
    have hppos : (0 : ℤ) < (p : ℤ) ^ h := pow_pos (by exact_mod_cast hpP.pos) h
    have hc0 : c = 0 := by
      by_contra hne
      have h6 : (p : ℤ) ^ h ≤ |(j : ℤ) - j'| := by
        rw [hc, abs_mul, abs_of_pos hppos]
        exact le_mul_of_one_le_right hppos.le (Int.one_le_abs hne)
      have h7 : |(j : ℤ) - j'| < Y₀ := by
        rw [abs_lt]
        constructor <;> omega
      linarith
    rw [hc0, mul_zero] at hc
    omega
  convert key roots
    (fun j ζ => ‖((progr t₀ d j : ℤ) : K) - ζ‖ ≤ (p : ℝ) ^ (-(h : ℤ))) (range Y₀) huniq
end Formalism.GM
