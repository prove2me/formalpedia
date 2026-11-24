-- Prove2me | solution 1 for Formalism.mxS_mellin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:46:34.156921+00:00
-- url     : https://prove2.me/submissions/cd553556-a002-4344-aabe-fd21bc2f553f

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_MellinSAux
import Theorems.Thm_Formalism_mxS_eq_indicator

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
namespace Formalism
theorem _root_.solution {n : ℕ} (hn : 1 ≤ n) {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 1) ∧
    ∫ x in Ioi (1 : ℝ), (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1) = (n : ℂ) ^ (-s) / (s * (s - 1)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hsub : Ioi (n : ℝ) ⊆ Ioi 1 := Ioi_subset_Ioi hn1
  have ha : (-s).re < -1 := by
    simp only [Complex.neg_re]
    linarith
  have hb : (-s - 1).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    linarith
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hs
    linarith
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.one_re, Complex.zero_re] at h'
    linarith
  have hs2 : -s + 1 ≠ 0 := by
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.add_re, Complex.neg_re, Complex.one_re, Complex.zero_re] at h'
    linarith

  have hfun : (fun x : ℝ => (mxS n x : ℂ) * (x : ℂ) ^ (-s - 1)) =
      (Ioi (n : ℝ)).indicator (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    rw [mxS_eq_indicator hn x]
    by_cases hx : x ∈ Ioi (n : ℝ)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Complex.ofReal_zero, zero_mul]
  have heq : EqOn (fun x : ℝ => ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1))
      (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)) (Ioi (n : ℝ)) := by
    intro x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (lt_trans hn0 (Set.mem_Ioi.mp hx)).ne'
    have hpow : (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - 1) * x := by
      calc (x : ℂ) ^ (-s) = (x : ℂ) ^ ((-s - 1) + 1) := by rw [sub_add_cancel]
        _ = (x : ℂ) ^ (-s - 1) * x := by rw [Complex.cpow_add _ _ hx0, Complex.cpow_one]
    show ((x / n - 1 : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1)
    rw [hpow]
    push_cast
    ring
  have hA : Integrable (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s)) (volume.restrict (Ioi (n : ℝ))) :=
    Integrable.const_mul (integrableOn_Ioi_cpow_of_lt ha hn0) (1 / (n : ℂ))
  have hB : Integrable (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (volume.restrict (Ioi (n : ℝ))) :=
    integrableOn_Ioi_cpow_of_lt hb hn0
  have hint : IntegrableOn (fun x : ℝ => 1 / (n : ℂ) * (x : ℂ) ^ (-s) - (x : ℂ) ^ (-s - 1))
      (Ioi (n : ℝ)) := hA.sub hB
  have hg := hint.congr_fun heq.symm measurableSet_Ioi
  rw [hfun]
  refine ⟨((integrable_indicator_iff measurableSet_Ioi).mpr hg).integrableOn, ?_⟩
  rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr hsub,
    setIntegral_congr_fun measurableSet_Ioi heq, integral_sub hA hB, integral_const_mul,
    integral_Ioi_cpow_of_lt ha hn0, integral_Ioi_cpow_of_lt hb hn0, sub_add_cancel,
    Complex.ofReal_natCast, Complex.cpow_add _ _ hnC, Complex.cpow_one]
  field_simp
  ring
end Formalism
