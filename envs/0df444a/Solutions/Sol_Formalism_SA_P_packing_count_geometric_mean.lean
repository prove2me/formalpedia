-- Prove2me | solution 1 for Formalism.SA.P.packing_count_geometric_mean
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:46:28.18929+00:00
-- url     : https://prove2.me/submissions/afa4fd44-09f9-4dbb-998c-aa48ea5d9041

import Definitions.Def_Formalism_LatticeRigidity_PackCount
import Definitions.Def_Formalism_LatticeRigidity_HeightMinimum_PackingCountGeometricMean
import Theorems.Thm_Formalism_SA_P_card_le_of_separated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Module
open Formalism Formalism.SA Formalism.SA.P
namespace Formalism.SA.P
theorem _root_.solution : Formalism.SA.P7.PackCount := by
  unfold Formalism.SA.P7.PackCount
  intro ι _ _ V _ _ _ N hN S lam X hlam hX hsep hbd
  have hnpos : 0 < Fintype.card ι := Fintype.card_pos
  have hnR : (0 : ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hnpos
  have hQpos : 0 < ∏ v, X v := Finset.prod_pos (fun v _ => hX v)
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (∏ v, X v) ^ (1 / (Fintype.card ι : ℝ)) := ⟨_, rfl⟩
  have hPpos : 0 < P := by rw [hP]; exact Real.rpow_pos_of_pos hQpos _
  have hPn : P ^ Fintype.card ι = ∏ v, X v := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hQpos.le, one_div_mul_cancel hnR.ne',
      Real.rpow_one]
  obtain ⟨c, hcdef⟩ : ∃ c : ι → ℝ, c = fun v => P / X v := ⟨_, rfl⟩
  have hc : ∀ v, 0 < c v := by
    intro v
    rw [hcdef]
    exact div_pos hPpos (hX v)
  have hcX : ∀ v, c v * X v = P := by
    intro v
    rw [hcdef]
    exact div_mul_cancel₀ P (hX v).ne'
  have hprodc : ∏ v, c v = 1 := by
    rw [hcdef]
    simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ]
    rw [hPn, div_self hQpos.ne']
  obtain ⟨g, hg⟩ : ∃ g : ((v : ι) → V v) → ((v : ι) → V v),
      ∀ x, g x = fun v => c v • x v := ⟨_, fun _ => rfl⟩
  have hbdg : ∀ x ∈ S, ‖g x‖ ≤ P := by
    intro x hx
    refine (pi_norm_le_iff_of_nonneg hPpos.le).mpr fun v => ?_
    have hgv : g x v = c v • x v := by rw [hg]
    rw [hgv, norm_smul, Real.norm_eq_abs, abs_of_pos (hc v)]
    calc c v * ‖x v‖ ≤ c v * X v := mul_le_mul_of_nonneg_left (hbd x hx v) (hc v).le
      _ = P := hcX v
  have hsepg : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → lam ≤ ‖g x - g y‖ := by
    intro x hx y hy hxy
    have h1 := hsep x hx y hy hxy
    have hM0 : 0 ≤ ‖g x - g y‖ := norm_nonneg _
    have hcoord : ∀ v, c v * ‖x v - y v‖ ≤ ‖g x - g y‖ := by
      intro v
      have hd : (g x - g y) v = c v • (x v - y v) := by
        simp only [Pi.sub_apply, hg, smul_sub]
      have h2 := norm_le_pi_norm (g x - g y) v
      rw [hd, norm_smul, Real.norm_eq_abs, abs_of_pos (hc v)] at h2
      exact h2
    have hprod : ∏ v, ‖x v - y v‖ ≤ ‖g x - g y‖ ^ Fintype.card ι := by
      calc ∏ v, ‖x v - y v‖ = (∏ v, c v) * ∏ v, ‖x v - y v‖ := by rw [hprodc, one_mul]
        _ = ∏ v, (c v * ‖x v - y v‖) := by rw [Finset.prod_mul_distrib]
        _ ≤ ∏ _v : ι, ‖g x - g y‖ :=
            Finset.prod_le_prod (fun v _ => mul_nonneg (hc v).le (norm_nonneg _))
              (fun v _ => hcoord v)
        _ = ‖g x - g y‖ ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
    calc lam ≤ (∏ v, ‖x v - y v‖) ^ (1 / (Fintype.card ι : ℝ)) := h1
      _ ≤ (‖g x - g y‖ ^ Fintype.card ι) ^ (1 / (Fintype.card ι : ℝ)) :=
          Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => norm_nonneg _) hprod (by positivity)
      _ = ‖g x - g y‖ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hM0, mul_one_div_cancel hnR.ne',
            Real.rpow_one]
  have main := Formalism.SA.P.card_le_of_separated S g lam P hlam hPpos.le hsepg hbdg
  have hdim : finrank ℝ ((v : ι) → V v) = N * Fintype.card ι := by
    rw [Module.finrank_pi_fintype]
    simp only [hN, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  rw [hdim] at main
  rw [← hP]
  exact main
end Formalism.SA.P
