-- Prove2me | solution 1 for Formalism.L2.SG.Pf.ThresholdBounds.qfac_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:18:35.929552+00:00
-- url     : https://prove2.me/submissions/68f08390-c440-4ddf-9e83-a660ac3f51ac

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementSz
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ThresholdBounds
import Theorems.Thm_Formalism_L2_SG_Pf_ThresholdBounds_v_sub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Finset
namespace Formalism.L2.SG.Pf.ThresholdBounds
open Formalism.FourierDecayAlt
variable (c : Sz.Cfg)
private theorem v_eq_vlast_add_four_mul_Del (i : ℕ) : c.v i = c.vlast + 4 * c.Del * ((c.k : ℝ) - 1 - (i : ℝ)) := rfl
end Formalism.L2.SG.Pf.ThresholdBounds
end
end

set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.ThresholdBounds
open Formalism.FourierDecayAlt
variable (c : Sz.Cfg)
namespace Formalism.L2.SG.Pf.ThresholdBounds
theorem _root_.solution (hOk : c.Ok) (hb1 : 40 * (c.m : ℝ) * c.k * c.Del ≤ c.b 1) {de : ℕ → ℝ} (hw : Sz.IsWord c.k de)
    {l : ℕ} (hl : l + 1 ≤ c.k) {Y : ℝ} (hY1 : 5 / 2 ≤ c.v l + Y) (hY2 : c.v l + Y ≤ c.Del / 2) {i : ℕ} (hi1 : 1 ≤ i)
    (hik : i ≤ c.k) : Y + 1 / 2 + c.u de i ≠ 0 := by
  have hk4 : (4 : ℝ) ≤ c.k := by exact_mod_cast hOk.hk
  have hm2 : (2 : ℝ) ≤ c.m := by exact_mod_cast hOk.hm
  have hD := hOk.hDel
  have hv0 := hOk.hv0
  have hlk : (l : ℝ) + 1 ≤ c.k := by exact_mod_cast hl
  have hvl : c.vlast ≤ c.v l := by
    rw [v_eq_vlast_add_four_mul_Del c l]
    have := mul_nonneg (by linarith : (0 : ℝ) ≤ 4 * c.Del) (by linarith : (0 : ℝ) ≤ (c.k : ℝ) - 1 - l)
    linarith
  have hmk : (8 : ℝ) * c.Del ≤ (c.m : ℝ) * c.k * c.Del := by
    have h8 : (8 : ℝ) ≤ (c.m : ℝ) * c.k := by nlinarith
    exact mul_le_mul_of_nonneg_right h8 (by linarith)
  have hkD : 4 * c.Del ≤ (c.k : ℝ) * c.Del := mul_le_mul_of_nonneg_right hk4 (by linarith)
  have hw1 : ∀ i, de i = 0 ∨ de i = 1 :=
    (show (∀ i, de i = 0 ∨ de i = 1) ∧ de (c.k - 1) = 0 from hw).1
  by_cases h1 : i = 1
  · subst h1
    have hu : c.u de 1 = c.a := by simp [Formalism.FourierDecayAlt.Sz.Cfg.u]
    have ha := hOk.ha
    have e := v_sub c 1 l
    push_cast at e
    have hl0 : 0 ≤ 4 * c.Del * (l : ℝ) := by positivity
    rw [hu]; apply ne_of_gt; linarith
  · by_cases hk : i = c.k
    · have hu : c.u de i = c.ulast := by rw [Formalism.FourierDecayAlt.Sz.Cfg.u, if_neg h1, if_pos hk]
      rw [hu]
      cases ht : c.top
      · have hul : c.ulast = c.vlast - 1 / 2 := by simp [Formalism.FourierDecayAlt.Sz.Cfg.ulast, ht]
        rw [hul]
        rcases Nat.lt_or_ge (l + 1) c.k with hlt | hge
        · have h2' : l + 2 ≤ c.k := by omega
          have h2 : (l : ℝ) + 2 ≤ c.k := by exact_mod_cast h2'
          have hvl' : c.vlast + 4 * c.Del ≤ c.v l := by
            rw [v_eq_vlast_add_four_mul_Del c l]
            have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (c.k : ℝ) - 1 - l by linarith)
              (by linarith : (0 : ℝ) ≤ 4 * c.Del)
            linarith
          apply ne_of_lt; linarith
        · have heq : (l : ℝ) + 1 = c.k := by exact_mod_cast (le_antisymm hl hge)
          have hv' : c.v l = c.vlast := by rw [v_eq_vlast_add_four_mul_Del c l, ← heq]; ring
          apply ne_of_gt; linarith
      · have hul : c.ulast = -c.bp := by simp [Formalism.FourierDecayAlt.Sz.Cfg.ulast, ht]
        rw [hul]
        have hbp := (hOk.htop ht).1
        apply ne_of_lt; linarith
    · have hu : c.u de i = c.v (i - 1) - 1 / 2 - de (i - 1) * c.Del := by rw [Formalism.FourierDecayAlt.Sz.Cfg.u, if_neg h1, if_neg hk]
      rw [hu]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      have e := v_sub c j l
      have hde := hw1 j
      rcases lt_trichotomy j l with hjl | rfl | hlj
      · have h' : (j : ℝ) + 1 ≤ l := by exact_mod_cast hjl
        have : 4 * c.Del * 1 ≤ 4 * c.Del * ((l : ℝ) - j) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        rcases hde with h | h <;> rw [h] <;> apply ne_of_gt <;> linarith
      · rcases hde with h | h <;> rw [h]
        · apply ne_of_gt; linarith
        · apply ne_of_lt; linarith
      · have h' : (l : ℝ) + 1 ≤ j := by exact_mod_cast hlj
        have : 4 * c.Del * ((l : ℝ) - j) ≤ 4 * c.Del * (-1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
        rcases hde with h | h <;> rw [h] <;> apply ne_of_lt <;> linarith
end Formalism.L2.SG.Pf.ThresholdBounds
