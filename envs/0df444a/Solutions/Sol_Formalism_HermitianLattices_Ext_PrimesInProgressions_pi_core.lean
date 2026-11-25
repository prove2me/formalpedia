-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.pi_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:46.651521+00:00
-- url     : https://prove2.me/submissions/140c8aa8-8a60-4883-ac3e-d3a93ea96b7d

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiC
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_main_lower
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_exp_sum_le_min_exponent
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_small_terms
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_abel_core
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_abs_piAP_sub_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_abs_psiAP_sub_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sum_cAP
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_vonMangoldtAP_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_vonMangoldtAP_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (M : ℕ) [NeZero M] (h8 : 8 ∣ M) (b : ℕ) (hb : b.Coprime M)
    (e : Option (DirichletCharacter ℂ M × ℝ)) {θ β η c A c₁ X : ℝ}
    (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1)
    (hmain : ∀ t : ℝ, 0 ≤ t → ∑ χ : DirichletCharacter ℂ M, χ ((b : ZMod M)⁻¹) * mainPsi e χ t =
      ((t - θ * t ^ β / β : ℝ) : ℂ))
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hη : θ ≤ 0 ∨ η ≤ (1 - β) * Real.log M) (hc₁ : 0 < c₁)
    (hηl : c₁ * (M : ℝ) ^ (-1 : ℝ) ≤ η) (hc : 0 < c) (hA : 0 ≤ A) (hX : 0 < X)
    (hL : 16 * Real.log M ≤ Real.log X)
    (hP : ∀ y : ℝ, √X ≤ y → y ≤ X → ∑ χ : DirichletCharacter ℂ M, ‖psiChi χ y - mainPsi e χ y‖ ≤
      A * y * η * (Real.exp (-(c * Real.log y / Real.log M)) + Real.exp (-(c * Real.sqrt (Real.log y))))) :
    |(piAP X M b : ℝ) - (liX X - θ * liX (X ^ β)) / (M.totient : ℝ)| ≤
      (10 * A + 5632 * Real.exp (2 * min (c / 2) (c ^ 2 / 2)) / c₁) *
        (Real.exp (-(min (c / 2) (c ^ 2 / 2) * Real.log X / Real.log M)) +
          Real.exp (-Real.sqrt (min (c / 2) (c ^ 2 / 2) * Real.log X))) *
        ((liX X - θ * liX (X ^ β)) / (M.totient : ℝ)) := by
  have hMpos : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hM8 : (8 : ℝ) ≤ M := by exact_mod_cast Nat.le_of_dvd hMpos h8
  have hM0 : (0 : ℝ) < M := by linarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hl : 2 ≤ Real.log M := by
    have h88 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have := Real.log_le_log (by norm_num) hM8
    linarith
  have hX16 : 16 ≤ X := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    rw [← Real.log_le_log_iff (by norm_num) hX]
    linarith
  have hφ1 : (1 : ℝ) ≤ M.totient := by exact_mod_cast Nat.totient_pos.2 hMpos
  have hφM : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hφ0 : (0 : ℝ) < M.totient := by linarith
  set l := Real.log M with hldef
  set L := Real.log X with hLdef
  set φ : ℝ := (M.totient : ℝ) with hφdef
  set c₃ := min (c / 2) (c ^ 2 / 2) with hc₃def
  have hc₃ : 0 ≤ c₃ := le_min (by positivity) (by positivity)
  set E := Real.exp (-(c₃ * L / l)) + Real.exp (-Real.sqrt (c₃ * L)) with hEdef
  have hE0 : 0 ≤ E := by positivity
  have hL32 : 32 ≤ L := by linarith
  have hs0 : 0 ≤ √X := Real.sqrt_nonneg X
  have hcore := abel_core (cAP M b) (vonMangoldtAP_nonneg M b) (vonMangoldtAP_le M b) (K := 1 / φ) (θ := θ) (β := β)
    (D := A * η * E / φ) (X := X) (by positivity) (by rw [div_le_one hφ0]; exact hφ1) hθ hβ hβ1 hX16
    (by positivity) (by
      intro t h1 h2
      have hs4 : 0 < √X := Real.sqrt_pos.2 hX
      have ht0 : 0 < t := by linarith
      have hu : L / 2 ≤ Real.log t := by
        rw [hLdef, ← Real.log_sqrt hX.le]
        exact Real.log_le_log hs4 h1
      rw [sum_cAP]
      calc |psiAP M b t - Fm (1 / φ) θ β t|
          ≤ (∑ χ : DirichletCharacter ℂ M, ‖psiChi χ t - mainPsi e χ t‖) / φ :=
            abs_psiAP_sub_le M b hb e θ β t (hmain t ht0.le)
        _ ≤ (A * t * η * E) / φ := by
            gcongr
            refine (hP t h1 h2).trans ?_
            gcongr
            exact exp_sum_le_min_exponent hc (by linarith) (by linarith) hu
        _ = A * η * E / φ * t := by ring)
  have hpp := abs_piAP_sub_le M b (by linarith : 1 ≤ X)
  have hm := main_lower hθ hβ hβ1 hX16 (by linarith : l ≤ L) hη0 hη1 hη
  have hexpl : Real.exp l = M := Real.exp_log hM0
  have hst := small_terms (c₃ := c₃) (c₁ := c₁) (L := L) (l := l) (η := η) (φ := φ) hc₃ hc₁ hL (by linarith)
    (by
      have : (M : ℝ) ^ (-1 : ℝ) = Real.exp (-l) := by
        rw [Real.rpow_def_of_pos hM0]; congr 1; ring
      rw [← this]; exact hηl) hφ0 (by rw [hexpl]; exact hφM)
  rw [Real.exp_half, Real.exp_log hX] at hst
  set m := liX X - θ * liX (X ^ β) with hmdef
  set P := X * η / (2 * L) / φ with hPdef
  have hP0 : 0 ≤ P := by positivity
  have hPm : P ≤ m / φ := by
    rw [hPdef]
    gcongr
  have hKm : 1 / φ * m = m / φ := by ring
  rw [hKm] at hcore
  have h5 : 5 * (A * η * E / φ) * X / L = 10 * A * E * P := by
    rw [hPdef]
    field_simp
    ring
  rw [h5] at hcore
  have h40 : 40 * √X ≤ 40 * √X * L := by nlinarith
  have hEs : Real.exp (-Real.sqrt (c₃ * L)) ≤ E := by
    rw [hEdef]
    have := Real.exp_pos (-(c₃ * L / l))
    linarith
  have hA2 : 0 ≤ 5632 * Real.exp (2 * c₃) / c₁ := by positivity
  have hst2 : 44 * √X * L ≤ 5632 * Real.exp (2 * c₃) / c₁ * E * P :=
    hst.trans (by gcongr)
  have htot : |(piAP X M b : ℝ) - m / φ| ≤ (10 * A + 5632 * Real.exp (2 * c₃) / c₁) * E * P := by
    have hexp : (10 * A + 5632 * Real.exp (2 * c₃) / c₁) * E * P =
        10 * A * E * P + 5632 * Real.exp (2 * c₃) / c₁ * E * P := by ring
    have h44 : 44 * √X * L = 4 * √X * L + 40 * √X * L := by ring
    rw [hexp]
    rw [abs_le] at hcore hpp ⊢
    constructor <;> linarith [hcore.1, hcore.2, hpp.1, hpp.2]
  exact htot.trans (by gcongr)
end Formalism.HermitianLattices.Ext.PrimesInProgressions
