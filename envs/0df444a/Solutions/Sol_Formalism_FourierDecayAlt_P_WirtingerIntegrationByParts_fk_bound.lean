-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.fk_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:49.151239+00:00
-- url     : https://prove2.me/submissions/519abfb7-1c56-4608-9337-261a8a41adc1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_tsupport_smul_subset__d2c1bc7b3def
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_Bd_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_bk_contDiffOn

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] {d : ℕ}
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
theorem _root_.solution {q n : ℕ} (hn : n ≤ q) {Ω : Set (Fin d → ℂ)} {g : (Fin d → ℂ) → ℂ} {η P B S : ℝ} (hΩ : IsOpen Ω)
    (hg : DifferentiableOn ℂ g Ω) (hη : 0 < η) (hP : 0 < P) (hlow : ∀ x ∈ Ω, η ≤ ‖fderiv ℂ g x‖) (hB : 0 ≤ B)
    (hbk : ∀ x ∈ Ω, ∀ k, Bd (bk g k) Ω x q (B / ‖fderiv ℂ g x‖) P)
    {a : (Fin d → ℂ) → V} (ha : ContDiff ℝ n a) (hsupp : tsupport a ⊆ Ω)
    (hb : ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S * P ^ j) (k : Fin d) :
    ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun y => bk g k y • a y) x‖ ≤ (2 ^ q * B * S / η) * P ^ j := by
  have hS : 0 ≤ S := by
    have := hb 0 (Nat.zero_le _) 0
    simp only [pow_zero, mul_one] at this
    exact (norm_nonneg _).trans this
  have hne : ∀ x ∈ Ω, fderiv ℂ g x ≠ 0 := fun x hx h => by
    have := hlow x hx
    rw [h, norm_zero] at this
    linarith
  intro j hj x
  by_cases hx : x ∈ Ω
  · have b1 : Bd (bk g k) Ω x n (B / ‖fderiv ℂ g x‖) P := fun i hi => hbk x hx k i (hi.trans hn)
    have b2 : Bd a Ω x n S P := fun i hi => by
      rw [iteratedFDerivWithin_of_isOpen i hΩ hx]; exact hb i hi x
    have b3 := Bd.smul hΩ hx hP.le (bk_contDiffOn hΩ hg hne k n) ha.contDiffOn b1 b2 j hj
    rw [iteratedFDerivWithin_of_isOpen j hΩ hx] at b3
    refine b3.trans ?_
    have hG : 0 < ‖fderiv ℂ g x‖ := lt_of_lt_of_le hη (hlow x hx)
    have h1 : B / ‖fderiv ℂ g x‖ ≤ B / η := div_le_div_of_nonneg_left hB hη (hlow x hx)
    have h2 : (2 : ℝ) ^ n ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hn
    have h3 : 2 ^ q * B * S / η = 2 ^ q * (B / η) * S := by ring
    rw [h3]
    have h4 : 0 ≤ B / ‖fderiv ℂ g x‖ := div_nonneg hB hG.le
    gcongr
  · have hx' : x ∉ tsupport (fun y => bk g k y • a y) := fun h =>
      hx (hsupp (tsupport_smul_subset' _ _ h))
    have hx'' : x ∉ tsupport (iteratedFDeriv ℝ j (fun y => bk g k y • a y)) := fun h =>
      hx' (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) j h)
    rw [image_eq_zero_of_notMem_tsupport hx'', norm_zero]
    positivity
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
