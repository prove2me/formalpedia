-- Prove2me | solution 1 for BookProof.CarlemanGeneralHop.flux_bound_gen
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-07T22:59:42.493663+00:00
-- url     : https://prove2.me/submissions/29b6a2e3-95fb-43c5-ae00-201cfc40fbfe

-- Generated from ChapterCarlemanGeneralHop.lean — solution of BookProof.CarlemanGeneralHop.flux_bound_gen
import Mathlib
import Definitions.Def_ChapterCarlemanGeneralHopPromoted
import Definitions.Def_ChapterHermiteCarlemanEsaPromoted
import Definitions.Def_ChapterCarlemanTwoStepPromoted
open BookProof.CarlemanGeneralHop




open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}

set_option maxHeartbeats 1000000 in

theorem solution {w : ℂ} {c : (Fin d →₀ ℕ) → ℝ} {p m : Fin d →₀ ℕ}
    (F G : Finset (Fin d →₀ ℕ)) (hzero : ∀ a ∈ F, a ∉ G → c a = 0)
    {Cn : ℝ} (hCn : 0 ≤ Cn) (hC : ∀ a ∈ G, |c a| ≤ Cn) :
    |(∑ a ∈ F, rtG u w c p m a).im|
      ≤ Cn * (‖w‖ * ((∑ a ∈ G, (‖u a‖ ^ 2 + ‖u (hshift p m a)‖ ^ 2)) / 2)) := by
  classical
  have h1 : |(∑ a ∈ F, rtG u w c p m a).im| ≤ ∑ a ∈ F, ‖rtG u w c p m a‖ :=
    (Complex.abs_im_le_norm _).trans (norm_sum_le _ _)
  have h2 : ∑ a ∈ F, ‖rtG u w c p m a‖ = ∑ a ∈ F ∩ G, ‖rtG u w c p m a‖ := by
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro x hx hxn
    have : c x = 0 := hzero x hx (fun hg => hxn (Finset.mem_inter.mpr ⟨hx, hg⟩))
    rw [rtG, this]
    simp
  have h3 : ∑ a ∈ F ∩ G, ‖rtG u w c p m a‖ ≤ ∑ a ∈ G, ‖rtG u w c p m a‖ :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
      (fun _ _ _ => norm_nonneg _)
  have h4 : ∀ a ∈ G, ‖rtG u w c p m a‖
      ≤ Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (hshift p m a)‖ ^ 2) / 2)) := by
    intro a ha
    have hnorm : ‖rtG u w c p m a‖ = ‖w‖ * |c a| * ‖u a‖ * ‖u (hshift p m a)‖ := by
      rw [rtG]; simp [Complex.norm_real]
    have hprod : ‖u a‖ * ‖u (hshift p m a)‖
        ≤ (‖u a‖ ^ 2 + ‖u (hshift p m a)‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖u a‖ - ‖u (hshift p m a)‖)]
    have hb1 : ‖w‖ * |c a| ≤ ‖w‖ * Cn :=
      mul_le_mul_of_nonneg_left (hC a ha) (norm_nonneg w)
    rw [hnorm]
    calc ‖w‖ * |c a| * ‖u a‖ * ‖u (hshift p m a)‖
        = (‖w‖ * |c a|) * (‖u a‖ * ‖u (hshift p m a)‖) := by ring
      _ ≤ (‖w‖ * Cn) * (‖u a‖ * ‖u (hshift p m a)‖) := by
          refine mul_le_mul_of_nonneg_right hb1 ?_
          positivity
      _ ≤ (‖w‖ * Cn) * ((‖u a‖ ^ 2 + ‖u (hshift p m a)‖ ^ 2) / 2) := by
          refine mul_le_mul_of_nonneg_left hprod ?_
          positivity
      _ = Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (hshift p m a)‖ ^ 2) / 2)) := by ring
  calc |(∑ a ∈ F, rtG u w c p m a).im|
      ≤ ∑ a ∈ F ∩ G, ‖rtG u w c p m a‖ := by rw [← h2]; exact h1
    _ ≤ ∑ a ∈ G, ‖rtG u w c p m a‖ := h3
    _ ≤ ∑ a ∈ G, Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (hshift p m a)‖ ^ 2) / 2)) :=
        Finset.sum_le_sum h4
    _ = Cn * (‖w‖ * ((∑ a ∈ G, (‖u a‖ ^ 2 + ‖u (hshift p m a)‖ ^ 2)) / 2)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_div]

/-! ## 5. Bessel's inequality for the two boundary layers -/
