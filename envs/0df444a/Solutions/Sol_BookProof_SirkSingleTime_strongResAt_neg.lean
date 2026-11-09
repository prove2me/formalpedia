-- Prove2me | solution 1 for BookProof.SirkSingleTime.strongResAt_neg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T20:03:18.216453+00:00
-- url     : https://prove2.me/submissions/6e2d01c2-8c34-468c-8bdd-7a53d124f0d0

-- Generated from ChapterSirkSingleTimeShift.lean — solution of BookProof.SirkSingleTime.strongResAt_neg
import Mathlib
import Definitions.Def_ChapterSirkSingleTimeShift
import Theorems.Thm_BookProof_SirkSingleTime_norm_res_neg
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterStoneResolvent
open BookProof.SirkSingleTime



open scoped InnerProductSpace


open Filter Topology
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {T : UnboundedSelfAdjoint E} {S : ℕ → UnboundedSelfAdjoint E}

set_option maxHeartbeats 1000000 in
theorem solution {l : ℝ} (hl : l ≠ 0) (h : StrongResAt T S l) :
    StrongResAt T S (-l) := by

  intro y
  have hl' : -l ≠ 0 := neg_ne_zero.mpr hl
  set x : E := T.resCLM (-l) y with hx
  have hnorm : Tendsto (fun n => ‖(S n).resCLM (-l) y‖) atTop (𝓝 ‖x‖) := by
    have heq : ∀ n, ‖(S n).resCLM (-l) y‖ = ‖(S n).resCLM l y‖ := by
      intro n; simpa using norm_res_neg (S n) hl y
    have hxx : ‖x‖ = ‖T.resCLM l y‖ := by simpa [hx] using norm_res_neg T hl y
    simp only [heq, hxx]
    exact (h y).norm
  have hinner : Tendsto (fun n => (⟪(S n).resCLM (-l) y, x⟫_ℂ : ℂ)) atTop (𝓝 (⟪x, x⟫_ℂ : ℂ)) := by
    have heq : ∀ n, (⟪(S n).resCLM (-l) y, x⟫_ℂ : ℂ) = ⟪y, (S n).resCLM l x⟫_ℂ := by
      intro n; simpa using (S n).inner_res hl' y x
    have hxx : (⟪x, x⟫_ℂ : ℂ) = ⟪y, T.resCLM l x⟫_ℂ := by
      simpa [hx] using T.inner_res hl' y x
    simp only [heq, hxx]
    exact Filter.Tendsto.inner tendsto_const_nhds (h x)
  have hsq : Tendsto (fun n => ‖(S n).resCLM (-l) y - x‖ ^ 2) atTop (𝓝 0) := by
    have hexp : ∀ n, ‖(S n).resCLM (-l) y - x‖ ^ 2
        = ‖(S n).resCLM (-l) y‖ ^ 2 - 2 * (⟪(S n).resCLM (-l) y, x⟫_ℂ : ℂ).re + ‖x‖ ^ 2 := by
      intro n; exact norm_sub_sq (𝕜 := ℂ) _ _
    simp only [hexp]
    have h1 : Tendsto (fun n => ‖(S n).resCLM (-l) y‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := hnorm.pow 2
    have h2 : Tendsto (fun n => ((⟪(S n).resCLM (-l) y, x⟫_ℂ : ℂ).re)) atTop (𝓝 (‖x‖ ^ 2)) := by
      have hre := (Complex.continuous_re.tendsto _).comp hinner
      simp only [Function.comp_def] at hre
      have hxx : ((⟪x, x⟫_ℂ : ℂ)).re = ‖x‖ ^ 2 := by
        rw [inner_self_eq_norm_sq_to_K]
        simp [← Complex.ofReal_pow]
      rwa [hxx] at hre
    have hcomb := (h1.sub (h2.const_mul 2)).add (tendsto_const_nhds (x := ‖x‖ ^ 2))
    have : ‖x‖ ^ 2 - 2 * ‖x‖ ^ 2 + ‖x‖ ^ 2 = 0 := by ring
    rw [this] at hcomb
    exact hcomb
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  simp only [Function.comp_def] at hroot
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.sqrt_sq_eq_abs, abs_norm] using hroot
