-- Prove2me | solution 1 for FarmerInfo.Exclusive.proposition_2_one_gt_two
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T22:08:50.247205+00:00
-- url     : https://prove2.me/submissions/276dc7c6-1863-4672-87e9-dfc8e2016209

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

open MeasureTheory Finset FarmerInfo.Exclusive

theorem solution (M : Model) (hM : M.Standing) :
    M.W 2 < M.W 1 := by
  obtain ⟨hn, ha, hb, hα, hβ, hγ⟩ := hM
  have hn' : (4 : ℝ) ≤ M.n := by exact_mod_cast hn
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 ≤ m ∧ (M.n : ℝ) = m + 4 := ⟨(M.n : ℝ) - 4, by linarith, by ring⟩
  have h1 : 0 < M.Psi 1 := by unfold Model.Psi; positivity
  have h2 : 0 < M.Psi 2 := by unfold Model.Psi; positivity
  have key : M.W 1 - M.W 2 = M.β * (256*M.α^6 + 768*M.α^5*M.β + 1024*M.α^5*M.γ*m + 4096*M.α^5*M.γ + 768*M.α^4*M.β^2 + 2112*M.α^4*M.β*M.γ*m + 8384*M.α^4*M.β*M.γ + 448*M.α^4*M.γ^2*m^2 + 5760*M.α^4*M.γ^2*m + 14912*M.α^4*M.γ^2 + 256*M.α^3*M.β^3 + 1152*M.α^3*M.β^2*M.γ*m + 4480*M.α^3*M.β^2*M.γ + 640*M.α^3*M.β*M.γ^2*m^2 + 8320*M.α^3*M.β*M.γ^2*m + 20992*M.α^3*M.β*M.γ^2 + 896*M.α^3*M.γ^3*m^2 + 8960*M.α^3*M.γ^3*m + 20224*M.α^3*M.γ^3 + 64*M.α^2*M.β^3*M.γ*m + 192*M.α^2*M.β^3*M.γ + 192*M.α^2*M.β^2*M.γ^2*m^2 + 2624*M.α^2*M.β^2*M.γ^2*m + 6080*M.α^2*M.β^2*M.γ^2 + 944*M.α^2*M.β*M.γ^3*m^2 + 9072*M.α^2*M.β*M.γ^3*m + 19168*M.α^2*M.β*M.γ^3 + 672*M.α^2*M.γ^4*m^2 + 6080*M.α^2*M.γ^4*m + 12848*M.α^2*M.γ^4 + 64*M.α*M.β^3*M.γ^2*m + 224*M.α*M.β^2*M.γ^3*m^2 + 1920*M.α*M.β^2*M.γ^3*m + 3296*M.α*M.β^2*M.γ^3 + 464*M.α*M.β*M.γ^4*m^2 + 3888*M.α*M.β*M.γ^4*m + 7376*M.α*M.β*M.γ^4 + 224*M.α*M.γ^5*m^2 + 1920*M.α*M.γ^5*m + 3904*M.α*M.γ^5 + 16*M.β^3*M.γ^3*m^2 + 96*M.β^3*M.γ^3*m + 80*M.β^3*M.γ^3 + 64*M.β^2*M.γ^4*m^2 + 448*M.β^2*M.γ^4*m + 640*M.β^2*M.γ^4 + 76*M.β*M.γ^5*m^2 + 584*M.β*M.γ^5*m + 1020*M.β*M.γ^5 + 28*M.γ^6*m^2 + 232*M.γ^6*m + 460*M.γ^6) / (M.b * M.Psi 1 ^ 2 * M.Psi 2 ^ 2) := by
    unfold Model.W Model.WI Model.WJ Model.A1 Model.A2 Model.B1 Model.B0
    rw [eq_div_iff (by positivity)]
    field_simp
    unfold Model.Psi
    rw [hm]
    ring
  have : 0 < M.W 1 - M.W 2 := by rw [key]; positivity
  linarith
