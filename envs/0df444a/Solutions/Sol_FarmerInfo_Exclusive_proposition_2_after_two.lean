-- Prove2me | solution 1 for FarmerInfo.Exclusive.proposition_2_after_two
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T22:16:37.757996+00:00
-- url     : https://prove2.me/submissions/a0ec6fb0-3ee2-4330-a8e4-379567c24969

import Mathlib
import Definitions.Def_FarmerInfo_Exclusive_Setting

open MeasureTheory Finset FarmerInfo.Exclusive

namespace FarmerP2AfterTwo

def Rpart0 (a b c m p q : ℝ) : ℝ :=
  256*a^6*p*q + 512*a^6*p + 512*a^6*q + 768*a^6 + 768*a^5*b*p*q + 1536*a^5*b*p + 1536*a^5*b*q + 2304*a^5*b + 384*a^5*c*m*p*q + 896*a^5*c*m*p + 896*a^5*c*m*q + 1920*a^5*c*m + 2176*a^5*c*p*q + 4736*a^5*c*p + 4736*a^5*c*q + 8832*a^5*c + 768*a^4*b^2*p*q + 1536*a^4*b^2*p + 1536*a^4*b^2*q + 2304*a^4*b^2 + 768*a^4*b*c*m*p*q + 1856*a^4*b*c*m*p + 1856*a^4*b*c*m*q + 3968*a^4*b*c*m + 4544*a^4*b*c*p*q + 10112*a^4*b*c*p + 10112*a^4*b*c*q + 18496*a^4*b*c + 128*a^4*c^2*m^2*p*q + 320*a^4*c^2*m^2*p + 320*a^4*c^2*m^2*q + 768*a^4*c^2*m^2 + 1920*a^4*c^2*m*p*q + 4608*a^4*c^2*m*p + 4608*a^4*c^2*m*q + 10368*a^4*c^2*m + 6272*a^4*c^2*p*q + 14272*a^4*c^2*p + 14272*a^4*c^2*q + 29184*a^4*c^2

def Rpart1 (a b c m p q : ℝ) : ℝ :=
  256*a^3*b^3*p*q + 512*a^3*b^3*p + 512*a^3*b^3*q + 768*a^3*b^3 + 384*a^3*b^2*c*m*p*q + 1024*a^3*b^2*c*m*p + 1024*a^3*b^2*c*m*q + 2176*a^3*b^2*c*m + 2560*a^3*b^2*c*p*q + 6016*a^3*b^2*c*p + 6016*a^3*b^2*c*q + 10496*a^3*b^2*c + 128*a^3*b*c^2*m^2*p*q + 384*a^3*b*c^2*m^2*p + 384*a^3*b*c^2*m^2*q + 1024*a^3*b*c^2*m^2 + 2304*a^3*b*c^2*m*p*q + 6144*a^3*b*c^2*m*p + 6144*a^3*b*c^2*m*q + 14464*a^3*b*c^2*m + 8192*a^3*b*c^2*p*q + 19968*a^3*b*c^2*p + 19968*a^3*b*c^2*q + 40960*a^3*b*c^2 + 256*a^3*c^3*m^2*p*q + 640*a^3*c^3*m^2*p + 640*a^3*c^3*m^2*q + 1536*a^3*c^3*m^2 + 2880*a^3*c^3*m*p*q + 6976*a^3*c^3*m*p + 6976*a^3*c^3*m*q + 15936*a^3*c^3*m + 7744*a^3*c^3*p*q + 17984*a^3*c^3*p + 17984*a^3*c^3*q + 38208*a^3*c^3 + 64*a^2*b^3*c*m*p + 64*a^2*b^3*c*m*q + 128*a^2*b^3*c*m + 192*a^2*b^3*c*p*q

def Rpart2 (a b c m p q : ℝ) : ℝ :=
  640*a^2*b^3*c*p + 640*a^2*b^3*c*q + 832*a^2*b^3*c + 64*a^2*b^2*c^2*m^2*p + 64*a^2*b^2*c^2*m^2*q + 256*a^2*b^2*c^2*m^2 + 384*a^2*b^2*c^2*m*p*q + 1600*a^2*b^2*c^2*m*p + 1600*a^2*b^2*c^2*m*q + 4224*a^2*b^2*c^2*m + 1920*a^2*b^2*c^2*p*q + 5952*a^2*b^2*c^2*p + 5952*a^2*b^2*c^2*q + 12032*a^2*b^2*c^2 + 176*a^2*b*c^3*m^2*p*q + 544*a^2*b*c^3*m^2*p + 544*a^2*b*c^3*m^2*q + 1488*a^2*b*c^3*m^2 + 2144*a^2*b*c^3*m*p*q + 6096*a^2*b*c^3*m*p + 6096*a^2*b*c^3*m*q + 15168*a^2*b*c^3*m + 6048*a^2*b*c^3*p*q + 15872*a^2*b*c^3*p + 15872*a^2*b*c^3*q + 35040*a^2*b*c^3 + 192*a^2*c^4*m^2*p*q + 480*a^2*c^4*m^2*p + 480*a^2*c^4*m^2*q + 1152*a^2*c^4*m^2 + 1920*a^2*c^4*m*p*q + 4672*a^2*c^4*m*p + 4672*a^2*c^4*m*q + 10752*a^2*c^4*m + 4688*a^2*c^4*p*q + 11008*a^2*c^4*p + 11008*a^2*c^4*q + 23856*a^2*c^4 + 64*a*b^3*c^2*m*p + 64*a*b^3*c^2*m*q

def Rpart3 (a b c m p q : ℝ) : ℝ :=
  128*a*b^3*c^2*m + 256*a*b^3*c^2*p + 256*a*b^3*c^2*q + 256*a*b^3*c^2 + 64*a*b^2*c^3*m^2*p + 64*a*b^2*c^3*m^2*q + 288*a*b^2*c^3*m^2 + 96*a*b^2*c^3*m*p*q + 800*a*b^2*c^3*m*p + 800*a*b^2*c^3*m*q + 2720*a*b^2*c^3*m + 416*a*b^2*c^3*p*q + 2144*a*b^2*c^3*p + 2144*a*b^2*c^3*q + 5440*a*b^2*c^3 + 80*a*b*c^4*m^2*p*q + 256*a*b*c^4*m^2*p + 256*a*b*c^4*m^2*q + 720*a*b*c^4*m^2 + 800*a*b*c^4*m*p*q + 2416*a*b*c^4*m*p + 2416*a*b*c^4*m*q + 6304*a*b*c^4*m + 1936*a*b*c^4*p*q + 5472*a*b*c^4*p + 5472*a*b*c^4*q + 12848*a*b*c^4 + 64*a*c^5*m^2*p*q + 160*a*c^5*m^2*p + 160*a*c^5*m^2*q + 384*a*c^5*m^2 + 600*a*c^5*m*p*q + 1464*a*c^5*m*p + 1464*a*c^5*m*q + 3384*a*c^5*m + 1384*a*c^5*p*q + 3272*a*c^5*p + 3272*a*c^5*q + 7176*a*c^5 + 16*b^3*c^3*m^2

def Rpart4 (a b c m p q : ℝ) : ℝ :=
  96*b^3*c^3*m + 80*b^3*c^3 + 16*b^2*c^4*m^2*p + 16*b^2*c^4*m^2*q + 80*b^2*c^4*m^2 + 128*b^2*c^4*m*p + 128*b^2*c^4*m*q + 576*b^2*c^4*m + 240*b^2*c^4*p + 240*b^2*c^4*q + 880*b^2*c^4 + 12*b*c^5*m^2*p*q + 40*b*c^5*m^2*p + 40*b*c^5*m^2*q + 116*b*c^5*m^2 + 104*b*c^5*m*p*q + 336*b*c^5*m*p + 336*b*c^5*m*q + 920*b*c^5*m + 220*b*c^5*p*q + 680*b*c^5*p + 680*b*c^5*q + 1700*b*c^5 + 8*c^6*m^2*p*q + 20*c^6*m^2*p + 20*c^6*m^2*q + 48*c^6*m^2 + 72*c^6*m*p*q + 176*c^6*m*p + 176*c^6*m*q + 408*c^6*m + 160*c^6*p*q + 380*c^6*p + 380*c^6*q + 840*c^6

end FarmerP2AfterTwo

open FarmerP2AfterTwo in
set_option maxHeartbeats 4000000 in
theorem solution (M : Model) (hM : M.Standing) :
    M.Omega_n 2 < 0 ∧
      StrictAntiOn M.W (Set.Icc (2 : ℝ) (M.n : ℝ)) := by
  obtain ⟨hn, ha, hb, hα, hβ, hγ⟩ := hM
  have hn' : (4 : ℝ) ≤ M.n := by exact_mod_cast hn
  obtain ⟨m, hm0, hm⟩ : ∃ m : ℝ, 0 ≤ m ∧ (M.n : ℝ) = m + 4 := ⟨(M.n : ℝ) - 4, by linarith, by ring⟩
  constructor
  · have key : M.Omega_n 2 = -(4 * M.β * (16*M.α^4 + 32*M.α^3*M.β + 32*M.α^3*M.γ*m + 136*M.α^3*M.γ + 16*M.α^2*M.β^2 + 32*M.α^2*M.β*M.γ*m + 140*M.α^2*M.β*M.γ + 48*M.α^2*M.γ^2*m + 180*M.α^2*M.γ^2 + 4*M.α*M.β^2*M.γ + 30*M.α*M.β*M.γ^2*m + 100*M.α*M.β*M.γ^2 + 24*M.α*M.γ^3*m + 86*M.α*M.γ^3 + 2*M.β^2*M.γ^2*m + 2*M.β^2*M.γ^2 + 7*M.β*M.γ^3*m + 19*M.β*M.γ^3 + 4*M.γ^4*m + 14*M.γ^4)) := by
      unfold Model.Omega_n
      simp only [hm]
      ring
    rw [key]
    have : 0 < 4 * M.β * (16*M.α^4 + 32*M.α^3*M.β + 32*M.α^3*M.γ*m + 136*M.α^3*M.γ + 16*M.α^2*M.β^2 + 32*M.α^2*M.β*M.γ*m + 140*M.α^2*M.β*M.γ + 48*M.α^2*M.γ^2*m + 180*M.α^2*M.γ^2 + 4*M.α*M.β^2*M.γ + 30*M.α*M.β*M.γ^2*m + 100*M.α*M.β*M.γ^2 + 24*M.α*M.γ^3*m + 86*M.α*M.γ^3 + 2*M.β^2*M.γ^2*m + 2*M.β^2*M.γ^2 + 7*M.β*M.γ^3*m + 19*M.β*M.γ^3 + 4*M.γ^4*m + 14*M.γ^4) := by positivity
    linarith
  · intro s hs t ht hst
    obtain ⟨p, hp0, rfl⟩ : ∃ p : ℝ, 0 ≤ p ∧ s = p + 2 := ⟨s - 2, by linarith [hs.1], by ring⟩
    obtain ⟨q, hq0, rfl⟩ : ∃ q : ℝ, 0 ≤ q ∧ t = q + 2 := ⟨t - 2, by linarith [ht.1], by ring⟩
    have hpq : 0 < q - p := by linarith
    have h1 : 0 < M.Psi (p + 2) := by unfold Model.Psi; positivity
    have h2 : 0 < M.Psi (q + 2) := by unfold Model.Psi; positivity
    have hR : 0 < Rpart0 M.α M.β M.γ m p q + Rpart1 M.α M.β M.γ m p q + Rpart2 M.α M.β M.γ m p q + Rpart3 M.α M.β M.γ m p q + Rpart4 M.α M.β M.γ m p q := by
      unfold Rpart0 Rpart1 Rpart2 Rpart3 Rpart4
      positivity
    have key : M.W (p + 2) - M.W (q + 2) = M.β * (q - p) * (Rpart0 M.α M.β M.γ m p q + Rpart1 M.α M.β M.γ m p q + Rpart2 M.α M.β M.γ m p q + Rpart3 M.α M.β M.γ m p q + Rpart4 M.α M.β M.γ m p q) /
        (M.b * M.Psi (p + 2) ^ 2 * M.Psi (q + 2) ^ 2) := by
      unfold Model.W Model.WI Model.WJ Model.A1 Model.A2 Model.B1 Model.B0
      rw [eq_div_iff (by positivity)]
      field_simp
      unfold Model.Psi Rpart0 Rpart1 Rpart2 Rpart3 Rpart4
      rw [hm]
      ring
    have : 0 < M.W (p + 2) - M.W (q + 2) := by rw [key]; positivity
    linarith
