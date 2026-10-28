-- Prove2me | solution 1 for D1Bound5.frontier_scalar_reduction
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-10-24T04:31:28.791711+00:00
-- url     : https://prove2.me/submissions/5a0589cd-204e-4fdc-b621-3bca108b0312

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5







/-- Division-free form of the manuscript normalization: after setting
τ=T/(ABS), the determinant bound becomes τ≤2Kτ²+LPτ+J. -/
theorem _root_.solution (A B C T alpha beta K L Q : ℝ)
    (ha : 0 < alpha) (hb : 0 < beta)
    (hA : alpha ≤ A) (hB : beta ≤ B) (hC : beta ≤ C) (hT : 0 ≤ T)
    (hK : 0 ≤ K) (hL : 0 ≤ L) (hQ : 0 ≤ Q)
    (hupper : A*B*C*T ≤
      2*K*(A^2+B^2+C^2+T^2)+L*(A*B+A*C+A*T+B*C+B*T+C*T)+Q) :
    let tau := T/(A*B*C)
    tau ≤ 2*K*tau^2+L*(2/(alpha*beta)+1/beta^2)*tau+
      (2*K*(2/(alpha^2*beta^2)+1/beta^4)+
       L*(1/(alpha^2*beta^2)+2/(alpha*beta^3))+Q/(alpha^2*beta^4)) := by
  have hA0 : 0 < A := ha.trans_le hA
  have hB0 : 0 < B := hb.trans_le hB
  have hC0 : 0 < C := hb.trans_le hC
  have hAn : A ≠ 0 := ne_of_gt hA0
  have hBn : B ≠ 0 := ne_of_gt hB0
  have hCn : C ≠ 0 := ne_of_gt hC0
  let tau := T/(A*B*C)
  have htau : 0 ≤ tau := div_nonneg hT (by positivity)
  have hdiag : 1/(B^2*C^2)+1/(A^2*C^2)+1/(A^2*B^2) ≤
      1/beta^4+1/(alpha^2*beta^2)+1/(alpha^2*beta^2) := by
    have h1 : 1/(B^2*C^2) ≤ 1/(beta^2*beta^2) := by gcongr
    have h2 : 1/(A^2*C^2) ≤ 1/(alpha^2*beta^2) := by gcongr
    have h3 : 1/(A^2*B^2) ≤ 1/(alpha^2*beta^2) := by gcongr
    have heq : beta^2*beta^2 = beta^4 := by ring
    rw [heq] at h1
    linarith only [h1,h2,h3]
  have hcross : 1/(B*C)+1/(A*C)+1/(A*B) ≤
      1/beta^2+1/(alpha*beta)+1/(alpha*beta) := by
    have h1 : 1/(B*C) ≤ 1/(beta*beta) := by gcongr
    have h2 : 1/(A*C) ≤ 1/(alpha*beta) := by gcongr
    have h3 : 1/(A*B) ≤ 1/(alpha*beta) := by gcongr
    rw [← pow_two] at h1
    linarith only [h1,h2,h3]
  have hpair : 1/(A*B*C^2)+1/(A*B^2*C)+1/(A^2*B*C) ≤
      1/(alpha*beta^3)+1/(alpha*beta^3)+1/(alpha^2*beta^2) := by
    have h1 : 1/(A*B*C^2) ≤ 1/(alpha*beta*beta^2) := by gcongr
    have h2 : 1/(A*B^2*C) ≤ 1/(alpha*beta^2*beta) := by gcongr
    have h3 : 1/(A^2*B*C) ≤ 1/(alpha^2*beta*beta) := by gcongr
    have heq1 : alpha*beta*beta^2 = alpha*beta^3 := by ring
    have heq2 : alpha*beta^2*beta = alpha*beta^3 := by ring
    have heq3 : alpha^2*beta*beta = alpha^2*beta^2 := by ring
    rw [heq1] at h1
    rw [heq2] at h2
    rw [heq3] at h3
    linarith only [h1,h2,h3]
  have hquartic : 1/(A^2*B^2*C^2) ≤ 1/(alpha^2*beta^4) := by
    have h : 1/(A^2*B^2*C^2) ≤ 1/(alpha^2*beta^2*beta^2) := by gcongr
    have heq : alpha^2*beta^2*beta^2 = alpha^2*beta^4 := by ring
    simpa only [heq] using h
  have hnormal : tau ≤
      (2*K*(A^2+B^2+C^2+T^2)+L*(A*B+A*C+A*T+B*C+B*T+C*T)+Q)/(A^2*B^2*C^2) := by
    calc
      tau = (A*B*C*T)/(A^2*B^2*C^2) := by
        change T/(A*B*C) = (A*B*C*T)/(A^2*B^2*C^2)
        field_simp [hAn, hBn, hCn] <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right hupper (by positivity : 0 ≤ A^2*B^2*C^2)
  change tau ≤ _
  calc
    tau ≤ _ := hnormal
    _ = 2*K*tau^2+
        2*K*(1/(B^2*C^2)+1/(A^2*C^2)+1/(A^2*B^2))+
        L*tau*(1/(B*C)+1/(A*C)+1/(A*B))+
        L*(1/(A*B*C^2)+1/(A*B^2*C)+1/(A^2*B*C))+Q*(1/(A^2*B^2*C^2)) := by
      dsimp [tau]
      field_simp [hAn, hBn, hCn]
      ring
    _ ≤ 2*K*tau^2+
        2*K*(1/beta^4+1/(alpha^2*beta^2)+1/(alpha^2*beta^2))+
        L*tau*(1/beta^2+1/(alpha*beta)+1/(alpha*beta))+
        L*(1/(alpha*beta^3)+1/(alpha*beta^3)+1/(alpha^2*beta^2))+Q*(1/(alpha^2*beta^4)) := by
      gcongr
    _ = _ := by ring



end D1Bound5
end
