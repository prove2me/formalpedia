-- Prove2me | solution 1 for DyckAlgebra.DyckRepU.thetaDGamma_eq_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-23T23:49:41.475009+00:00
-- url     : https://prove2.me/submissions/9adcf4f2-3f68-4321-8eae-f4ff94ad38e0

import Definitions.Def_RequestProject_Aqt_PreserveKernel
import Definitions.Def_RequestProject_Aqt_DGamma
set_option autoImplicit true
open DyckAlgebra
open DyckAlgebra.DyckRepU
variable {𝕜 : Type*} [Field 𝕜] {q cQ2 : 𝕜} (ρ : DyckRepU 𝕜 q cQ2)


theorem solution (γ : List ℕ) (U Uinv : ρ.carrier)
    (hm : U * ρ.dm = ρ.dm * U)
    (hy : U * ρ.yy 1 = ρ.Θy1 * U)
    (hz : U * ρ.zz 1 = ρ.Θz1 * U)
    (hp : U * ρ.dp = ρ.Θdp * U)
    (hright : U * Uinv = 1) :
    ρ.thetaDGamma γ = U * ρ.dGamma γ * Uinv := by
  have hc (a b c d : ρ.carrier) (hab : U * a = b * U) (hcd : U * c = d * U) : U * (a*c) = (b*d)*U := by rw [← mul_assoc, hab, mul_assoc, hcd, mul_assoc]
  have hn : U * (-ρ.yy 1) = (-ρ.Θy1) * U := by simp [hy]
  have pw (n : ℕ) : U * (-ρ.yy 1)^n = (-ρ.Θy1)^n * U := by
    induction n with
    | zero => simp
    | succ n ih => simpa only [pow_succ] using hc _ _ _ _ ih hn
  have tail (l : List ℕ) : U * ρ.dGammaTail l = ρ.thetaDGammaTail l * U := by
    induction l with
    | nil => exact hc _ _ _ _ hz hp
    | cons g gs ih => exact hc _ _ _ _ (hc _ _ _ _ hz (pw g)) ih
  have word : U * ρ.dGamma γ = ρ.thetaDGamma γ * U := by
    cases γ with
    | nil => simp [dGamma,thetaDGamma]
    | cons g gs => exact hc _ _ _ _ (hc _ _ _ _ hm (pw _)) (tail gs)
  rw [word, mul_assoc, hright, mul_one]
