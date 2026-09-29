-- Prove2me | solution 1 for CohCarrier.iDeg_diamondRaw_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d9543aac-abfc-5097-92e9-01bc0827d7ac

import Definitions.Def_CohCarrier_Level
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_iDeg_diamondRaw_comm

set_option autoImplicit false

namespace CohL2
namespace S1

open CongruenceSubgroup Matrix.SpecialLinearGroup CohCarrier
open scoped MatrixGroups

theorem conjLowerMat_one' (d : ℕ) (h : (d : ℤ) ∣ (1 : SL(2, ℤ)) 1 0) : conjLowerMat d 1 h = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [conjLowerMat]

theorem conjLowerMat_inv (d : ℕ) (A : SL(2, ℤ)) (hA : (d : ℤ) ∣ A 1 0) (hAi : (d : ℤ) ∣ (A⁻¹ : SL(2, ℤ)) 1 0) :
    conjLowerMat d A⁻¹ hAi = (conjLowerMat d A hA)⁻¹ := by
  have h1 : (d : ℤ) ∣ (A * A⁻¹ : SL(2, ℤ)) 1 0 := by rw [mul_inv_cancel]; simp
  have hmul := conjLowerMat_mul d A A⁻¹ hA hAi h1
  have hone : conjLowerMat d (A * A⁻¹) h1 = 1 := by
    have : ∀ (h' : (d : ℤ) ∣ (1 : SL(2, ℤ)) 1 0), conjLowerMat d (A * A⁻¹) h1 = conjLowerMat d 1 h' := by
      intro h'; congr 1; exact mul_inv_cancel A
    rw [this (by simp), conjLowerMat_one']
  rw [hone] at hmul
  exact (eq_inv_of_mul_eq_one_right hmul.symm)

end CohL2.S1

open CohL2.S1 CongruenceSubgroup CohCarrier in
open scoped MatrixGroups in
theorem solution
    {M M' : ℕ} [NeZero M] [NeZero M'] {H : Subgroup (ZMod M)ˣ} {H' : Subgroup (ZMod M')ˣ} {d : ℕ} [NeZero d]
    (h : LevelLE M M' H H' d) {A : Type} [AddCommGroup A] (σ' : Gamma0 M')
    (hd : (d : ℤ) ∣ (σ' : SL(2, ℤ)) 1 0) (σ : Gamma0 M) (hσ : (σ : SL(2, ℤ)) = conjLowerMat d (σ' : SL(2, ℤ)) hd)
    (φ : H1 M H A) :
    iDeg' M M' H H' d A h (diamondRaw M H A σ φ) = diamondRaw M' H' A σ' (iDeg' M M' H H' d A h φ) := by
  refine AddMonoidHom.ext fun a => ?_
  set γ' : ↥(GammaH M' H') := Additive.toMul a with hγ'
  show φ (Additive.ofMul (conjHom M H σ (iotaDeg M M' H H' d h γ'))) =
    φ (Additive.ofMul (iotaDeg M M' H H' d h (conjHom M' H' σ' γ')))
  congr 2
  apply Subtype.ext
  show (σ : SL(2, ℤ)) * conjLowerMat d (γ' : SL(2, ℤ)) (h.dvd_entry γ') * (σ : SL(2, ℤ))⁻¹ =
    conjLowerMat d ((σ' : SL(2, ℤ)) * (γ' : SL(2, ℤ)) * (σ' : SL(2, ℤ))⁻¹) (h.dvd_entry (conjHom M' H' σ' γ'))
  have hσγ : (d : ℤ) ∣ ((σ' : SL(2, ℤ)) * (γ' : SL(2, ℤ))) 1 0 := by
    have e : ((σ' : SL(2, ℤ)) * (γ' : SL(2, ℤ))) 1 0 =
        (σ' : SL(2, ℤ)) 1 0 * (γ' : SL(2, ℤ)) 0 0 + (σ' : SL(2, ℤ)) 1 1 * (γ' : SL(2, ℤ)) 1 0 := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hd _) (dvd_mul_of_dvd_right (h.dvd_entry γ') _)
  have hσi : (d : ℤ) ∣ ((σ' : SL(2, ℤ))⁻¹ : SL(2, ℤ)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact (dvd_neg).mpr hd
  rw [conjLowerMat_mul d _ _ hσγ hσi, conjLowerMat_mul d _ _ hd (h.dvd_entry γ'), conjLowerMat_inv d _ hd hσi, hσ]

end S_CohCarrier_iDeg_diamondRaw_comm
end P2MW
export P2MW.S_CohCarrier_iDeg_diamondRaw_comm (solution)
