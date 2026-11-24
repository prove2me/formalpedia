-- Prove2me | solution 1 for Formalism.L2.Th1.A.iSerSpec_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:32:02.915416+00:00
-- url     : https://prove2.me/submissions/23704aae-6eb9-404e-ba92-c59d0f8ff457

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_EqWSerSubst
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_apply
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_X
import Theorems.Thm_Formalism_L2_Th1_A_ISer_subHom_C
import Theorems.Thm_Formalism_L2_Th1_A_ISer_eq_wSer_subst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
open ISer
namespace Formalism.L2.Th1.A
theorem _root_.solution (hW : WSerSpec.{u}) (hF : WSerFactor.{u}) (hU : UnitSpec.{u})
    (hD : FlowU.{u}) (hN : FlowNegUW.{u}) : ISerSpec.{u} := by
  intro R _ W
  obtain ⟨hw3, -, hUx, -, -⟩ := hF R W
  obtain ⟨-, hfo, -, -, -, hq0, hqr⟩ := hU R W
  obtain ⟨hDer, hConst, hFlow, -, -, hom⟩ := hD R W
  have hw0 : constantCoeff (wSer W) = 0 := (hW R W).1.1
  set r : R⟦X⟧ := invOfUnit (iDen W) (-1) with hr
  have hq : iDen W = -1 + C W.a₁ * X + C W.a₃ * wSer W := rfl
  have hi : iSer W = X * r := rfl
  have hr0 : constantCoeff r = -1 := by
    rw [hr, constantCoeff_invOfUnit]; simp
  have hi0 : constantCoeff (iSer W) = 0 := by rw [hi]; simp
  have hi1 : coeff 1 (iSer W) = -1 := by
    rw [hi, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
      hr0]

  have hneg := hN R⟦X⟧ (curveS W) (D W) X (wSer W) r hDer hConst hFlow
    (by
      have : (-1 + (curveS W).a₁ * X + (curveS W).a₃ * wSer W : R⟦X⟧) = iDen W := rfl
      rw [this, mul_comm]; exact hqr)
  obtain ⟨hE, hDi, -⟩ := hneg
  have hwi : (wSer W).subst (iSer W) = wSer W * r := by
    symm
    apply eq_wSer_subst hW W (iSer W) (wSer W * r) hi0 (by simp [hw0])
    exact hE
  set φ := subHom (iSer W) hi0 with hφ
  have φa : ∀ f, f.subst (iSer W) = φ f := fun f => (subHom_apply _ _ f).symm
  have φX : φ X = X * r := subHom_X _ _
  have φC : ∀ a, φ (C a) = C a := subHom_C _ _
  have φw : φ (wSer W) = wSer W * r := by rw [← φa, hwi]
  have φq : φ (iDen W) = r := by
    rw [hq]
    simp only [map_add, map_mul, map_neg, map_one, φX, φC, φw]
    rw [hq] at hqr
    linear_combination hqr
  have φr : φ r = iDen W := by
    have h1 : φ (iDen W) * φ r = 1 := by rw [← map_mul, hqr, map_one]
    rw [φq] at h1
    linear_combination (iDen W) * h1 - (φ r) * hqr
  have hii : φ (iSer W) = X := by
    rw [hi, map_mul, φX, φr]
    linear_combination X * hqr
  have φU : φ (wU W) = wU W * iDen W ^ 2 := by
    have h1 : φ (wSer W) = φ X ^ 3 * φ (wU W) := by rw [← map_pow, ← map_mul, ← hw3]
    rw [φw, φX] at h1
    have h2 : X ^ 3 * (wU W * r) = X ^ 3 * (r ^ 3 * φ (wU W)) := by
      linear_combination h1 - r * hw3
    have h3 := X_pow_mul_cancel h2
    linear_combination (-(iDen W) ^ 3) * h3
      + (wU W * iDen W ^ 2 - φ (wU W) * ((iDen W * r) ^ 2 + iDen W * r + 1)) * hqr
  have φx : φ (xS W) = r ^ 2 * xS W := by
    have h1 : φ (wU W) * φ (xS W) = 1 := by rw [← map_mul, hUx, map_one]
    rw [φU] at h1
    linear_combination (r ^ 2 * xS W) * h1 - φ (xS W) * (iDen W * r) ^ 2 * hUx
      - φ (xS W) * (iDen W * r + 1) * hqr
  have φfw : φ (fw W) = fwAt (curveS W) (X * r) (wSer W * r) := by
    have : fwAt (curveS W) (X * r) (wSer W * r) = 1 - C W.a₁ * (X * r) - C W.a₂ * (X * r) ^ 2
      - 2 * C W.a₃ * (wSer W * r) - 2 * C W.a₄ * (X * r) * (wSer W * r)
      - 3 * C W.a₆ * (wSer W * r) ^ 2 := rfl
    rw [this, fw]
    simp only [map_sub, map_mul, map_pow, map_one, map_ofNat, φX, φC, φw]
  have hDi' : D W (iSer W) = -φ (fw W) := by
    rw [φfw, ← hDi, hi, neg_neg]
  refine ⟨hi0, hi1, ?_, hwi, ?_, ?_, ?_, ?_⟩
  · rw [φa, hii]
  · rw [φa, φx]
  · rw [φa, yS, map_neg, φx]
    rw [hq] at hqr
    linear_combination (r ^ 2 * xS W) * hqr - r ^ 3 * C W.a₃ * xS W * hw3
      - r ^ 3 * C W.a₃ * X ^ 3 * hUx
  · rw [φa, hDi']
  · rw [φa, ← hom, hDi']
    have h1 : φ (fw W) * φ (om W) = 1 := by rw [← map_mul, hfo, map_one]
    linear_combination (-om W) * h1
end Formalism.L2.Th1.A
