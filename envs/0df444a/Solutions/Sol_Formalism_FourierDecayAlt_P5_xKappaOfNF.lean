-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P5.xKappaOfNF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:12:52.164535+00:00
-- url     : https://prove2.me/submissions/d5b04e6a-0d7e-478d-9326-7a311444484f

import Definitions.Def_Formalism_HermitianCurvature_TopDensNonnegOfKappa
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SignedCoordinateEqSignSmul
import Theorems.Thm_Formalism_FourierDecayAlt_P5_signed_coordinate_eq_sign_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P5
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd
namespace Formalism.FourierDecayAlt.P5
theorem _root_.solution : XKappaOfNF := by
  intro hNF hPos Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 hD
  obtain ⟨hPl, -, hL, hQQ, -, hinv, -, hLS⟩ := hD
  obtain ⟨d, hdL, hdS, hdR, hdQ⟩ := hNF Wp Wq P z z' π π' hPl X
  have hfn : ∀ i j : Fin 6,
      (∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' i x.2 * fnVal P.k P.r z z' j x.2 = 1) →
      X.fn i * X.fn j = 1 := by
    intro i j hij
    refine LinearMap.ext fun Φ => Subtype.ext (funext fun c => funext fun g => ?_)
    rw [Module.End.mul_apply, Module.End.one_apply]
    by_cases hx : (c, g) ∈ DomR P.k P.r z z'
    · have e1 := X.fn_apply i (X.fn j Φ) (c, g) hx
      have e2 := X.fn_apply j Φ (c, g) hx
      dsimp only at e1 e2
      rw [e1, e2, smul_smul, hij (c, g) hx, one_smul]
    · have e1 := (X.fn i (X.fn j Φ)).2.1 (c, g) hx
      have e2 := Φ.2.1 (c, g) hx
      dsimp only at e1 e2
      rw [e1, e2]
  have hG : ∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' 5 x.2 * fnVal P.k P.r z z' 4 x.2 = 1 := by
    intro x hx
    simp only [fnVal]
    exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hx.2.2.ne')
  have hG' : ∀ x ∈ DomR P.k P.r z z', fnVal P.k P.r z z' 4 x.2 * fnVal P.k P.r z z' 5 x.2 = 1 := by
    intro x hx
    simp only [fnVal]
    exact mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hx.2.2.ne')
  have hGinv : L.GGi * L.GG = 1 := by
    rw [hL.2.2.2.2.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine Prod.ext ?_ ?_
    · show X.fn 5 * X.fn 4 = 1
      exact hfn 5 4 hG
    · show MulOpposite.op (X.fn 5) * MulOpposite.op (X.fn 4) = MulOpposite.op 1
      rw [← MulOpposite.op_mul, hfn 4 5 hG']
  have hGG : L.GG = d.L.GG := hL.2.2.2.2.2.2.2.2.2.2.1.trans hdL.2.2.2.2.2.2.2.2.2.2.1.symm
  have hx : ∀ Y, st.x Y = d.κ fun ρ => M.x0 P l0 ρ Y := by
    intro Y
    have h1 := hLS.tau Y
    have h2 : d.QQ Y 1 1 = d.L.GG * d.x Y := by simp [NFData.QQ]
    rw [hQQ Y, hdQ Y, Matrix.smul_apply, h2, ← hGG, ← mul_smul_comm] at h1
    have h3 : st.x Y = M.sgn P l0 • d.x Y := by
      calc st.x Y = L.GGi * (L.GG * st.x Y) := by rw [← mul_assoc, hGinv, one_mul]
        _ = L.GGi * (L.GG * (M.sgn P l0 • d.x Y)) := by rw [← h1]
        _ = _ := by rw [← mul_assoc, hGinv, one_mul]
    rw [h3, NFData.x, signed_coordinate_eq_sign_smul, map_smul]
  have hxi : ∀ Y ∈ st.inv, st.xi Y = d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹ := by
    intro Y hY
    have hne : ∀ ρ, M.x0 P l0 ρ Y ≠ 0 := by
      intro ρ
      have hY' := hY
      rw [hinv] at hY'
      have e := congrFun (signed_coordinate_eq_sign_smul P l0 Y) ρ
      simp only [Pi.smul_apply, smul_eq_mul] at e
      rw [e]
      exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) (hY' ρ)
    have hprod : (d.κ fun ρ => M.x0 P l0 ρ Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹) = 1 := by
      rw [← map_mul, ← map_one d.κ]
      congr 1
      funext ρ
      simp [hne ρ]
    calc st.xi Y
        = st.xi Y * ((d.κ fun ρ => M.x0 P l0 ρ Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹)) := by
          rw [hprod, mul_one]
      _ = (st.xi Y * st.x Y) * (d.κ fun ρ => (M.x0 P l0 ρ Y)⁻¹) := by rw [hx Y, mul_assoc]
      _ = _ := by rw [(hLS.x_xi Y hY).2, one_mul]
  exact ⟨d.κ, hx, hxi, hPos Wp Wq P z z' π π' hPl X d hdL hdS hdR hdQ⟩
end Formalism.FourierDecayAlt.P5
