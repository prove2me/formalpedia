-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.p3aOfParts_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:40:59.5238+00:00
-- url     : https://prove2.me/submissions/34f070ed-9c83-467d-9817-eeff385d5de2

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremsAssembly
import Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_thGrid_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_sum_abs_coProd
import Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_co_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
theorem _root_.solution : LeadingBlockRecursiveBoundFromComponents := by
  intro V _ _ K d grid q x nn w e t X0 XK ρ E wt bw Rw ZZ hg he ht hpos hTop hFS hR hZ hwt hbw
  obtain ⟨hρ, -, hE⟩ := hFS
  unfold LeadingCoefficientVectorIdentity at hTop
  have htn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  have he1 : ‖e‖ = 1 := by rcases he with h | h <;> simp [h]
  have h1 : ‖t‖⁻¹ ^ K * ‖X0‖ ≤ ∑ j, |coProd grid j| * ‖XK j‖ := by
    have : ‖(e / t) ^ K • X0‖ = ‖t‖⁻¹ ^ K * ‖X0‖ := by rw [norm_smul, norm_pow, norm_div, he1, one_div]
    rw [← this, hTop]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have hCS : (∑ j, |coProd grid j| * ‖XK j‖) ^ 2 ≤
      (∑ j, |coProd grid j|) * ∑ j, |coProd grid j| * ‖XK j‖ ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => Real.sqrt |coProd grid j|)
      (fun j => Real.sqrt |coProd grid j| * ‖XK j‖)
    have hs : ∀ j, Real.sqrt |coProd grid j| * (Real.sqrt |coProd grid j| * ‖XK j‖) = |coProd grid j| * ‖XK j‖ :=
      fun j => by rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg _)]
    have hs2 : ∀ j, Real.sqrt |coProd grid j| ^ 2 = |coProd grid j| := fun j => Real.sq_sqrt (abs_nonneg _)
    have hs3 : ∀ j, (Real.sqrt |coProd grid j| * ‖XK j‖) ^ 2 = |coProd grid j| * ‖XK j‖ ^ 2 :=
      fun j => by rw [mul_pow, hs2]
    simp only [hs, hs2, hs3] at h
    exact h
  have hnn : ∀ j, (∏ b, nn (grid b (j b))) ≤ (∏ _b : Fin K, (Rw * ZZ)) * ∏ b, ρ b j := by
    intro j
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod (fun b _ => (hpos b (j b)).2.1.le)
    intro b _
    have hq := (hpos b (j b)).1
    have hnb := (hpos b (j b)).2.1
    have hx0 : 0 < |x (grid b (j b) + 1)| := abs_pos.mpr (hpos b (j b)).2.2
    have h1 := hR b j
    have h2 := hZ b (j b)
    have hZ0 : 0 ≤ ZZ := le_trans (div_nonneg (mul_nonneg hnb.le hx0.le) hq.le) h2
    have hqne := hq.ne'
    have hxne := hx0.ne'
    calc nn (grid b (j b)) = (nn (grid b (j b)) * |x (grid b (j b) + 1)| / q (grid b (j b))) *
          (q (grid b (j b)) / |x (grid b (j b) + 1)|) := by field_simp
      _ ≤ ZZ * (Rw * ρ b j) := mul_le_mul h2 h1 (div_nonneg hq.le hx0.le) hZ0
      _ = Rw * ZZ * ρ b j := by ring
  have hn0 : ∀ j, 0 < nnProd nn 0 grid j := fun j =>
    Finset.prod_pos fun b _ => by simpa using (hpos b (j b)).2.1
  have hP0 : 0 < ∏ _b : Fin K, (Rw * ZZ) := by
    have h := hnn (fun _ => 0)
    have h1 : 0 < ∏ b, nn (grid b ((fun _ => (0 : Fin (d + 1))) b)) :=
      Finset.prod_pos fun b _ => (hpos b _).2.1
    have h2 : 0 < ∏ b, ρ b (fun _ => 0) := Finset.prod_pos fun b _ => hρ b _
    by_contra hc
    have hc' := not_lt.mp hc
    nlinarith
  have hE0 : ∀ j, 0 ≤ E j := fun j =>
    le_trans (mul_nonneg (Finset.prod_pos fun b _ => hρ b j).le (sq_nonneg _)) (hE j)
  have hXK : ∀ j, ‖XK j‖ ^ 2 ≤ (∏ _b : Fin K, (Rw * ZZ)) * (E j / nnProd nn 0 grid j) := by
    intro j
    have hnn' : nnProd nn 0 grid j ≤ (∏ _b : Fin K, (Rw * ZZ)) * ∏ b, ρ b j := by
      simpa [nnProd] using hnn j
    rw [mul_div_assoc', le_div_iff₀ (hn0 j)]
    calc ‖XK j‖ ^ 2 * nnProd nn 0 grid j
        ≤ ‖XK j‖ ^ 2 * ((∏ _b : Fin K, (Rw * ZZ)) * ∏ b, ρ b j) :=
          mul_le_mul_of_nonneg_left hnn' (sq_nonneg _)
      _ = (∏ _b : Fin K, (Rw * ZZ)) * ((∏ b, ρ b j) * ‖XK j‖ ^ 2) := by ring
      _ ≤ (∏ _b : Fin K, (Rw * ZZ)) * E j := mul_le_mul_of_nonneg_left (hE j) hP0.le
  have hth := Formalism.FourierDecayAlt.P.SecondPolynomialClauses.co_eq grid hg
  have step : (‖t‖⁻¹ ^ K) ^ 2 * ‖X0‖ ^ 2 ≤ (∏ a, cg grid a) ^ 2 *
      ((∏ _b : Fin K, (Rw * ZZ)) * ∑ j, F7.thGrid grid j * (E j / nnProd nn 0 grid j)) := by
    have hm0 : 0 ≤ ‖t‖⁻¹ ^ K * ‖X0‖ := by positivity
    calc (‖t‖⁻¹ ^ K) ^ 2 * ‖X0‖ ^ 2 = (‖t‖⁻¹ ^ K * ‖X0‖) ^ 2 := by ring
      _ ≤ (∑ j, |coProd grid j| * ‖XK j‖) ^ 2 := pow_le_pow_left₀ hm0 h1 2
      _ ≤ (∑ j, |coProd grid j|) * ∑ j, |coProd grid j| * ‖XK j‖ ^ 2 := hCS
      _ = (∏ a, cg grid a) * ∑ j, (∏ a, cg grid a) * F7.thGrid grid j * ‖XK j‖ ^ 2 := by
          rw [sum_abs_coProd]; simp only [hth]
      _ = (∏ a, cg grid a) ^ 2 * ∑ j, F7.thGrid grid j * ‖XK j‖ ^ 2 := by
          rw [sq, mul_assoc]; congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
      _ ≤ (∏ a, cg grid a) ^ 2 * ∑ j, F7.thGrid grid j *
            ((∏ _b : Fin K, (Rw * ZZ)) * (E j / nnProd nn 0 grid j)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hXK j) (thGrid_nonneg grid j))
            (sq_nonneg _)
      _ = (∏ a, cg grid a) ^ 2 *
            ((∏ _b : Fin K, (Rw * ZZ)) * ∑ j, F7.thGrid grid j * (E j / nnProd nn 0 grid j)) := by
          congr 1; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; ring
  have hz : ‖t‖ ^ (-(2 * K : ℤ)) = (‖t‖⁻¹ ^ K) ^ 2 := by
    rw [← pow_mul, inv_pow, ← zpow_natCast, ← zpow_neg]; congr 1; push_cast; ring
  have hprod : ∏ a, (cg grid a ^ 2 * Rw * ZZ) = (∏ a, cg grid a) ^ 2 * ∏ _b : Fin K, (Rw * ZZ) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]; apply Finset.prod_congr rfl; intro a _; ring
  have hsum : ∑ j, F7.thGrid grid j * (wt ^ 2 * E j / (bw * nnProd nn 0 grid j)) =
      wt ^ 2 / bw * ∑ j, F7.thGrid grid j * (E j / nnProd nn 0 grid j) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _; rw [mul_div_mul_comm]; ring
  rw [hz, hprod, hsum]
  calc (‖t‖⁻¹ ^ K) ^ 2 * (wt ^ 2 * ‖X0‖ ^ 2 / bw) = wt ^ 2 / bw * ((‖t‖⁻¹ ^ K) ^ 2 * ‖X0‖ ^ 2) := by ring
    _ ≤ wt ^ 2 / bw * ((∏ a, cg grid a) ^ 2 *
          ((∏ _b : Fin K, (Rw * ZZ)) * ∑ j, F7.thGrid grid j * (E j / nnProd nn 0 grid j))) :=
        mul_le_mul_of_nonneg_left step (div_nonneg (sq_nonneg _) hbw.le)
    _ = (∏ a, cg grid a) ^ 2 * (∏ _b : Fin K, (Rw * ZZ)) *
          (wt ^ 2 / bw * ∑ j, F7.thGrid grid j * (E j / nnProd nn 0 grid j)) := by ring
end Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
