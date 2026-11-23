-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.markovTerm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:42:49.158512+00:00
-- url     : https://prove2.me/submissions/5ef840be-b84f-4461-a389-05d6a2b18ff3

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_dS_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_meas_th
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_coefIntegrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_opt_delta
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A3_dsMeas
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_int_pr
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_int_pr_self
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_iterDeriv_poly
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_mkP_coeff
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_mkP_eval
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_norm_int_pr_le
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_LEx2_sq_nonneg__b7974ad0744f


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution : MarkovTerm := by
  intro hMV B S σ ε M hσ hε hL hM hW hI4 hI4' Y hY hEns p
  obtain ⟨c, hc⟩ := hI4 Y hY
  have hth : ∀ ω, 0 ≤ th ε σ (B.G ω) := fun ω =>
    Real.rpow_nonneg (div_nonneg (B.G_pos ω).le (by have := B.G_pos ω; linarith)) _
  have hd : ∀ ω k, 0 ≤ S.d Y ω k := fun ω k => (hW.2 Y hY ω k).le
  set wt : B.Ω → Bool × S.ι → ℝ := fun ω k => th ε σ (B.G ω) * S.d Y ω k with hwt
  have hwt0 : ∀ ω k, 0 ≤ wt ω k := fun ω k => mul_nonneg (hth ω) (hd ω k)
  have hwtm : ∀ k, Measurable fun ω => wt ω k := fun k => (meas_th B ε σ).mul ((hM.2.2 Y hY).1 k)
  have hsq : ∀ v : Fn B (Bool × S.ι), (fun ω => th ε σ (B.G ω) * LE.sq B (S.d Y) v ω) = LE.sq B wt v := by
    intro v; funext ω; unfold LE.sq; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; simp only [hwt]; ring
  have hmds : ∀ q k, Measurable fun ω => S.ds Y q ω k := fun q k => A3.dsMeas B S hM hI4 Y hY q k
  have hci : ∀ q, Integrable (LE.sq B wt (S.ds Y q)) B.μ := fun q => by
    rw [← hsq]; exact coefIntegrable B S σ hσ hM hW hI4 hI4' ε hε Y hY q
  have hgi : ∀ s, Integrable (LE.sq B wt (S.gs Y s)) B.μ := fun s => by
    rw [← hsq]; exact (hI4' ε hε).1 Y hY s
  have hDn : S.Dn ε σ Y p = ∫ ω, LE.sq B wt (S.ds Y p) ω ∂B.μ := by unfold Step.Dn; rw [hsq]
  have hEn : ∀ s, S.Ens ε σ Y s = ∫ ω, LE.sq B wt (S.gs Y s) ω ∂B.μ := fun s => by unfold Step.Ens; rw [hsq]
  have hD0 : 0 ≤ S.Dn ε σ Y p := by rw [hDn]; exact integral_nonneg fun ω => sq_nonneg' B wt hwt0 _ ω
  have hM0 : 0 ≤ M := by
    refine le_trans ?_ (hEns 0 (by simpa using hY))
    rw [hEn]; exact integral_nonneg fun ω => sq_nonneg' B wt hwt0 _ ω
  have hK0 : 0 ≤ 2 * ((S.r : ℝ) + 1) ^ 2 / S.L := by positivity
  have hdsq : ∀ q ω k, S.ds Y q ω k = q.factorial * (if q < S.r + 1 + 1 then c q ω k else 0) :=
    fun q ω k => dS_poly B (S.g Y) S.X (S.r + 1) c hc q ω k
  by_cases hp : p < S.r + 1 + 1
  swap
  · have : S.ds Y p = fun _ _ => 0 := by funext ω k; rw [hdsq, if_neg hp]; simp
    have h0 : S.Dn ε σ Y p = 0 := by rw [hDn, this]; simp [LE.sq]
    rw [h0]; positivity
  set w : Fn B (Bool × S.ι) := S.ds Y p with hw
  let a' : ℕ → ℂ := fun q => (∫ ω, pr B wt (S.ds Y q) w ω ∂B.μ) / q.factorial
  have hpi : ∀ q, Integrable (pr B wt (S.ds Y q) w) B.μ := fun q =>
    int_pr B wt hwt0 _ _ hwtm (hmds q) (hmds p) (hci q) (hci p)
  have hphi : ∀ s : ℝ, ∫ ω, pr B wt (S.gs Y s) w ω ∂B.μ = ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * a' q := by
    intro s
    have h1 : pr B wt (S.gs Y s) w = fun ω => ∑ q ∈ range (S.r + 1 + 1),
        (s : ℂ) ^ q * (pr B wt (S.ds Y q) w ω / q.factorial) := by
      funext ω
      unfold pr
      have hgs : ∀ k, S.gs Y s ω k = ∑ q ∈ range (S.r + 1 + 1), (s : ℂ) ^ q * (S.ds Y q ω k / q.factorial) := by
        intro k
        show conjS B (S.g Y) S.X s ω k = _
        rw [hc s ω k]
        apply Finset.sum_congr rfl
        intro q hq
        rw [hdsq, if_pos (Finset.mem_range.1 hq)]
        have : (q.factorial : ℂ) ≠ 0 := by exact_mod_cast q.factorial_ne_zero
        field_simp
      simp_rw [hgs, Finset.mul_sum, Finset.sum_mul, Finset.sum_div, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro q _
      apply Finset.sum_congr rfl; intro k _
      ring
    rw [h1, integral_finset_sum _ (fun q _ => ((hpi q).div_const _).const_mul _)]
    apply Finset.sum_congr rfl; intro q _
    rw [integral_const_mul, integral_div]
  have hbound : ∀ s : ℝ, Y + s ∈ S.J →
      ‖∫ ω, pr B wt (S.gs Y s) w ω ∂B.μ‖ ≤ √M * √(S.Dn ε σ Y p) := by
    intro s hs
    have h1 := opt_delta _ _ _ (integral_nonneg fun ω => sq_nonneg' B wt hwt0 (S.gs Y s) ω)
      (integral_nonneg fun ω => sq_nonneg' B wt hwt0 w ω)
      (fun δ hδ => norm_int_pr_le B wt hwt0 (S.gs Y s) w (hgi s) (hci p) δ hδ)
    rw [← hEn, ← hDn] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hEns s hs)) (Real.sqrt_nonneg _))
  have hfun : (fun s : ℝ => ∑ k : Fin (S.r + 1 + 1), s ^ (k : ℕ) • a' k) =
      fun s : ℝ => (mkP (S.r + 1) a').eval (s : ℂ) := by
    funext s
    rw [mkP_eval, ← Fin.sum_univ_eq_sum_range (fun q => (s : ℂ) ^ q * a' q)]
    apply Finset.sum_congr rfl; intro k _
    rw [Complex.real_smul]; push_cast; ring
  have hmk := hMV ℂ (S.r + 1) (fun k => a' k) (S.a - Y) S.L (√M * √(S.Dn ε σ Y p)) hL (by
    intro t ht
    have hs : Y + t ∈ S.J := by
      unfold Step.J; constructor <;> [linarith [ht.1]; linarith [ht.2]]
    have e : (∑ k : Fin (S.r + 1 + 1), t ^ (k : ℕ) • a' k) = (mkP (S.r + 1) a').eval (t : ℂ) := congrFun hfun t
    rw [e, mkP_eval, ← hphi t]
    exact hbound t hs) p 0 (by
      have h1 := hY.1; have h2 := hY.2
      constructor <;> linarith)
  rw [hfun, iterDeriv_poly] at hmk
  simp only [Complex.ofReal_zero] at hmk
  rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative, mkP_coeff, zero_add, if_pos hp] at hmk
  have hval : (p.descFactorial p) • a' p = ((S.Dn ε σ Y p : ℝ) : ℂ) := by
    rw [Nat.descFactorial_self, hDn, ← int_pr_self]
    simp only [a', nsmul_eq_mul]
    have : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
    field_simp
    rfl
  rw [hval, Complex.norm_real, Real.norm_of_nonneg hD0] at hmk
  push_cast at hmk
  set x := √(S.Dn ε σ Y p) with hx
  set y := √M with hy
  set A := (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ p with hA
  have hx2 : x * x = S.Dn ε σ Y p := Real.mul_self_sqrt hD0
  have hy2 : y * y = M := Real.mul_self_sqrt hM0
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hA0 : 0 ≤ A := pow_nonneg hK0 p
  have hpow : (2 * ((S.r : ℝ) + 1) ^ 2 / S.L) ^ (2 * p) = A * A := by
    rw [hA, ← pow_add]; congr 1; ring
  rw [hpow, ← hx2, ← hy2]
  rw [← hx2] at hmk
  rcases hx0.eq_or_lt with h0 | h0
  · rw [← h0]; simp; positivity
  · have h3 : x ≤ A * y := by
      have : x * x ≤ (A * y) * x := by linarith
      exact le_of_mul_le_mul_right this h0
    nlinarith [mul_nonneg hA0 hy0]
end Formalism.FourierDecayAlt.P.LEx2
