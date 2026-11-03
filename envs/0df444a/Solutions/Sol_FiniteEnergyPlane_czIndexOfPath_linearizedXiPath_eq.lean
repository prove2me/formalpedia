-- Prove2me | solution 1 for FiniteEnergyPlane.czIndexOfPath_linearizedXiPath_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T19:57:29.530849+00:00
-- url     : https://prove2.me/submissions/4952a06e-6969-4df5-9336-7152ac08c9df

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Mathlib
import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Theorems.Thm_FiniteEnergyPlane_hamiltonianFlow_reeb_timeChange
import Theorems.Thm_FiniteEnergyPlane_linReebFlow_unitaryFrame_eq
import Theorems.Thm_HryniewiczCriterion_czIndexOfPath_conj_of_loop
import Theorems.Thm_HryniewiczCriterion_windingInterval_reparam
import Theorems.Thm_FiniteEnergyPlane_linReebFlow_spec
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_symplectic

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real
open FiniteEnergyPlane
open scoped ContDiff Topology in
open scoped ContDiff Topology
open Set
open Matrix
open Set Matrix
open scoped ContDiff Real

/-! Linear algebra of Hryniewicz's global frame `Z₁, Z₂` of `ξ` (copied from the
`exists_prime_periodicOrbit_cover` solution, renamed `r26_*`). -/

namespace HryniewiczCriterion

open scoped ContDiff

lemma r26_clm_apply_eq_sum (L : R4 →L[ℝ] ℝ) (v : R4) :
    L v = v 0 * L (Pi.single 0 1) + v 1 * L (Pi.single 1 1) +
      v 2 * L (Pi.single 2 1) + v 3 * L (Pi.single 3 1) := by
  have hv : v = ∑ i, v i • (Pi.single i 1 : R4) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_smul, Fin.sum_univ_four, smul_eq_mul]

lemma r26_omega0_X_right (H : R4 → ℝ) (y p : R4) :
    omega0 p (hamiltonianVectorField H y) = fderiv ℝ H y p := by
  rw [r26_clm_apply_eq_sum (fderiv ℝ H y) p]
  simp [omega0, hamiltonianVectorField, partialDeriv]

lemma r26_omega0_antisymm (u v : R4) : omega0 u v = -omega0 v u := by
  simp [omega0]; ring

lemma r26_omega0_self (u : R4) : omega0 u u = 0 := by
  simp [omega0]; ring

lemma r26_omega0_lin_right (u a b c d : R4) (p q r s : ℝ) :
    omega0 u (p • a + q • b + r • c + s • d) =
      p * omega0 u a + q * omega0 u b + r * omega0 u c + s * omega0 u d := by
  simp [omega0]; ring

lemma r26_omega0_lin_left (u a b : R4) (p q : ℝ) :
    omega0 (p • a + q • b) u = p * omega0 a u + q * omega0 b u := by
  simp [omega0]; ring

lemma r26_omega0_lin_right2 (u a b : R4) (p q : ℝ) :
    omega0 u (p • a + q • b) = p * omega0 u a + q * omega0 u b := by
  simp [omega0]; ring

lemma r26_omega0_smul_left (u v : R4) (p : ℝ) : omega0 (p • u) v = p * omega0 u v := by
  simp [omega0]; ring

lemma r26_omega0_smul_right (u v : R4) (p : ℝ) : omega0 u (p • v) = p * omega0 u v := by
  simp [omega0]; ring

lemma r26_eq_frame_of_omega0 (Z₁ Z₂ a b v : R4) (h12 : omega0 Z₁ Z₂ = 1)
    (h1a : omega0 Z₁ a = 0) (h1b : omega0 Z₁ b = 0) (h2a : omega0 Z₂ a = 0)
    (h2b : omega0 Z₂ b = 0) (hab : omega0 a b ≠ 0)
    (hva : omega0 v a = 0) (hvb : omega0 v b = 0) :
    v = omega0 v Z₂ • Z₁ + omega0 Z₁ v • Z₂ := by
  set w : Fin 4 → R4 := ![Z₁, Z₂, a, b] with hw
  have hli : LinearIndependent ℝ w := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    replace hg : g 0 • Z₁ + g 1 • Z₂ + g 2 • a + g 3 • b = 0 := by
      simpa [Fin.sum_univ_four, hw] using hg
    have e1 := congrArg (omega0 Z₁) hg
    have e2 := congrArg (omega0 Z₂) hg
    have e3 := congrArg (omega0 a) hg
    have e4 := congrArg (omega0 b) hg
    rw [r26_omega0_lin_right] at e1 e2 e3 e4
    have z : ∀ u : R4, omega0 u 0 = 0 := fun u => by simp [omega0]
    rw [z] at e1 e2 e3 e4
    rw [r26_omega0_self, h12, h1a, h1b] at e1
    rw [r26_omega0_antisymm Z₂ Z₁, h12, r26_omega0_self, h2a, h2b] at e2
    rw [r26_omega0_antisymm a Z₁, r26_omega0_antisymm a Z₂, h1a, h2a, r26_omega0_self] at e3
    rw [r26_omega0_antisymm b Z₁, r26_omega0_antisymm b Z₂, r26_omega0_antisymm b a, h1b, h2b,
      r26_omega0_self] at e4
    have g1 : g 1 = 0 := by linarith
    have g0 : g 0 = 0 := by linarith
    have g3 : g 3 = 0 := by
      have : g 3 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    have g2 : g 2 = 0 := by
      have : g 2 * omega0 a b = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_right hab
    intro i; fin_cases i <;> assumption
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp)
  have hv : v ∈ Submodule.span ℝ (Set.range w) := by rw [hspan]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
  replace hc : c 0 • Z₁ + c 1 • Z₂ + c 2 • a + c 3 • b = v := by
    simpa [Fin.sum_univ_four, hw] using hc
  have ea : omega0 v a = c 0 * omega0 Z₁ a + c 1 * omega0 Z₂ a + c 2 * omega0 a a +
      c 3 * omega0 b a := by
    rw [← hc, r26_omega0_antisymm, r26_omega0_lin_right]
    rw [r26_omega0_antisymm a Z₁, r26_omega0_antisymm a Z₂, r26_omega0_antisymm a b,
      r26_omega0_self]; ring
  have eb : omega0 v b = c 0 * omega0 Z₁ b + c 1 * omega0 Z₂ b + c 2 * omega0 a b +
      c 3 * omega0 b b := by
    rw [← hc, r26_omega0_antisymm, r26_omega0_lin_right]
    rw [r26_omega0_antisymm b Z₁, r26_omega0_antisymm b Z₂, r26_omega0_antisymm b a,
      r26_omega0_self]; ring
  rw [h1a, h2a, r26_omega0_self, r26_omega0_antisymm b a, hva] at ea
  rw [h1b, h2b, r26_omega0_self, hvb] at eb
  have c3 : c 3 = 0 := by
    have : c 3 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have c2 : c 2 = 0 := by
    have : c 2 * omega0 a b = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right hab
  have hv2 : v = c 0 • Z₁ + c 1 • Z₂ := by rw [← hc, c2, c3]; simp
  have k0 : omega0 v Z₂ = c 0 := by
    rw [hv2, r26_omega0_lin_left, r26_omega0_self, h12]; ring
  have k1 : omega0 Z₁ v = c 1 := by
    rw [hv2, r26_omega0_antisymm, r26_omega0_lin_left, r26_omega0_self,
      r26_omega0_antisymm Z₂ Z₁, h12]; ring
  rw [k0, k1]; exact hv2

variable {H : R4 → ℝ}

lemma r26_ne_zero_of_dH_pos {y : R4} (hy : 0 < fderiv ℝ H y y) : y ≠ 0 := by
  rintro rfl; simp at hy

lemma r26_dot4_pos {y : R4} (hy : y ≠ 0) : 0 < dot4 y y := by
  by_contra h
  push_neg at h
  apply hy
  have hs : ∀ i, y i * y i = 0 := by
    intro i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ y j * y j := fun j _ => mul_self_nonneg _
    have hsum : ∑ j, y j * y j = 0 := le_antisymm h (Finset.sum_nonneg hnn)
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ _)
  ext i; simpa using hs i

lemma r26_euclidNorm_sq (y : R4) : euclidNorm y * euclidNorm y = dot4 y y := by
  have : 0 ≤ dot4 y y := Finset.sum_nonneg fun j _ => mul_self_nonneg (y j)
  exact Real.mul_self_sqrt this

lemma r26_dH_xiFrameRaw {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    fderiv ℝ H y (xiFrameRaw H Q y) = 0 := by
  simp only [xiFrameRaw, map_sub, map_smul, smul_eq_mul]
  field_simp; ring

lemma r26_omega0_xiFrameRaw_self (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) (y : R4) :
    omega0 y (xiFrameRaw H Q y) = 0 := by
  have := hQ y
  simp only [xiFrameRaw, omega0] at this ⊢
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination this

lemma r26_omega0_quatQ1 (y : R4) : omega0 y (quatQ1 y) = 0 := by
  simp [omega0, quatQ1]; ring

lemma r26_omega0_quatQ2 (y : R4) : omega0 y (quatQ2 y) = 0 := by
  simp [omega0, quatQ2]; ring

lemma r26_omega0_raw21 (y : R4) :
    omega0 (xiFrameRaw H quatQ2 y) (xiFrameRaw H quatQ1 y) = dot4 y y := by
  simp [xiFrameRaw, omega0, quatQ1, quatQ2, dot4, Fin.sum_univ_four]; ring

lemma r26_omega0_xiFrame12 {y : R4} (hy : 0 < fderiv ℝ H y y) :
    omega0 (xiFrame1 H y) (xiFrame2 H y) = 1 := by
  have hpos := r26_dot4_pos (r26_ne_zero_of_dH_pos hy)
  have hn := r26_euclidNorm_sq y
  have hne : euclidNorm y ≠ 0 := by
    intro h; rw [h] at hn; linarith
  rw [xiFrame1, xiFrame2, r26_omega0_smul_left, r26_omega0_smul_right, r26_omega0_raw21, ← hn]
  field_simp

/-- `ω₀(y, Zᵢ) = 0`. -/
lemma r26_omega0_y_xiFrame (Q : R4 → R4) (hQ : ∀ y, omega0 y (Q y) = 0) (y : R4) :
    omega0 y ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) = 0 := by
  rw [r26_omega0_smul_right, r26_omega0_xiFrameRaw_self Q hQ y, mul_zero]

/-- `dH(Zᵢ) = 0`. -/
lemma r26_dH_xiFrame {y : R4} (hy : 0 < fderiv ℝ H y y) (Q : R4 → R4) :
    fderiv ℝ H y ((euclidNorm y)⁻¹ • xiFrameRaw H Q y) = 0 := by
  rw [map_smul, r26_dH_xiFrameRaw hy, smul_zero]

lemma r26_cd_omega0 {p q : ℝ → R4} (hp : ContDiff ℝ ∞ p) (hq : ContDiff ℝ ∞ q) :
    ContDiff ℝ ∞ (fun τ => omega0 (p τ) (q τ)) := by
  have h := fun i => contDiff_pi.1 hp i
  have k := fun i => contDiff_pi.1 hq i
  simp only [omega0]
  exact ((((h 0).mul (k 1)).sub ((h 1).mul (k 0))).add ((h 2).mul (k 3))).sub
    ((h 3).mul (k 2))

lemma r26_cd_dH (hH : ContDiff ℝ ∞ H) {c v : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (fun τ => fderiv ℝ H (c τ) (v τ)) :=
  ((hH.fderiv_right le_rfl).comp hc).clm_apply hv

lemma r26_cd_quatQ1 {c : ℝ → R4} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun τ => quatQ1 (c τ)) := by
  have h := fun i => contDiff_pi.1 hc i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ1] <;> first | exact h _ | exact (h _).neg

lemma r26_cd_quatQ2 {c : ℝ → R4} (hc : ContDiff ℝ ∞ c) :
    ContDiff ℝ ∞ (fun τ => quatQ2 (c τ)) := by
  have h := fun i => contDiff_pi.1 hc i
  refine contDiff_pi.2 fun i => ?_
  fin_cases i <;> simp [quatQ2] <;> first | exact h _ | exact (h _).neg

lemma r26_cd_xiFrame (hH : ContDiff ℝ ∞ H) {c : ℝ → R4} (hc : ContDiff ℝ ∞ c)
    (hpos : ∀ τ, 0 < fderiv ℝ H (c τ) (c τ)) (Q : R4 → R4)
    (hQ : ContDiff ℝ ∞ (fun τ => Q (c τ))) :
    ContDiff ℝ ∞ (fun τ => (euclidNorm (c τ))⁻¹ • xiFrameRaw H Q (c τ)) := by
  have hraw : ContDiff ℝ ∞ (fun τ => xiFrameRaw H Q (c τ)) :=
    hQ.sub (((r26_cd_dH hH hc hQ).div (r26_cd_dH hH hc hc) fun τ => (hpos τ).ne').smul hc)
  have hdot : ContDiff ℝ ∞ (fun τ => dot4 (c τ) (c τ)) := by
    have h := fun i => contDiff_pi.1 hc i
    simp only [dot4, Fin.sum_univ_four]
    exact ((((h 0).mul (h 0)).add ((h 1).mul (h 1))).add ((h 2).mul (h 2))).add
      ((h 3).mul (h 3))
  have hdne : ∀ τ, dot4 (c τ) (c τ) ≠ 0 := fun τ =>
    (r26_dot4_pos (r26_ne_zero_of_dH_pos (hpos τ))).ne'
  have hnorm : ContDiff ℝ ∞ (fun τ => euclidNorm (c τ)) := hdot.sqrt hdne
  have hnne : ∀ τ, euclidNorm (c τ) ≠ 0 := fun τ h => by
    have := r26_euclidNorm_sq (c τ); rw [h] at this; exact hdne τ (by linarith)
  exact (hnorm.inv hnne).smul hraw

end HryniewiczCriterion

namespace FiniteEnergyPlane

/-- `Z₁(x)`, the first vector of the global frame. -/
noncomputable def r26de (H : V 1 → ℝ) (x : V 1) : V 1 := HryniewiczCriterion.xiFrame1 H x

lemma r26d_omega0_eq (u v : V 1) : omega0 u v = HryniewiczCriterion.omega0 u v := by
  simp [omega0, HryniewiczCriterion.omega0, dot, j0, Fin.sum_univ_four]; ring

section point

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {x : V 1} (hx : H x = 1)

include hH hx in
lemma r26d_pos : 0 < fderiv ℝ H x x := hH.2.2 x hx

include hH hx in
lemma r26d_e12 : HryniewiczCriterion.omega0 (r26de H x) (HryniewiczCriterion.xiFrame2 H x) = 1 :=
  HryniewiczCriterion.r26_omega0_xiFrame12 (r26d_pos hH hx)

include hH hx in
lemma r26d_e_xi : IsInXi H x (r26de H x) := by
  refine ⟨?_, ?_⟩
  · rw [liouville, r26d_omega0_eq, r26de, HryniewiczCriterion.xiFrame1,
      HryniewiczCriterion.r26_omega0_y_xiFrame _ HryniewiczCriterion.r26_omega0_quatQ2]
    simp
  · exact HryniewiczCriterion.r26_dH_xiFrame (r26d_pos hH hx) _

include hH hx in
lemma r26d_e2_xi : IsInXi H x (HryniewiczCriterion.xiFrame2 H x) := by
  refine ⟨?_, ?_⟩
  · rw [liouville, r26d_omega0_eq, HryniewiczCriterion.xiFrame2,
      HryniewiczCriterion.r26_omega0_y_xiFrame _ HryniewiczCriterion.r26_omega0_quatQ1]
    simp
  · exact HryniewiczCriterion.r26_dH_xiFrame (r26d_pos hH hx) _

include hH hx in
/-- Every `w ∈ ξ_x` is `ω₀(w, Z₂) Z₁ + ω₀(Z₁, w) Z₂`. -/
lemma r26d_decomp {w : V 1} (hw : IsInXi H x w) :
    w = HryniewiczCriterion.omega0 w (HryniewiczCriterion.xiFrame2 H x) • r26de H x +
      HryniewiczCriterion.omega0 (r26de H x) w • HryniewiczCriterion.xiFrame2 H x := by
  have hpos := r26d_pos hH hx
  have xi_a : ∀ v, IsInXi H x v → HryniewiczCriterion.omega0 v x = 0 := by
    intro v hv
    have := hv.1
    rw [liouville, r26d_omega0_eq] at this
    rw [HryniewiczCriterion.r26_omega0_antisymm]; linarith
  have xi_b : ∀ v, IsInXi H x v →
      HryniewiczCriterion.omega0 v (HryniewiczCriterion.hamiltonianVectorField H x) = 0 := by
    intro v hv
    rw [HryniewiczCriterion.r26_omega0_X_right]; exact hv.2
  have := HryniewiczCriterion.r26_eq_frame_of_omega0 (r26de H x) (HryniewiczCriterion.xiFrame2 H x)
    x (HryniewiczCriterion.hamiltonianVectorField H x) w (r26d_e12 hH hx)
    (xi_a _ (r26d_e_xi hH hx)) (xi_b _ (r26d_e_xi hH hx)) (xi_a _ (r26d_e2_xi hH hx))
    (xi_b _ (r26d_e2_xi hH hx))
    (by rw [HryniewiczCriterion.r26_omega0_X_right]; exact hpos.ne') (xi_a _ hw) (xi_b _ hw)
  exact this

end point

theorem eq_xiCoordC_smul_xiFrame_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    {x w : V 1} (hx : H x = 1) (hw : IsInXi H x w) :
    w = (xiCoordC H x w).re • ofR4 (HryniewiczCriterion.xiFrame1 (fun z => H (ofR4 z)) (toR4 x)) +
      (xiCoordC H x w).im • ofR4 (HryniewiczCriterion.xiFrame2 (fun z => H (ofR4 z)) (toR4 x)) :=
  r26d_decomp hH hx hw

end FiniteEnergyPlane

/-! Basic identities for the symplectization of a star-shaped level (copied, renamed, from the
`ka_*` helpers of accepted solution a386257a). -/


set_option linter.unusedSimpArgs false

def ka_sig {n : ℕ} (k : Fin (2 * (n + 1))) : Fin (2 * (n + 1)) :=
  if h : (k : ℕ) % 2 = 0 then ⟨k + 1, by have := k.2; omega⟩ else ⟨k - 1, by have := k.2; omega⟩

def ka_sgn {n : ℕ} (k : Fin (2 * (n + 1))) : ℝ := if (k : ℕ) % 2 = 0 then -1 else 1

theorem ka_sig_val {n : ℕ} (k : Fin (2 * (n + 1))) :
    ((ka_sig k : Fin (2 * (n + 1))) : ℕ) = if (k : ℕ) % 2 = 0 then (k : ℕ) + 1 else (k : ℕ) - 1 := by
  unfold ka_sig; split_ifs <;> rfl

theorem ka_sig_sig {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sig (ka_sig k) = k := by
  ext
  rw [ka_sig_val, ka_sig_val]
  split_ifs <;> omega

theorem ka_sgn_sig {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sgn (ka_sig k) = - ka_sgn k := by
  unfold ka_sgn
  rw [ka_sig_val]
  split_ifs <;> (try norm_num) <;> omega

theorem ka_sgn_sq {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sgn k * ka_sgn k = 1 := by
  unfold ka_sgn; split_ifs <;> norm_num

def ka_sigE (n : ℕ) : Equiv.Perm (Fin (2 * (n + 1))) :=
  Function.Involutive.toPerm ka_sig ka_sig_sig

theorem ka_sigE_apply {n : ℕ} (k : Fin (2 * (n + 1))) : ka_sigE n k = ka_sig k := rfl

theorem ka_j0_apply {n : ℕ} (v : V n) (k : Fin (2 * (n + 1))) :
    j0 v k = ka_sgn k * v (ka_sig k) := by
  unfold j0 ka_sgn ka_sig
  split_ifs <;> simp

theorem ka_j0_j0 {n : ℕ} (v : V n) : j0 (j0 v) = -v := by
  funext k
  rw [ka_j0_apply, ka_j0_apply, ka_sig_sig, ka_sgn_sig]
  simp only [Pi.neg_apply]
  have := ka_sgn_sq k
  linear_combination (-(v k)) * this

theorem ka_j0_smul {n : ℕ} (a : ℝ) (v : V n) : j0 (a • v) = a • j0 v := by
  funext k; simp only [ka_j0_apply, Pi.smul_apply, smul_eq_mul]; ring

theorem ka_j0_add {n : ℕ} (u v : V n) : j0 (u + v) = j0 u + j0 v := by
  funext k; simp only [ka_j0_apply, Pi.add_apply]; ring

theorem ka_j0_sub {n : ℕ} (u v : V n) : j0 (u - v) = j0 u - j0 v := by
  funext k; simp only [ka_j0_apply, Pi.sub_apply]; ring

theorem ka_dot_comm {n : ℕ} (u v : V n) : dot u v = dot v u := by
  unfold dot; exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem ka_dot_smul_right {n : ℕ} (a : ℝ) (u v : V n) : dot u (a • v) = a * dot u v := by
  unfold dot; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_smul_left {n : ℕ} (a : ℝ) (u v : V n) : dot (a • u) v = a * dot u v := by
  rw [ka_dot_comm, ka_dot_smul_right, ka_dot_comm]

theorem ka_dot_add_right {n : ℕ} (u v w : V n) : dot u (v + w) = dot u v + dot u w := by
  unfold dot; rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_add_left {n : ℕ} (u v w : V n) : dot (v + w) u = dot v u + dot w u := by
  rw [ka_dot_comm, ka_dot_add_right, ka_dot_comm, ka_dot_comm u]

theorem ka_dot_sub_right {n : ℕ} (u v w : V n) : dot u (v - w) = dot u v - dot u w := by
  unfold dot; rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp; ring)

theorem ka_dot_sub_left {n : ℕ} (u v w : V n) : dot (v - w) u = dot v u - dot w u := by
  rw [ka_dot_comm, ka_dot_sub_right, ka_dot_comm, ka_dot_comm u]

theorem ka_dot_neg_right {n : ℕ} (u v : V n) : dot u (-v) = - dot u v := by
  unfold dot; rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl (fun k _ => by simp)

theorem ka_dot_neg_left {n : ℕ} (u v : V n) : dot (-u) v = - dot u v := by
  rw [ka_dot_comm, ka_dot_neg_right, ka_dot_comm]

theorem ka_dot_j0_left {n : ℕ} (u v : V n) : dot (j0 u) v = - dot u (j0 v) := by
  unfold dot
  rw [← Finset.sum_neg_distrib]
  rw [← Equiv.sum_comp (ka_sigE n)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [ka_sigE_apply, ka_j0_apply, ka_sig_sig, ka_sgn_sig]
  ring

theorem ka_dot_j0_j0 {n : ℕ} (u v : V n) : dot (j0 u) (j0 v) = dot u v := by
  rw [ka_dot_j0_left, ka_j0_j0, ka_dot_neg_right, neg_neg]

theorem ka_dot_self_j0 {n : ℕ} (u : V n) : dot u (j0 u) = 0 := by
  have := ka_dot_j0_left u u
  rw [ka_dot_comm] at this
  linarith

theorem ka_clm_apply {n : ℕ} (L : V n →L[ℝ] ℝ) (v : V n) :
    L v = ∑ k, v k * L (Pi.single k 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [show (Pi.single k (v k) : V n) = v k • Pi.single k 1 by
    rw [← Pi.single_smul]; simp]
  rw [map_smul, smul_eq_mul]

theorem ka_fderiv_eq_dot {n : ℕ} (H : V n → ℝ) (x v : V n) :
    fderiv ℝ H x v = dot (grad H x) v := by
  rw [ka_clm_apply]; unfold dot grad
  exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)

theorem ka_liouville_ham {n : ℕ} (H : V n → ℝ) (x : V n) :
    liouville x (hamVF H x) = fderiv ℝ H x x / 2 := by
  unfold liouville omega0 hamVF
  rw [ka_dot_j0_j0, ka_fderiv_eq_dot, ka_dot_comm]

theorem ka_reeb_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) :
    0 < liouville x (hamVF H x) ∧ liouville x (reeb H x) = 1 ∧ fderiv ℝ H x (reeb H x) = 0 ∧
      ∀ w : V n, fderiv ℝ H x w = 0 → omega0 (reeb H x) w = 0 := by
  have hpos : 0 < liouville x (hamVF H x) := by
    rw [ka_liouville_ham]; have := hH.2.2 x hx; linarith
  refine ⟨hpos, ?_, ?_, ?_⟩
  · unfold reeb
    have : liouville x ((liouville x (hamVF H x))⁻¹ • hamVF H x) =
        (liouville x (hamVF H x))⁻¹ * liouville x (hamVF H x) := by
      unfold liouville omega0; rw [ka_dot_smul_right]; ring
    rw [this, inv_mul_cancel₀ hpos.ne']
  · unfold reeb hamVF
    rw [map_smul, ka_fderiv_eq_dot, ka_dot_self_j0, smul_zero]
  · intro w hw
    unfold reeb hamVF omega0
    rw [ka_j0_smul, ka_j0_j0, ka_dot_smul_left, ka_dot_neg_left,
      ← ka_fderiv_eq_dot, hw]; ring

theorem ka_om_add_left {n : ℕ} (u v w : V n) : omega0 (u + v) w = omega0 u w + omega0 v w := by
  unfold omega0; rw [ka_j0_add, ka_dot_add_left]
theorem ka_om_add_right {n : ℕ} (u v w : V n) : omega0 w (u + v) = omega0 w u + omega0 w v := by
  unfold omega0; rw [ka_dot_add_right]
theorem ka_om_sub_left {n : ℕ} (u v w : V n) : omega0 (u - v) w = omega0 u w - omega0 v w := by
  unfold omega0; rw [ka_j0_sub, ka_dot_sub_left]
theorem ka_om_sub_right {n : ℕ} (u v w : V n) : omega0 w (u - v) = omega0 w u - omega0 w v := by
  unfold omega0; rw [ka_dot_sub_right]
theorem ka_om_smul_left {n : ℕ} (a : ℝ) (u w : V n) : omega0 (a • u) w = a * omega0 u w := by
  unfold omega0; rw [ka_j0_smul, ka_dot_smul_left]
theorem ka_om_smul_right {n : ℕ} (a : ℝ) (u w : V n) : omega0 w (a • u) = a * omega0 w u := by
  unfold omega0; rw [ka_dot_smul_right]
theorem ka_om_anti {n : ℕ} (u v : V n) : omega0 u v = - omega0 v u := by
  unfold omega0; rw [ka_dot_j0_left, ka_dot_comm]
theorem ka_om_self {n : ℕ} (u : V n) : omega0 u u = 0 := by
  have := ka_om_anti u u; linarith

theorem ka_liouvilleCLM_apply {n : ℕ} (x v : V n) : liouvilleCLM x v = liouville x v := by
  unfold liouvilleCLM liouville omega0 dot
  simp [Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => by ring)

theorem ka_scale_spec {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) : 0 < scaleToS H y ∧ H (scaleToS H y • y) = 1 := by
  have hex : ∃ r : ℝ, 0 < r ∧ H (r • y) = 1 := (hH.2.1 y hy).exists
  unfold scaleToS
  rw [dif_pos hex]
  exact Classical.choose_spec hex

theorem ka_scale_unique {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) (t : ℝ) (ht : 0 < t) (hHt : H (t • y) = 1) : scaleToS H y = t := by
  obtain ⟨r, _, hu⟩ := hH.2.1 y hy
  have h1 := hu t ⟨ht, hHt⟩
  have h2 := hu (scaleToS H y) (ka_scale_spec H hH y hy)
  rw [h1, h2]

theorem ka_scale_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y₀ : V n)
    (hy₀ : y₀ ≠ 0) : ContDiffAt ℝ ∞ (scaleToS H) y₀ := by
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y₀ hy₀
  set r := scaleToS H y₀
  set f : V n × ℝ → ℝ := fun p => H (p.2 • p.1) with hf
  have hfc : ContDiff ℝ ∞ f := hH.1.comp (ContDiff.smul contDiff_snd contDiff_fst)
  set u : V n × ℝ := (y₀, r)
  have cdf : ContDiffAt ℝ ∞ f u := hfc.contDiffAt
  have pn : (∞ : WithTop ℕ∞) ≠ 0 := by simp
  -- derivative
  have hg : HasFDerivAt (fun p : V n × ℝ => p.2 • p.1)
      (r • ContinuousLinearMap.fst ℝ (V n) ℝ + (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀) u := by
    have h1 : HasFDerivAt (fun p : V n × ℝ => p.2) (ContinuousLinearMap.snd ℝ (V n) ℝ) u :=
      hasFDerivAt_snd
    have h2 : HasFDerivAt (fun p : V n × ℝ => p.1) (ContinuousLinearMap.fst ℝ (V n) ℝ) u :=
      hasFDerivAt_fst
    exact h1.smul h2
  have hHd : HasFDerivAt H (fderiv ℝ H (r • y₀)) (r • y₀) :=
    (hH.1.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hfd : HasFDerivAt f ((fderiv ℝ H (r • y₀)).comp
      (r • ContinuousLinearMap.fst ℝ (V n) ℝ + (ContinuousLinearMap.snd ℝ (V n) ℝ).smulRight y₀)) u :=
    hHd.comp u hg
  have hpos : 0 < fderiv ℝ H (r • y₀) y₀ := by
    have := hH.2.2 (r • y₀) hHx
    rw [map_smul, smul_eq_mul] at this
    exact pos_of_mul_pos_right this hr.le
  set c := fderiv ℝ H (r • y₀) y₀
  have hL1 : (fderiv ℝ f u ∘L .inr ℝ (V n) ℝ) 1 = c := by
    rw [hfd.fderiv]; simp [c]
  have if₂ : (fderiv ℝ f u ∘L .inr ℝ (V n) ℝ).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
    · apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
      rw [show c⁻¹ = c⁻¹ • (1:ℝ) by simp, map_smul, hL1, smul_eq_mul, inv_mul_cancel₀ hpos.ne']
    · apply ContinuousLinearMap.ext_ring
      rw [ContinuousLinearMap.comp_apply, hL1]
      simp [inv_mul_cancel₀ hpos.ne']
  set ψ := ContDiffAt.implicitFunction cdf pn if₂
  have hψc : ContDiffAt ℝ ∞ ψ y₀ := ContDiffAt.contDiffAt_implicitFunction cdf pn if₂
  have hψ0 : ψ y₀ = r := ContDiffAt.implicitFunction_apply_self cdf pn if₂
  have hψeq := ContDiffAt.eventually_apply_implicitFunction cdf pn if₂
  have hψpos : ∀ᶠ y in 𝓝 y₀, 0 < ψ y := by
    have := hψc.continuousAt.eventually (lt_mem_nhds (show (0:ℝ) < ψ y₀ by rw [hψ0]; exact hr))
    exact this
  have hne : ∀ᶠ y in 𝓝 y₀, y ≠ 0 := isOpen_ne.mem_nhds hy₀
  have hev : ψ =ᶠ[𝓝 y₀] scaleToS H := by
    filter_upwards [hψeq, hψpos, hne] with y h1 h2 h3
    have h1' : H (ψ y • y) = 1 := by
      have : f (y, ψ y) = f u := h1
      simp only [hf, u] at this
      rw [this, hHx]
    exact (ka_scale_unique H hH y h3 (ψ y) h2 h1').symm
  exact hψc.congr_of_eventuallyEq hev.symm


theorem ka_j0_contDiff {n : ℕ} : ContDiff ℝ ∞ (j0 : V n → V n) := by
  refine contDiff_pi.2 (fun k => ?_)
  have : (fun v : V n => j0 v k) = fun v => ka_sgn k * v (ka_sig k) := by
    funext v; exact ka_j0_apply v k
  rw [this]
  exact contDiff_const.mul (contDiff_apply ℝ ℝ (ka_sig k))

theorem ka_dH_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (fderiv ℝ H) := hH.fderiv_right (m := ∞) (by simp)

theorem ka_grad_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (grad H) := by
  refine contDiff_pi.2 (fun k => ?_)
  exact (ka_dH_contDiff H hH).clm_apply contDiff_const

theorem ka_hamVF_contDiff {n : ℕ} (H : V n → ℝ) (hH : ContDiff ℝ ∞ H) :
    ContDiff ℝ ∞ (hamVF H) := ka_j0_contDiff.comp (ka_grad_contDiff H hH)

theorem ka_liouvilleCLM_contDiff {n : ℕ} : ContDiff ℝ ∞ (liouvilleCLM : V n → V n →L[ℝ] ℝ) := by
  unfold liouvilleCLM
  refine ContDiff.const_smul _ (ContDiff.sum (fun k _ => ?_))
  exact ((contDiff_apply ℝ ℝ k).comp ka_j0_contDiff).smul contDiff_const

theorem ka_reeb_contDiffAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (x : V n)
    (hx : x ∈ energySurface H) : ContDiffAt ℝ ∞ (reeb H) x := by
  have hpos := (ka_reeb_spec H hH x hx).1
  have hL : (fun x => liouville x (hamVF H x)) = fun x => liouvilleCLM x (hamVF H x) := by
    funext x; rw [ka_liouvilleCLM_apply]
  have hc : ContDiff ℝ ∞ (fun x => liouville x (hamVF H x)) := by
    rw [hL]; exact ka_liouvilleCLM_contDiff.clm_apply (ka_hamVF_contDiff H hH.1)
  unfold reeb
  exact (hc.contDiffAt.inv hpos.ne').smul (ka_hamVF_contDiff H hH.1).contDiffAt

theorem ka_scale_hasFDerivAt {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (y : V n)
    (hy : y ≠ 0) :
    HasFDerivAt (scaleToS H)
      ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)) y := by
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y hy
  have hd : DifferentiableAt ℝ (scaleToS H) y :=
    (ka_scale_contDiffAt H hH y hy).differentiableAt (by simp)
  set r := scaleToS H y
  set x := proj H y
  have hxr : x = r • y := rfl
  set L := fderiv ℝ (scaleToS H) y
  have hm : HasFDerivAt (fun y' => scaleToS H y' • y') (r • ContinuousLinearMap.id ℝ (V n) +
      L.smulRight y) y := hd.hasFDerivAt.smul (hasFDerivAt_id y)
  have hHd : HasFDerivAt H (fderiv ℝ H x) x :=
    (hH.1.differentiable (by simp)).differentiableAt.hasFDerivAt
  have hg := hHd.comp y hm
  have hev : (H ∘ fun y' => scaleToS H y' • y') =ᶠ[𝓝 y] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_ne.mem_nhds hy] with y' hy'
    exact (ka_scale_spec H hH y' hy').2
  have h0 := hg.fderiv
  rw [hev.fderiv_eq, fderiv_fun_const] at h0
  have hD : 0 < fderiv ℝ H x x := hH.2.2 x hHx
  have hL : ∀ v, L v = -(r ^ 2 / fderiv ℝ H x x) * fderiv ℝ H x v := by
    intro v
    have := congrArg (fun T => T v) h0
    simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, map_add, map_smul,
      smul_eq_mul] at this
    have hxy : fderiv ℝ H x y = fderiv ℝ H x x / r := by
      rw [hxr, map_smul, smul_eq_mul]; field_simp
    rw [hxy] at this
    field_simp
    field_simp at this
    linarith
  have : L = (-(r ^ 2 / fderiv ℝ H x x)) • fderiv ℝ H x := by
    ext1 v; rw [hL v]; rfl
  rw [← this]; exact hd.hasFDerivAt

theorem ka_hol_abstract {n : ℕ} (A B : V n) (P : V n → Prop) (J' : V n →L[ℝ] V n)
    (α β : V n →L[ℝ] ℝ)
    (hW : ∀ v, P (v - α v • A - β v • B)) (hJP : ∀ w, P w → P (J' w))
    (hαA : α A = 1) (hαB : α B = 0) (hβA : β A = 0) (hβB : β B = 1)
    (hαP : ∀ w, P w → α w = 0) (hβP : ∀ w, P w → β w = 0)
    (hB : ∀ w, P w → omega0 B w = 0) (us ut : V n)
    (hhol : us + (α ut • B - β ut • A + J' (ut - α ut • A - β ut • B)) = 0) :
    α us = β ut ∧ α ut = - β us ∧
      omega0 (us - α us • A) (ut - α ut • A) =
        omega0 (ut - α ut • A - β ut • B) (J' (ut - α ut • A - β ut • B)) ∧
      (β us = 0 → β ut = 0 → ut - α ut • A - β ut • B = 0 → us = 0 ∧ ut = 0) := by
  set w := ut - α ut • A - β ut • B with hwdef
  have hPw : P w := hW ut
  have hPJw := hJP _ hPw
  have hs : us = -(α ut • B - β ut • A + J' w) := eq_neg_of_add_eq_zero_left hhol
  have e1 : α us = β ut := by
    rw [hs, map_neg, map_add, hαP _ hPJw]
    simp only [map_sub, map_smul, hαA, hαB, smul_eq_mul]; ring
  have e2 : β us = - α ut := by
    rw [hs, map_neg, map_add, hβP _ hPJw]
    simp only [map_sub, map_smul, hβA, hβB, smul_eq_mul]; ring
  have hus : us - α us • A = β us • B - J' w := by
    rw [e1, e2]; rw [hs]; module
  have hut : ut - α ut • A = β ut • B + w := by rw [hwdef]; module
  have hBB : omega0 B B = 0 := ka_om_self B
  have hJwB : omega0 (J' w) B = 0 := by rw [ka_om_anti, hB _ hPJw, neg_zero]
  refine ⟨e1, by linarith, ?_, ?_⟩
  · rw [hus, hut]
    simp only [ka_om_add_right, ka_om_sub_left, ka_om_smul_left, ka_om_smul_right,
      hBB, hB _ hPw, hJwB]
    rw [ka_om_anti (J' w) w]; ring
  · intro h1 h2 h3
    have hw0 : w = 0 := h3
    have hα : α ut = 0 := by linarith
    have hJ0 : J' w = 0 := by rw [hw0, map_zero]
    constructor
    · rw [hs, hJ0, h2, hα]; simp
    · have : ut = α ut • A + β ut • B + w := by rw [hwdef]; module
      rw [this, hα, h2, hw0]; simp

theorem ka_clm_complex_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : ℂ →L[ℝ] E) (h1 : L 1 = 0) (hI : L Complex.I = 0) : L = 0 := by
  ext1 z
  have : z = z.re • (1:ℂ) + z.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [this, map_add, map_smul, map_smul, h1, hI]; simp

theorem ka_cr {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (z : ℂ)
    (hdu : DifferentiableAt ℝ u z) (hz : u z ≠ 0)
    (hhol : JHolomorphic.dbarJ (Jtilde H J) u z = 0) :
    ds (fun z => aCoord H (u z)) z = liouville (proj H (u z)) (dt (fun z => proj H (u z)) z) ∧
    dt (fun z => aCoord H (u z)) z = -liouville (proj H (u z)) (ds (fun z => proj H (u z)) z) := by
  set y := u z with hydef
  obtain ⟨hr, hHx⟩ := ka_scale_spec H hH y hz
  set r := scaleToS H y with hrdef
  set x := proj H y with hxdef
  have hxr : x = r • y := rfl
  have hx : x ∈ energySurface H := hHx
  have hyx : y = r⁻¹ • x := by rw [hxr, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  obtain ⟨hc, hR1, hRH, hRw⟩ := ka_reeb_spec H hH x hx
  set R := reeb H x
  set D := fderiv ℝ H x x
  have hD : 0 < D := hH.2.2 x hx
  set α : V n →L[ℝ] ℝ := (r / (2 * D)) • fderiv ℝ H x with hαdef
  set β : V n →L[ℝ] ℝ := r • liouvilleCLM x with hβdef
  set A : V n := (2:ℝ) • y
  set B : V n := r⁻¹ • R
  have hLA : liouvilleCLM x A = 0 := by
    simp only [A, hyx, ka_liouvilleCLM_apply]
    unfold liouville; simp only [ka_om_smul_right, ka_om_self]; ring
  -- derivatives
  have hS' := ka_scale_hasFDerivAt H hH y hz
  have ha' : HasFDerivAt (aCoord H) α y := by
    have h1 := (hS'.log hr.ne').const_mul (-1/2 : ℝ)
    have : (fun y => (-1/2 : ℝ) * Real.log (scaleToS H y)) = aCoord H := by
      funext y; unfold aCoord; ring
    rw [this] at h1
    have heq : α = ((-1 / 2 : ℝ) • (scaleToS H y)⁻¹ • -(scaleToS H y ^ 2 /
        (fderiv ℝ H (proj H y)) (proj H y)) • fderiv ℝ H (proj H y)) := by
      ext1 v
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, ← hrdef, ← hxdef]
      have hD' : fderiv ℝ H x x ≠ 0 := hD.ne'
      field_simp
      exact mul_comm _ _
    rw [heq]; exact h1
  have hp' : HasFDerivAt (proj H) (r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A)) y := by
    have h1 := hS'.smul (hasFDerivAt_id y)
    have heq : r • (ContinuousLinearMap.id ℝ (V n) - α.smulRight A) =
        scaleToS H y • ContinuousLinearMap.id ℝ (V n) +
        ((-(scaleToS H y ^ 2 / fderiv ℝ H (proj H y) (proj H y))) • fderiv ℝ H (proj H y)).smulRight y := by
      ext1 v
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
        ContinuousLinearMap.add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.smulRight_apply, smul_eq_mul, ← hrdef, ← hxdef, smul_sub, smul_smul]
      have hD' : fderiv ℝ H x x ≠ 0 := hD.ne'
      rw [sub_eq_add_neg, ← neg_smul]
      congr 2
      field_simp
      ring
    rw [heq]; exact h1
  set us := fderiv ℝ u z 1
  set ut := fderiv ℝ u z Complex.I
  have hdsa : ds (fun z => aCoord H (u z)) z = α us := by
    unfold ds; rw [show (fun z => aCoord H (u z)) = aCoord H ∘ u from rfl, (ha'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdta : dt (fun z => aCoord H (u z)) z = α ut := by
    unfold dt; rw [show (fun z => aCoord H (u z)) = aCoord H ∘ u from rfl, (ha'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdsw : ds (fun z => proj H (u z)) z = r • (us - α us • A) := by
    unfold ds; rw [show (fun z => proj H (u z)) = proj H ∘ u from rfl, (hp'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hdtw : dt (fun z => proj H (u z)) z = r • (ut - α ut • A) := by
    unfold dt; rw [show (fun z => proj H (u z)) = proj H ∘ u from rfl, (hp'.comp z hdu.hasFDerivAt).fderiv]; rfl
  have hWgen : ∀ v, IsInXi H x (v - α v • A - β v • B) := by
    intro v
    simp only [hαdef, hβdef, ContinuousLinearMap.smul_apply, ka_liouvilleCLM_apply, smul_eq_mul]
    constructor
    · unfold liouville
      rw [ka_om_sub_right, ka_om_sub_right]
      simp only [A, B, hyx, ka_om_smul_right]
      have h1 : omega0 x x = 0 := ka_om_self x
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h1, h2]; field_simp; ring
    · simp only [A, B, map_sub, map_smul, smul_eq_mul, hRH, hyx]
      field_simp; ring
  have key := ka_hol_abstract A B (IsInXi H x) (J x) α β hWgen
    (fun w hw => (hJ.2 x hx w w hw hw).1)
    (by
      simp only [hαdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hyx]
      field_simp
      rfl)
    (by simp only [hαdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, map_smul, hRH]; ring)
    (by
      simp only [hβdef, A, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply, hyx]
      unfold liouville; simp only [ka_om_smul_right, ka_om_self]; ring)
    (by
      simp only [hβdef, B, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply]
      unfold liouville; simp only [ka_om_smul_right]
      have h2 : omega0 x R = 2 := by unfold liouville at hR1; linarith
      rw [h2]; field_simp)
    (fun w hw => by
      simp only [hαdef, ContinuousLinearMap.smul_apply, smul_eq_mul, hw.2]; ring)
    (fun w hw => by
      simp only [hβdef, ContinuousLinearMap.smul_apply, smul_eq_mul, ka_liouvilleCLM_apply, hw.1]; ring)
    (fun w hw => by simp only [B]; rw [ka_om_smul_left, hRw w hw.2]; ring)
    us ut hhol
  obtain ⟨e1, e2, e3, e4⟩ := key
  set W := ut - α ut • A - β ut • B
  have hPW : IsInXi H x W := hWgen ut
  have hm : 0 ≤ omega0 W (J x W) := by
    by_cases h0 : W = 0
    · rw [h0, map_zero, ka_om_self]
    · exact ((hJ.2 x hx W W hPW hPW).2.2.1 h0).le
  have hLs : liouville x (r • (us - α us • A)) = β us := by
    rw [← ka_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  have hLt : liouville x (r • (ut - α ut • A)) = β ut := by
    rw [← ka_liouvilleCLM_apply]; simp only [map_smul, map_sub, hLA, hβdef]; simp
  refine ⟨?_, ?_⟩
  · rw [hdsa, hdtw, hLt, e1]
  · rw [hdta, hdsw, hLs, e2]



namespace KAo
open FiniteEnergyPlane
variable {n : ℕ}

/-- `j0` as a continuous linear map. -/
noncomputable def j0L : V n →L[ℝ] V n :=
  LinearMap.toContinuousLinearMap
    { toFun := j0, map_add' := ka_j0_add, map_smul' := ka_j0_smul }

/-- `ω₀` as a continuous bilinear map. -/
noncomputable def omegaL : V n →L[ℝ] V n →L[ℝ] ℝ :=
  ∑ k, ((ContinuousLinearMap.proj k).comp j0L).smulRight
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (2 * (n + 1)) => ℝ) k)

theorem omegaL_apply (u v : V n) : omegaL u v = omega0 u v := by
  simp [omegaL, omega0, dot, ContinuousLinearMap.sum_apply, j0L]

end KAo

/-!
# T2 glue: the time change between the Hamiltonian and Reeb parametrizations

For `σ(t) = ∫₀ᵗ a` with `a = b ∘ σ`, `a, b` continuous and positive, the rescaled time change
`ρ(τ) = σ(Tτ)/σ(T)` is a homeomorphism of `[0, 1]` fixing the endpoints.
-/


namespace T2G

theorem reparam (a b : ℝ → ℝ) (ha : Continuous a) (hb : Continuous b)
    (hbpos : ∀ r, 0 < b r) (hab : ∀ t, a t = b (∫ s in (0 : ℝ)..t, a s))
    (T : ℝ) (hT : 0 < T) :
    let σ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, a s
    let ρ : ℝ → ℝ := fun τ => σ (T * τ) / σ T
    0 < σ T ∧ ContinuousOn ρ (Icc 0 1) ∧ MapsTo ρ (Icc 0 1) (Icc 0 1) ∧ ρ 0 = 0 ∧ ρ 1 = 1 ∧
      ∃ χ : ℝ → ℝ, ContinuousOn χ (Icc 0 1) ∧ MapsTo χ (Icc 0 1) (Icc 0 1) ∧ χ 0 = 0 ∧
        χ 1 = 1 ∧ ∀ t ∈ Icc (0 : ℝ) 1, ρ (χ t) = t := by
  intro σ ρ
  have hapos : ∀ t, 0 < a t := fun t => by rw [hab t]; exact hbpos _
  have hσd : ∀ t, HasDerivAt σ (a t) t := fun t => (ha.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hσm : StrictMono σ := strictMono_of_hasDerivAt_pos hσd hapos
  have hσ0 : σ 0 = 0 := by simp [σ]
  have hσc : Continuous σ := continuous_iff_continuousAt.2 fun t => (hσd t).continuousAt
  set κ : ℝ → ℝ := fun s => ∫ r in (0 : ℝ)..s, 1 / b r with hκ
  have hic : Continuous fun r => 1 / b r :=
    continuous_const.div hb fun r => (hbpos r).ne'
  have hκd : ∀ s, HasDerivAt κ (1 / b s) s := fun s =>
    (hic.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hκm : StrictMono κ := strictMono_of_hasDerivAt_pos hκd fun s => by
    have := hbpos s; positivity
  have hκ0 : κ 0 = 0 := by simp [κ]
  have hκc : Continuous κ := continuous_iff_continuousAt.2 fun t => (hκd t).continuousAt
  -- `κ ∘ σ = id`
  have hκσ : ∀ t, κ (σ t) = t := by
    have hd : ∀ t, HasDerivAt (fun t => κ (σ t) - t) 0 t := fun t => by
      have h2 : HasDerivAt (fun t => κ (σ t) - t) (1 / b (σ t) * a t - 1) t :=
        ((hκd (σ t)).comp t (hσd t)).sub (hasDerivAt_id t)
      have hab' : a t = b (σ t) := hab t
      refine h2.congr_deriv ?_
      rw [hab']; have := hbpos (σ t); field_simp; ring
    have hc := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
      (fun t => (hd t).deriv)
    intro t
    have := hc t 0
    simp only [hσ0, hκ0, sub_zero] at this
    linarith
  have hσκ : ∀ s, σ (κ s) = s := fun s => hκm.injective (hκσ (κ s))
  have hT' : 0 < σ T := by rw [← hσ0]; exact hσm hT
  refine ⟨hT', ?_, ?_, ?_, ?_, ?_⟩
  · exact ((hσc.comp (continuous_const.mul continuous_id)).div_const _).continuousOn
  · rintro τ ⟨h0, h1⟩
    refine ⟨div_nonneg ?_ hT'.le, (div_le_one hT').2 ?_⟩
    · rw [← hσ0]; exact hσm.monotone (by positivity)
    · exact hσm.monotone (by nlinarith)
  · simp [ρ, hσ0]
  · simp [ρ, hT'.ne']
  · refine ⟨fun u => κ (σ T * u) / T, ?_, ?_, ?_, ?_, ?_⟩
    · exact ((hκc.comp (continuous_const.mul continuous_id)).div_const _).continuousOn
    · rintro u ⟨h0, h1⟩
      refine ⟨div_nonneg ?_ hT.le, (div_le_one hT).2 ?_⟩
      · rw [← hκ0]; exact hκm.monotone (by positivity)
      · exact (hκm.monotone (show σ T * u ≤ σ T by nlinarith)).trans_eq (hκσ T)
    · simp [hκ0]
    · simp only [mul_one, hκσ]; exact div_self hT.ne'
    · intro t _
      simp only [ρ]
      rw [mul_div_cancel₀ _ hT.ne', hσκ]
      field_simp

end T2G

/-!
# T2 glue: coordinates of a frame of `ξ` in the global frame

`t2gM H y L` is the matrix whose columns are the global-frame coordinates of the two vectors
`L e₁, L e₂` of a frame `L : ℝ² → ξ_y`.
-/


namespace FiniteEnergyPlane

noncomputable section

/-- Global-frame coordinates of the frame `L`. -/
def t2gM (H : V 1 → ℝ) (y : V 1) (L : CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i k =>
    HryniewiczCriterion.xiCoords H y (L (EuclideanSpace.single (finSumFinEquiv.symm k) 1)) i

lemma t2g_E0 : (finSumFinEquiv.symm (0 : Fin 2) : Fin 1 ⊕ Fin 1) = Sum.inl 0 := rfl
lemma t2g_E1 : (finSumFinEquiv.symm (1 : Fin 2) : Fin 1 ⊕ Fin 1) = Sum.inr 0 := rfl

lemma t2g_xiCoords_lin (H : V 1 → ℝ) (y u v : V 1) (a b : ℝ) :
    HryniewiczCriterion.xiCoords H y (a • u + b • v) =
      a • HryniewiczCriterion.xiCoords H y u + b • HryniewiczCriterion.xiCoords H y v := by
  funext i
  fin_cases i <;>
    simp [HryniewiczCriterion.xiCoords, HryniewiczCriterion.omega0] <;> ring

lemma t2g_vec_decomp (w : CauchyRiemannIndex.Vec 1) :
    w = w (Sum.inl 0) • EuclideanSpace.single (Sum.inl 0) 1 +
      w (Sum.inr 0) • EuclideanSpace.single (Sum.inr 0) 1 := by
  ext i
  rcases i with i | i <;> fin_cases i <;> simp

lemma t2g_coords_apply (H : V 1 → ℝ) (y : V 1) (L : CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (w : CauchyRiemannIndex.Vec 1) (i : Fin 2) :
    HryniewiczCriterion.xiCoords H y (L w) i =
      ∑ k, t2gM H y L i k * w (finSumFinEquiv.symm k) := by
  conv_lhs => rw [t2g_vec_decomp w]
  rw [map_add, map_smul, map_smul, t2g_xiCoords_lin]
  simp only [Fin.sum_univ_two, t2gM, Matrix.of_apply, t2g_E0, t2g_E1, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

lemma t2g_matrix (H : V 1 → ℝ) (y : V 1) (L : CauchyRiemannIndex.Vec 1 →L[ℝ] V 1)
    (A : CauchyRiemannIndex.Mat 1) (c : Fin 2 → CauchyRiemannIndex.Vec 1) :
    (Matrix.of fun i j =>
        HryniewiczCriterion.xiCoords H y (L (Matrix.toEuclideanLin A (c j))) i) =
      t2gM H y L * Matrix.reindex finSumFinEquiv finSumFinEquiv A *
        Matrix.of (fun l j => c j (finSumFinEquiv.symm l)) := by
  ext i j
  rw [Matrix.of_apply, t2g_coords_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_sum_type, Fin.sum_univ_one, t2g_E0, t2g_E1, PiLp.toLp_apply]
  rw [Fin.sum_univ_two]
  simp only [t2g_E0, t2g_E1]
  ring

lemma t2g_omega_self (u : V 1) : HryniewiczCriterion.omega0 u u = 0 := by
  simp [HryniewiczCriterion.omega0]; ring

section point

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {y : V 1} (hy : H y = 1)

include hH hy in
/-- The global frame has coordinates `Id`. -/
lemma t2g_frame_coords :
    (Matrix.of fun i j => HryniewiczCriterion.xiCoords H y
      (![HryniewiczCriterion.xiFrame1 H y, HryniewiczCriterion.xiFrame2 H y] j) i) = 1 := by
  have e12 := r26d_e12 hH hy
  rw [r26de] at e12
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [HryniewiczCriterion.xiCoords, e12, t2g_omega_self]

include hH hy in
lemma t2g_det (L : CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hL : ∀ a, IsInXi H y (L a))
    (hω : ∀ a b, omega0 (L a) (L b) =
      inner ℝ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) b) :
    (t2gM H y L).det = 1 := by
  rw [Matrix.det_fin_two]
  simp only [t2gM, Matrix.of_apply, t2g_E0, t2g_E1, HryniewiczCriterion.xiCoords]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  set u := L (EuclideanSpace.single (Sum.inl 0) 1)
  set w := L (EuclideanSpace.single (Sum.inr 0) 1)
  have du := r26d_decomp hH hy (hL (EuclideanSpace.single (Sum.inl 0) 1))
  have dw := r26d_decomp hH hy (hL (EuclideanSpace.single (Sum.inr 0) 1))
  rw [r26de] at du dw
  set Z1 := HryniewiczCriterion.xiFrame1 H y
  set Z2 := HryniewiczCriterion.xiFrame2 H y
  have e12 : HryniewiczCriterion.omega0 Z1 Z2 = 1 := r26d_e12 hH hy
  set a := HryniewiczCriterion.omega0 u Z2
  set b := HryniewiczCriterion.omega0 Z1 u
  set c := HryniewiczCriterion.omega0 w Z2
  set d := HryniewiczCriterion.omega0 Z1 w
  have huw : HryniewiczCriterion.omega0 u w = a * d - b * c := by
    have : HryniewiczCriterion.omega0 (a • Z1 + b • Z2) (c • Z1 + d • Z2) = a * d - b * c := by
      unfold HryniewiczCriterion.omega0 at e12 ⊢
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (a * d - b * c) * e12
    calc HryniewiczCriterion.omega0 u w
        = HryniewiczCriterion.omega0 (a • Z1 + b • Z2) (c • Z1 + d • Z2) := by rw [← du, ← dw]
      _ = a * d - b * c := this
  have h1 : HryniewiczCriterion.omega0 u w = 1 := by
    rw [← r26d_omega0_eq, hω]
    simp [Matrix.toEuclideanLin_apply, Matrix.J, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      PiLp.inner_apply, Matrix.fromBlocks]
  rw [huw] at h1
  linear_combination h1

end point

end

end FiniteEnergyPlane

/-!
# T2: the index of the linearized Hamiltonian flow equals the index of `Ψ`

Glue of the three children: the time change (`hamiltonianFlow_reeb_timeChange`), the frame
identity (`linReebFlow_unitaryFrame_eq`) and the frame-change invariance
(`czIndexOfPath_conj_of_loop`), with `windingInterval_reparam`.
-/


namespace FiniteEnergyPlane

noncomputable section

lemma t2g_det_symp (A : CauchyRiemannIndex.Mat 1) (hA : CauchyRiemannIndex.IsSymplectic A) :
    A.det = 1 := by
  have h := (SymplecticGroup.mem_iff (A := A)).1 hA
  have h' := congrFun (congrFun h (Sum.inl 0 : Fin 1 ⊕ Fin 1)) (Sum.inr 0 : Fin 1 ⊕ Fin 1)
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
    Matrix.transpose_apply] at h'
  have hd : A.det = A (Sum.inl 0) (Sum.inl 0) * A (Sum.inr 0) (Sum.inr 0) -
      A (Sum.inl 0) (Sum.inr 0) * A (Sum.inr 0) (Sum.inl 0) := by
    rw [← Matrix.det_reindex_self finSumFinEquiv A, Matrix.det_fin_two]
    simp [Matrix.reindex_apply, Matrix.submatrix_apply]
    rfl
  rw [hd]
  linarith

lemma t2g_hamVF (H₀ : HryniewiczCriterion.R4 → ℝ) (y : V 1) :
    hamVF H₀ y = HryniewiczCriterion.hamiltonianVectorField H₀ y := by
  funext k
  fin_cases k <;>
    simp [hamVF, j0, grad, HryniewiczCriterion.hamiltonianVectorField,
      HryniewiczCriterion.partialDeriv] <;> rfl

lemma t2g_liouville (x v : V 1) : liouville x v = HryniewiczCriterion.liouvilleForm x v := by
  rw [liouville, r26d_omega0_eq]; simp [HryniewiczCriterion.liouvilleForm, HryniewiczCriterion.omega0]

lemma t2g_reebProj (H : V 1 → ℝ) (y v : V 1) :
    HryniewiczCriterion.reebProjection H y v = piXi H y v := by
  rw [HryniewiczCriterion.reebProjection, piXi, reeb, ← t2g_hamVF, ← t2g_liouville,
    ← t2g_liouville, smul_smul, div_eq_mul_inv]

lemma t2g_f_cont (H : V 1 → ℝ) (hH : ContDiff ℝ ∞ H) :
    Continuous (fun y => liouville y (hamVF H y)) := by
  have hL : (fun x => liouville x (hamVF H x)) = fun x => liouvilleCLM x (hamVF H x) := by
    funext x; rw [ka_liouvilleCLM_apply]
  rw [hL]; exact (ka_liouvilleCLM_contDiff.clm_apply (ka_hamVF_contDiff H hH)).continuous

lemma t2g_const_wind (z : ℂ) (hz : z ≠ 0) : HasLoopWind (fun _ => z) 0 :=
  ⟨continuous_const, fun _ => rfl, fun _ => hz, fun _ => Complex.arg z, continuous_const,
    fun _ => (Complex.norm_mul_exp_arg_mul_I z).symm, by simp⟩

lemma t2g_vecToC_single (k : Fin 2) :
    vecToC (EuclideanSpace.single (finSumFinEquiv.symm k) 1) ≠ 0 := by
  fin_cases k <;> simp [vecToC, Complex.ext_iff, t2g_E0, t2g_E1]

theorem t2g_core (H : V 1 → ℝ) (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (P : HryniewiczCriterion.PeriodicOrbit H) (Q : ReebOrbit H)
    (hT : Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (n := 1) (P.x τ) (deriv P.x τ))
    (h0 : Q.x 0 = P.x 0) (hnd : Q.IsNondegenerate)
    (Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1) (hZ : IsUnitaryXiFrame J Q Z)
    (hwind : ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind Q (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k))
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSym : CauchyRiemannIndex.IsSymLoop Sinf)
    (hA : ∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J Q (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t)))
    (Ψ : ℝ → CauchyRiemannIndex.Mat 1) (hΨ : CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ)
    (Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4))
    (hY : HryniewiczCriterion.IsLinearizedFlow H P.x Y) :
    HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H P Y) =
      HryniewiczCriterion.czIndexOfPath (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)) := by
  have hH : IsStrictlyStarShapedLevel H := hH₀
  have eX : hamVF H = HryniewiczCriterion.hamiltonianVectorField H := funext (t2g_hamVF H)
  have hx : ∀ t, HasDerivAt P.x (hamVF H (P.x t)) t := fun t => by
    rw [eX]; exact P.trajectory.1 t
  have hxS : ∀ t, P.x t ∈ energySurface H := fun t => P.trajectory.2 t
  have hYB : ∀ t, HasDerivAt Y ((fderiv ℝ (hamVF H) (P.x t)).comp (Y t)) t := fun t => by
    rw [eX]; exact hY.2 t
  obtain ⟨⟨Φ, hΦ, -⟩, -⟩ := linReebFlow_spec H hH Q
  set σ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, liouville (n := 1) (P.x s) (hamVF H (P.x s)) with hσ
  have hB : ∀ t : ℝ, Q.x (σ t) = P.x t ∧
      ∀ v : V 1, IsInXi H (P.x 0) v → piXi H (P.x t) (Y t v) = Φ (σ t) v :=
    hamiltonianFlow_reeb_timeChange H hH P.x hx hxS Q h0 Y hY.1 hYB Φ hΦ
  have hAZ := linReebFlow_unitaryFrame_eq H hH J Q Z hZ Sinf hA Ψ hΨ Φ hΦ
  -- the time change
  set f : V 1 → ℝ := fun y => liouville y (hamVF H y) with hf
  have hfc : Continuous f := t2g_f_cont H hH.1
  have hPc : Continuous P.x := continuous_iff_continuousAt.2 fun t => (hx t).continuousAt
  have hQc : Continuous Q.x :=
    continuous_iff_continuousAt.2 fun t => (Q.hasDerivAt t).continuousAt
  have hR := T2G.reparam (fun t => f (P.x t)) (fun r => f (Q.x r)) (hfc.comp hPc)
    (hfc.comp hQc) (fun r => (ka_reeb_spec H hH _ (Q.mem r)).1)
    (fun t => by simp only [f]; rw [(hB t).1]) P.T P.T_pos
  set ρ : ℝ → ℝ := fun τ => σ (P.T * τ) / σ P.T with hρ
  obtain ⟨hσT, hρc, hρm, hρ0, hρ1, χ, hχc, hχm, hχ0, hχ1, hρχ⟩ := hR
  replace hσT : 0 < σ P.T := hσT
  replace hρc : ContinuousOn ρ (Icc 0 1) := hρc
  replace hρm : MapsTo ρ (Icc 0 1) (Icc 0 1) := hρm
  replace hρ0 : ρ 0 = 0 := hρ0
  replace hρ1 : ρ 1 = 1 := hρ1
  replace hρχ : ∀ t ∈ Icc (0 : ℝ) 1, ρ (χ t) = t := hρχ
  have hTσ : Q.T = σ P.T := by
    rw [hT]
    exact intervalIntegral.integral_congr fun τ _ => by simp only [(hx τ).deriv]
  have hστ : ∀ τ, σ (P.T * τ) = Q.T * ρ τ := fun τ => by
    simp only [ρ]; rw [hTσ, mul_div_cancel₀ _ hσT.ne']
  -- the frame at `t = 0`
  have hP0 : H (P.x 0) = 1 := P.trajectory.2 0
  have he : ∀ j, IsInXi H (P.x 0)
      (![HryniewiczCriterion.xiFrame1 H (P.x 0), HryniewiczCriterion.xiFrame2 H (P.x 0)] j) := by
    intro j; fin_cases j
    · exact r26d_e_xi hH hP0
    · exact r26d_e2_xi hH hP0
  have hQ0 : Q.x (Q.T * 0) = P.x 0 := by rw [mul_zero, h0]
  have hc : ∀ j, ∃ a, Z 0 a =
      ![HryniewiczCriterion.xiFrame1 H (P.x 0), HryniewiczCriterion.xiFrame2 H (P.x 0)] j :=
    fun j => (hZ.2.2 0).2.1 _ (by rw [hQ0]; exact he j)
  choose c hc using hc
  set G : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun s => t2gM H (Q.x (Q.T * s)) (Z s) with hG
  set φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun s => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ s) with hφ
  set C : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun l j => c j (finSumFinEquiv.symm l) with hC
  have key : ∀ τ, HryniewiczCriterion.linearizedXiPath H P Y τ = G (ρ τ) * φ (ρ τ) * C := by
    intro τ
    simp only [G, φ, C]
    rw [← t2g_matrix]
    ext i j
    simp only [HryniewiczCriterion.linearizedXiPath, Matrix.of_apply]
    rw [t2g_reebProj, (hB (P.T * τ)).2 _ (he j), ← (hB (P.T * τ)).1, hστ, ← hc j, hAZ]
  have hL0 : HryniewiczCriterion.linearizedXiPath H P Y 0 = 1 := by
    rw [← t2g_frame_coords hH hP0]
    ext i j
    simp only [HryniewiczCriterion.linearizedXiPath, Matrix.of_apply, mul_zero, hY.1,
      ContinuousLinearMap.id_apply]
    rw [t2g_reebProj, piXi, (he j).1, zero_smul, sub_zero]
  have hφ0 : φ 0 = 1 := by
    simp only [φ, hΨ.1]; simp [Matrix.reindex_apply, Matrix.submatrix_one_equiv]
  have hGC : G 0 * C = 1 := by
    have := key 0
    rw [hL0, hρ0, hφ0, Matrix.mul_one] at this
    exact this.symm
  have hCinv : C = (G 0)⁻¹ := (Matrix.inv_eq_right_inv hGC).symm
  -- determinants and continuity
  have hGd : ∀ t, (G t).det = 1 := fun t =>
    t2g_det hH (Q.mem _) (Z t) (hZ.2.2 t).1 (hZ.2.2 t).2.2.2
  have hcol : ∀ k : Fin 2, Continuous fun t =>
      xiCoordC H (Q.x (Q.T * t)) (Z t (EuclideanSpace.single (finSumFinEquiv.symm k) 1)) := by
    intro k
    have hw := (hwind (fun _ => EuclideanSpace.single (finSumFinEquiv.symm k) 1)
      continuous_const (fun _ => rfl) (fun _ h => t2g_vecToC_single k (by rw [h]; rfl)) 0).2
      (t2g_const_wind _ (t2g_vecToC_single k))
    exact hw.1
  have hGcont : Continuous G := by
    apply continuous_matrix
    intro i k
    fin_cases i
    · exact Complex.continuous_re.comp (hcol k)
    · exact Complex.continuous_im.comp (hcol k)
  have hΨc : Continuous Ψ := continuous_matrix fun i j => continuous_iff_continuousAt.2 fun s =>
    (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hΨ.2 s) i) j).continuousAt
  have hφc : Continuous φ := hΨc.matrix_reindex _ _
  have hφd : ∀ t, (φ t).det = 1 := fun t => by
    simp only [φ]
    rw [Matrix.det_reindex_self]
    exact t2g_det_symp _ (CauchyRiemannIndex.fundamentalSolution_symplectic 1 Sinf hSym.2.2 Ψ hΨ t)
  have hG1 : G 1 = G 0 := by
    have h1 : Q.x (Q.T * 1) = Q.x (Q.T * 0) := by
      rw [mul_one, mul_zero]; simpa using Q.periodic 0
    have h2 : Z 1 = Z 0 := by simpa using hZ.2.1 0
    simp only [G]; rw [h1, h2]
  -- coordinates of `Z t a` through `G t`
  have hGv : ∀ t (a : CauchyRiemannIndex.Vec 1),
      G t *ᵥ (fun k => a (finSumFinEquiv.symm k)) =
        HryniewiczCriterion.xiCoords H (Q.x (Q.T * t)) (Z t a) := fun t a => by
    funext i; rw [t2g_coords_apply]; rfl
  -- nondegeneracy
  have hφ1 : (1 - φ 1).det ≠ 0 := by
    intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    set a : CauchyRiemannIndex.Vec 1 := WithLp.toLp 2 (fun l => v (finSumFinEquiv l)) with ha
    have hav : (fun k => a (finSumFinEquiv.symm k)) = v := by
      funext k; simp [a]
    have hΨa : Matrix.toEuclideanLin (Ψ 1) a = a := by
      have e0 := congrFun hv 0
      have e1 := congrFun hv 1
      simp [φ, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.reindex_apply,
        Matrix.sub_apply, Matrix.one_apply, t2g_E0, t2g_E1] at e0 e1
      have f0 : (finSumFinEquiv (Sum.inl 0 : Fin 1 ⊕ Fin 1) : Fin 2) = 0 := rfl
      have f1 : (finSumFinEquiv (Sum.inr 0 : Fin 1 ⊕ Fin 1) : Fin 2) = 1 := rfl
      ext l
      rcases l with l | l <;> fin_cases l <;>
        simp [a, Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct,
          Fintype.sum_sum_type, f0, f1] <;> linarith
    have hfix : Φ Q.T (Z 0 a) = Z 0 a := by
      have := hAZ 1 a
      rw [mul_one, hΨa, show Z 1 = Z 0 by simpa using hZ.2.1 0] at this
      exact this
    have hxi : IsInXi H (Q.x 0) (Z 0 a) := by
      have := (hZ.2.2 0).1 a; rwa [mul_zero] at this
    have hz := hnd Φ hΦ _ hxi hfix
    have : G 0 *ᵥ v = 0 := by
      rw [← hav, hGv, hz]
      funext i; fin_cases i <;> simp [HryniewiczCriterion.xiCoords, HryniewiczCriterion.omega0]
    have hd0 := Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, this⟩
    rw [hGd 0] at hd0; exact one_ne_zero hd0
  -- the winding of `G t G(0)⁻¹ e₁`
  have hunit : IsUnit (G 0).det := by rw [hGd 0]; exact isUnit_one
  set w : Fin 2 → ℝ := (G 0)⁻¹ *ᵥ HryniewiczCriterion.rotationVector 0 with hw
  set ĉ : CauchyRiemannIndex.Vec 1 := WithLp.toLp 2 (fun l => w (finSumFinEquiv l)) with hĉ
  have hĉw : (fun k => ĉ (finSumFinEquiv.symm k)) = w := by funext k; simp [ĉ]
  have hĉ0 : vecToC ĉ ≠ 0 := by
    intro h
    have hw0 : w = 0 := by
      funext k
      have h1 := congrArg Complex.re h
      have h2 := congrArg Complex.im h
      simp [vecToC, ĉ] at h1 h2
      fin_cases k
      · exact h1
      · exact h2
    have : HryniewiczCriterion.rotationVector 0 = 0 := by
      rw [← Matrix.one_mulVec (HryniewiczCriterion.rotationVector 0),
        ← Matrix.mul_nonsing_inv _ hunit, ← Matrix.mulVec_mulVec, ← hw, hw0, Matrix.mulVec_zero]
    have := congrFun this 0
    simp [HryniewiczCriterion.rotationVector] at this
  obtain ⟨-, -, hf0, θ, hθc, hθ, hθ1⟩ := (hwind (fun _ => ĉ) continuous_const (fun _ => rfl)
    (fun _ h => hĉ0 (by rw [h]; rfl)) 0).2 (t2g_const_wind _ hĉ0)
  have hθt : ∀ t ∈ Icc (0 : ℝ) 1, ∃ r : ℝ, 0 < r ∧
      (G t * (G 0)⁻¹).mulVec (HryniewiczCriterion.rotationVector 0) =
        r • HryniewiczCriterion.rotationVector (θ t) := by
    intro t _
    set z := xiCoordC H (Q.x (Q.T * t)) (Z t ĉ) with hz
    refine ⟨‖z‖, norm_pos_iff.2 (hf0 t), ?_⟩
    have hzt : z = (‖z‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I) := hθ t
    rw [← Matrix.mulVec_mulVec, ← hw, ← hĉw, hGv]
    have hre := congrArg Complex.re hzt
    have him := congrArg Complex.im hzt
    rw [Complex.exp_mul_I] at hre him
    simp only [← Complex.ofReal_cos, ← Complex.ofReal_sin] at hre him
    simp [Complex.mul_re, Complex.mul_im] at hre him
    funext i
    fin_cases i
    · simp [HryniewiczCriterion.rotationVector]; exact hre
    · simp [HryniewiczCriterion.rotationVector]; exact him
  -- assembly
  set F : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun s => G s * φ s * (G 0)⁻¹ with hF
  have hfun : HryniewiczCriterion.linearizedXiPath H P Y = fun τ => F (ρ τ) := by
    funext τ; rw [key, hCinv]
  have hrep := HryniewiczCriterion.windingInterval_reparam F ρ χ hρc hρm hρ0 hρ1 hχc hχm hχ0 hχ1
    hρχ
  have hconj := HryniewiczCriterion.czIndexOfPath_conj_of_loop φ G hφc.continuousOn hφ0
    (fun t _ => hφd t) hφ1 hGcont.continuousOn (fun t _ => hGd t) hG1 θ hθc.continuousOn
    (by have := hθ1; simp at this; linarith) hθt
  rw [hfun]
  calc HryniewiczCriterion.czIndexOfPath (fun τ => F (ρ τ))
      = HryniewiczCriterion.czIndexOfPath F := by
        unfold HryniewiczCriterion.czIndexOfPath; rw [hrep]
    _ = HryniewiczCriterion.czIndexOfPath φ := hconj

end

theorem czIndexOfPath_linearizedXiPath_eq_aux (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1,
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.x 0 = toV (P.x 0) →
      Q.IsNondegenerate →
      ∀ Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1, IsUnitaryXiFrame J Q Z →
      (∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind Q (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k)) →
      ∀ Sinf : ℝ → CauchyRiemannIndex.Mat 1, CauchyRiemannIndex.IsSymLoop Sinf →
      (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) →
      (∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J Q (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t))) →
      ∀ Ψ : ℝ → CauchyRiemannIndex.Mat 1, CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ →
      ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
        HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
        HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y) =
          HryniewiczCriterion.czIndexOfPath
            (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)) := by
  intro toV H J P Q _ hT h0 hnd Z hZ hwind Sinf hSym _ hA Ψ hΨ Y hY
  exact t2g_core H₀ hH₀ J P Q hT h0 hnd Z hZ hwind Sinf hSym hA Ψ hΨ Y hY

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H₀ : HryniewiczCriterion.R4 → ℝ)
    (hH₀ : HryniewiczCriterion.IsStrictlyStarShapedLevel H₀) :
    let toV : HryniewiczCriterion.R4 → V 1 := fun x k => x (Fin.cast (by norm_num) k)
    let H : V 1 → ℝ := fun y => H₀ (fun k => y (Fin.cast (by norm_num) k))
    ∀ J : V 1 → V 1 →L[ℝ] V 1,
    ∀ (P : HryniewiczCriterion.PeriodicOrbit H₀) (Q : ReebOrbit H),
      Set.range Q.x = Set.range (fun τ => toV (P.x τ)) →
      Q.T = ∫ τ in (0 : ℝ)..P.T, liouville (toV (P.x τ)) (deriv (fun s => toV (P.x s)) τ) →
      Q.x 0 = toV (P.x 0) →
      Q.IsNondegenerate →
      ∀ Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1, IsUnitaryXiFrame J Q Z →
      (∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind Q (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k)) →
      ∀ Sinf : ℝ → CauchyRiemannIndex.Mat 1, CauchyRiemannIndex.IsSymLoop Sinf →
      (∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) →
      (∀ η : ℝ → CauchyRiemannIndex.Vec 1, ContDiff ℝ ∞ η → Function.Periodic η 1 →
        ∀ t : ℝ, asympOp J Q (fun t => Z t (η t)) t =
          Z t (-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) (deriv η t)) -
            Matrix.toEuclideanLin (Sinf t) (η t))) →
      ∀ Ψ : ℝ → CauchyRiemannIndex.Mat 1, CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ →
      ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
        HryniewiczCriterion.IsLinearizedFlow H₀ P.x Y →
        HryniewiczCriterion.czIndexOfPath (HryniewiczCriterion.linearizedXiPath H₀ P Y) =
          HryniewiczCriterion.czIndexOfPath
            (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)) :=
  FiniteEnergyPlane.czIndexOfPath_linearizedXiPath_eq_aux H₀ hH₀
