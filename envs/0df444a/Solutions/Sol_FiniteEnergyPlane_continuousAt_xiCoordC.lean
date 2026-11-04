-- Prove2me | solution 1 for FiniteEnergyPlane.continuousAt_xiCoordC
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-03T08:49:31.050381+00:00
-- url     : https://prove2.me/submissions/355399df-4d96-4fa2-a1ca-32b171cd590b

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_triangular_iff
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x



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

open scoped ContDiff

lemma r26_omega0_eq (u v : V 1) : omega0 u v = HryniewiczCriterion.omega0 u v := by
  simp [omega0, HryniewiczCriterion.omega0, dot, j0, Fin.sum_univ_four]; ring

lemma r26_omega0_bilin (a b c d : HryniewiczCriterion.R4) (p q r s : ℝ) :
    HryniewiczCriterion.omega0 (p • a + q • b) (r • c + s • d) =
      p * r * HryniewiczCriterion.omega0 a c + p * s * HryniewiczCriterion.omega0 a d +
      q * r * HryniewiczCriterion.omega0 b c + q * s * HryniewiczCriterion.omega0 b d := by
  simp [HryniewiczCriterion.omega0]; ring

lemma r26_J0_inl (a : CauchyRiemannIndex.Vec 1) :
    Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a (Sum.inl 0) = -a (Sum.inr 0) := by
  simp [Matrix.J, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Matrix.fromBlocks]

lemma r26_J0_inr (a : CauchyRiemannIndex.Vec 1) :
    Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a (Sum.inr 0) = a (Sum.inl 0) := by
  simp [Matrix.J, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Matrix.fromBlocks]

lemma r26_isInXi_comb {H : V 1 → ℝ} {x u v : V 1} (hu : IsInXi H x u) (hv : IsInXi H x v)
    (p q : ℝ) : IsInXi H x (p • u + q • v) := by
  obtain ⟨hu1, hu2⟩ := hu
  obtain ⟨hv1, hv2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [liouville, r26_omega0_eq] at hu1 hv1 ⊢
    have e : HryniewiczCriterion.omega0 x (p • u + q • v) =
        p * HryniewiczCriterion.omega0 x u + q * HryniewiczCriterion.omega0 x v := by
      simp [HryniewiczCriterion.omega0]; ring
    rw [e]
    have h1 : HryniewiczCriterion.omega0 x u = 0 := by linarith
    have h2 : HryniewiczCriterion.omega0 x v = 0 := by linarith
    rw [h1, h2]; simp
  · rw [map_add, map_smul, map_smul, hu2, hv2]; simp

/-! ### The frame at a point of `S` -/

/-- `Z₁(x)`, the first vector of the global frame. -/
noncomputable def r26e (H : V 1 → ℝ) (x : V 1) : V 1 := HryniewiczCriterion.xiFrame1 H x

/-- `β(x) = ω₀(Z₁, J Z₁)`. -/
noncomputable def r26β (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) : ℝ :=
  HryniewiczCriterion.omega0 (r26e H x) (J x (r26e H x))

/-- `W = β^{-1/2} Z₁`. -/
noncomputable def r26W (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) : V 1 :=
  (Real.sqrt (r26β H J x))⁻¹ • r26e H x

/-- `Z(x) a = a₁ W + a₂ J W`. -/
noncomputable def r26ZAt (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1) :
    CauchyRiemannIndex.Vec 1 →L[ℝ] V 1 :=
  (EuclideanSpace.proj (Sum.inl 0 : Fin 1 ⊕ Fin 1)).smulRight (r26W H J x) +
    (EuclideanSpace.proj (Sum.inr 0 : Fin 1 ⊕ Fin 1)).smulRight (J x (r26W H J x))

lemma r26ZAt_apply (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (x : V 1)
    (a : CauchyRiemannIndex.Vec 1) :
    r26ZAt H J x a = a (Sum.inl 0) • r26W H J x + a (Sum.inr 0) • J x (r26W H J x) := by
  simp [r26ZAt]

section point

variable {H : V 1 → ℝ} (hH : IsStrictlyStarShapedLevel H) {J : V 1 → V 1 →L[ℝ] V 1}
  (hJ : IsCompatibleXiStructure H J) {x : V 1} (hx : H x = 1)

include hH hx in
lemma r26_pos : 0 < fderiv ℝ H x x := hH.2.2 x hx

include hH hx in
lemma r26_e12 : HryniewiczCriterion.omega0 (r26e H x) (HryniewiczCriterion.xiFrame2 H x) = 1 :=
  HryniewiczCriterion.r26_omega0_xiFrame12 (r26_pos hH hx)

include hH hx in
lemma r26_e_xi : IsInXi H x (r26e H x) := by
  refine ⟨?_, ?_⟩
  · rw [liouville, r26_omega0_eq, r26e, HryniewiczCriterion.xiFrame1,
      HryniewiczCriterion.r26_omega0_y_xiFrame _ HryniewiczCriterion.r26_omega0_quatQ2]
    simp
  · exact HryniewiczCriterion.r26_dH_xiFrame (r26_pos hH hx) _

include hH hx in
lemma r26_e2_xi : IsInXi H x (HryniewiczCriterion.xiFrame2 H x) := by
  refine ⟨?_, ?_⟩
  · rw [liouville, r26_omega0_eq, HryniewiczCriterion.xiFrame2,
      HryniewiczCriterion.r26_omega0_y_xiFrame _ HryniewiczCriterion.r26_omega0_quatQ1]
    simp
  · exact HryniewiczCriterion.r26_dH_xiFrame (r26_pos hH hx) _

include hH hx in
/-- Every `w ∈ ξ_x` is `ω₀(w, Z₂) Z₁ + ω₀(Z₁, w) Z₂`. -/
lemma r26_decomp {w : V 1} (hw : IsInXi H x w) :
    w = HryniewiczCriterion.omega0 w (HryniewiczCriterion.xiFrame2 H x) • r26e H x +
      HryniewiczCriterion.omega0 (r26e H x) w • HryniewiczCriterion.xiFrame2 H x := by
  have hpos := r26_pos hH hx
  have xi_a : ∀ v, IsInXi H x v → HryniewiczCriterion.omega0 v x = 0 := by
    intro v hv
    have := hv.1
    rw [liouville, r26_omega0_eq] at this
    rw [HryniewiczCriterion.r26_omega0_antisymm]; linarith
  have xi_b : ∀ v, IsInXi H x v →
      HryniewiczCriterion.omega0 v (HryniewiczCriterion.hamiltonianVectorField H x) = 0 := by
    intro v hv
    rw [HryniewiczCriterion.r26_omega0_X_right]; exact hv.2
  have := HryniewiczCriterion.r26_eq_frame_of_omega0 (r26e H x) (HryniewiczCriterion.xiFrame2 H x)
    x (HryniewiczCriterion.hamiltonianVectorField H x) w (r26_e12 hH hx)
    (xi_a _ (r26_e_xi hH hx)) (xi_b _ (r26_e_xi hH hx)) (xi_a _ (r26_e2_xi hH hx))
    (xi_b _ (r26_e2_xi hH hx))
    (by rw [HryniewiczCriterion.r26_omega0_X_right]; exact hpos.ne') (xi_a _ hw) (xi_b _ hw)
  exact this

include hH hJ hx in
lemma r26_β_pos : 0 < r26β H J x := by
  have h := (hJ.2 x hx _ _ (r26_e_xi hH hx) (r26_e_xi hH hx)).2.2.1
  have hne : r26e H x ≠ 0 := by
    intro h0
    have := r26_e12 hH hx
    rw [h0] at this; simp [HryniewiczCriterion.omega0] at this
  have := h hne
  rw [r26_omega0_eq] at this
  exact this

include hH hJ hx in
lemma r26_W_xi : IsInXi H x (r26W H J x) := by
  have := r26_isInXi_comb (r26_e_xi hH hx) (r26_e_xi hH hx) (Real.sqrt (r26β H J x))⁻¹ 0
  simpa [r26W] using this

include hH hJ hx in
lemma r26_JW_xi : IsInXi H x (J x (r26W H J x)) :=
  (hJ.2 x hx _ _ (r26_W_xi hH hJ hx) (r26_W_xi hH hJ hx)).1

include hH hJ hx in
lemma r26_JJW : J x (J x (r26W H J x)) = -r26W H J x :=
  (hJ.2 x hx _ _ (r26_W_xi hH hJ hx) (r26_W_xi hH hJ hx)).2.1

include hH hJ hx in
lemma r26_sqrt_pos : 0 < Real.sqrt (r26β H J x) := Real.sqrt_pos.2 (r26_β_pos hH hJ hx)

include hH hJ hx in
lemma r26_W_JW : HryniewiczCriterion.omega0 (r26W H J x) (J x (r26W H J x)) = 1 := by
  have hs := r26_sqrt_pos hH hJ hx
  have hss : Real.sqrt (r26β H J x) * Real.sqrt (r26β H J x) = r26β H J x :=
    Real.mul_self_sqrt (r26_β_pos hH hJ hx).le
  rw [r26W, map_smul, HryniewiczCriterion.r26_omega0_smul_left,
    HryniewiczCriterion.r26_omega0_smul_right]
  change _ * (_ * r26β H J x) = 1
  rw [inv_mul_eq_div (Real.sqrt _) (r26β H J x), Real.div_sqrt]
  exact inv_mul_cancel₀ hs.ne'

include hH hJ hx in
lemma r26_unitary_xi (a : CauchyRiemannIndex.Vec 1) : IsInXi H x (r26ZAt H J x a) := by
  rw [r26ZAt_apply]; exact r26_isInXi_comb (r26_W_xi hH hJ hx) (r26_JW_xi hH hJ hx) _ _

include hH hJ hx in
lemma r26_unitary_surj (w : V 1) (hw : IsInXi H x w) :
    ∃ a, r26ZAt H J x a = w := by
  set e := r26e H x
  set e2 := HryniewiczCriterion.xiFrame2 H x
  set s := Real.sqrt (r26β H J x)
  set β := r26β H J x
  have hs := r26_sqrt_pos hH hJ hx
  have hβ := r26_β_pos hH hJ hx
  have hJe := r26_decomp hH hx ((hJ.2 x hx _ _ (r26_e_xi hH hx) (r26_e_xi hH hx)).1)
  have hβdef : HryniewiczCriterion.omega0 e (J x e) = β := rfl
  rw [hβdef] at hJe
  set α := HryniewiczCriterion.omega0 (J x e) e2
  set p := HryniewiczCriterion.omega0 w e2
  set q := HryniewiczCriterion.omega0 e w
  have hw' := r26_decomp hH hx hw
  have hβ0 : β ≠ 0 := hβ.ne'
  have hs0 : s ≠ 0 := hs.ne'
  refine ⟨(WithLp.equiv 2 (Fin 1 ⊕ Fin 1 → ℝ)).symm
    (Sum.elim (fun _ => s * (p - q * α / β)) (fun _ => s * q / β)), ?_⟩
  rw [r26ZAt_apply]
  simp only [WithLp.equiv_symm_apply, PiLp.toLp_apply, Sum.elim_inl, Sum.elim_inr]
  rw [r26W, map_smul, hJe]
  conv_rhs => rw [hw']
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

include hH hJ hx in
lemma r26_unitary_J (a : CauchyRiemannIndex.Vec 1) :
    J x (r26ZAt H J x a) =
      r26ZAt H J x (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) := by
  rw [r26ZAt_apply, r26ZAt_apply, r26_J0_inl, r26_J0_inr, map_add, map_smul, map_smul,
    r26_JJW hH hJ hx]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring

include hH hJ hx in
lemma r26_unitary_omega (a b : CauchyRiemannIndex.Vec 1) :
    omega0 (r26ZAt H J x a) (r26ZAt H J x b) =
      inner ℝ (Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ 1) a) b := by
  rw [r26_omega0_eq, r26ZAt_apply, r26ZAt_apply, r26_omega0_bilin,
    HryniewiczCriterion.r26_omega0_self, HryniewiczCriterion.r26_omega0_self,
    HryniewiczCriterion.r26_omega0_antisymm (J x _) (r26W H J x), r26_W_JW hH hJ hx]
  simp only [PiLp.inner_apply, Fintype.sum_sum_type, Fin.sum_univ_one, r26_J0_inl, r26_J0_inr,
    RCLike.inner_apply, conj_trivial]
  ring

include hH hJ hx in
lemma r26_coord (a : CauchyRiemannIndex.Vec 1) :
    xiCoordC H x (r26ZAt H J x a) =
      ((((Real.sqrt (r26β H J x))⁻¹ * a (Sum.inl 0) +
        (Real.sqrt (r26β H J x))⁻¹ *
          HryniewiczCriterion.omega0 (J x (r26e H x)) (HryniewiczCriterion.xiFrame2 H x) *
            a (Sum.inr 0) : ℝ)) : ℂ) +
        ((Real.sqrt (r26β H J x) * a (Sum.inr 0) : ℝ) : ℂ) * Complex.I := by
  have hs := r26_sqrt_pos hH hJ hx
  have hss : Real.sqrt (r26β H J x) * Real.sqrt (r26β H J x) = r26β H J x :=
    Real.mul_self_sqrt (r26_β_pos hH hJ hx).le
  have h12 := r26_e12 hH hx
  have hc : xiCoordC H x (r26ZAt H J x a) =
      ⟨HryniewiczCriterion.omega0 (r26ZAt H J x a) (HryniewiczCriterion.xiFrame2 H x),
        HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame1 H x) (r26ZAt H J x a)⟩ := rfl
  rw [hc]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    rw [r26ZAt_apply, HryniewiczCriterion.r26_omega0_lin_left, r26W, map_smul,
      HryniewiczCriterion.r26_omega0_smul_left, HryniewiczCriterion.r26_omega0_smul_left,
      h12]
    ring
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im]
    change HryniewiczCriterion.omega0 (r26e H x) _ = _
    rw [r26ZAt_apply, HryniewiczCriterion.r26_omega0_lin_right2, r26W, map_smul,
      HryniewiczCriterion.r26_omega0_smul_right, HryniewiczCriterion.r26_omega0_smul_right,
      HryniewiczCriterion.r26_omega0_self]
    change _ * (_ * 0) + _ * (_ * r26β H J x) = _
    rw [inv_mul_eq_div (Real.sqrt _) (r26β H J x), Real.div_sqrt]
    ring

end point

theorem exists_unitaryXiFrame_hasXiLoopWind_iff_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V 1 → V 1 →L[ℝ] V 1)
    (hJ : IsCompatibleXiStructure H J) (P : ReebOrbit H) :
    ∃ Z : ℝ → CauchyRiemannIndex.Vec 1 →L[ℝ] V 1, IsUnitaryXiFrame J P Z ∧
      ∀ ζ : ℝ → CauchyRiemannIndex.Vec 1, Continuous ζ → Function.Periodic ζ 1 →
        (∀ t : ℝ, ζ t ≠ 0) → ∀ k : ℤ,
          (HasXiLoopWind P (fun t => Z t (ζ t)) k ↔ HasLoopWind (fun t => vecToC (ζ t)) k) := by
  set c : ℝ → V 1 := fun t => P.x (P.T * t) with hcdef
  have hc : ContDiff ℝ ∞ c := (ReebOrbit.contDiff_x H hH P).comp (contDiff_const.mul contDiff_id)
  have hcper : ∀ t, c (t + 1) = c t := fun t => by
    simp only [hcdef, mul_add, mul_one, P.periodic]
  have hcS : ∀ t, H (c t) = 1 := fun t => P.mem _
  have hpos : ∀ t, 0 < fderiv ℝ H (c t) (c t) := fun t => r26_pos hH (hcS t)
  have he : ContDiff ℝ ∞ (fun t => r26e H (c t)) :=
    HryniewiczCriterion.r26_cd_xiFrame hH.1 hc hpos HryniewiczCriterion.quatQ2
      (HryniewiczCriterion.r26_cd_quatQ2 hc)
  have he2 : ContDiff ℝ ∞ (fun t => HryniewiczCriterion.xiFrame2 H (c t)) :=
    HryniewiczCriterion.r26_cd_xiFrame hH.1 hc hpos HryniewiczCriterion.quatQ1
      (HryniewiczCriterion.r26_cd_quatQ1 hc)
  have hJc : ContDiff ℝ ∞ (fun t => J (c t)) := hJ.1.comp hc
  have hβ : ContDiff ℝ ∞ (fun t => r26β H J (c t)) :=
    HryniewiczCriterion.r26_cd_omega0 he (hJc.clm_apply he)
  have hs : ContDiff ℝ ∞ (fun t => Real.sqrt (r26β H J (c t))) :=
    hβ.sqrt (fun t => (r26_β_pos hH hJ (hcS t)).ne')
  have hsinv : ContDiff ℝ ∞ (fun t => (Real.sqrt (r26β H J (c t)))⁻¹) :=
    hs.inv (fun t => (r26_sqrt_pos hH hJ (hcS t)).ne')
  have hW : ContDiff ℝ ∞ (fun t => r26W H J (c t)) := hsinv.smul he
  have hJW : ContDiff ℝ ∞ (fun t => J (c t) (r26W H J (c t))) := hJc.clm_apply hW
  have hb : ContDiff ℝ ∞ (fun t => (Real.sqrt (r26β H J (c t)))⁻¹ *
      HryniewiczCriterion.omega0 (J (c t) (r26e H (c t))) (HryniewiczCriterion.xiFrame2 H (c t))) :=
    hsinv.mul (HryniewiczCriterion.r26_cd_omega0 (hJc.clm_apply he) he2)
  refine ⟨fun t => r26ZAt H J (c t), ⟨?_, ?_, fun t => ⟨r26_unitary_xi hH hJ (hcS t),
    r26_unitary_surj hH hJ (hcS t), r26_unitary_J hH hJ (hcS t),
    r26_unitary_omega hH hJ (hcS t)⟩⟩, ?_⟩
  · exact (contDiff_const.smulRight hW).add (contDiff_const.smulRight hJW)
  · intro t; simp only [hcper]
  · intro ζ hζ hζp hζ0 k
    have h1 : Continuous fun t => ζ t (Sum.inl 0) :=
      (EuclideanSpace.proj (Sum.inl 0 : Fin 1 ⊕ Fin 1)).continuous.comp hζ
    have h2 : Continuous fun t => ζ t (Sum.inr 0) :=
      (EuclideanSpace.proj (Sum.inr 0 : Fin 1 ⊕ Fin 1)).continuous.comp hζ
    have hzeq : (fun t => vecToC (ζ t)) = fun t => ((ζ t (Sum.inl 0) : ℝ) : ℂ) +
        ((ζ t (Sum.inr 0) : ℝ) : ℂ) * Complex.I :=
      funext fun t => Complex.ext (by simp [vecToC]) (by simp [vecToC])
    have hz : Continuous (fun t => vecToC (ζ t)) := by rw [hzeq]; fun_prop
    have hzp : Function.Periodic (fun t => vecToC (ζ t)) 1 := fun t => by
      simp only [hζp t]
    have hz0 : ∀ t, vecToC (ζ t) ≠ 0 := by
      intro t h
      apply hζ0 t
      have hre := congrArg Complex.re h
      have him := congrArg Complex.im h
      simp only [vecToC, Complex.zero_re, Complex.zero_im] at hre him
      ext i
      rcases i with i | i <;> fin_cases i
      · simpa using hre
      · simpa using him
    have hA := hasLoopWind_triangular_iff hsinv.continuous hb.continuous hs.continuous
      (fun t => by simp only [hcper]) (fun t => by simp only [hcper])
      (fun t => by simp only [hcper])
      (fun t => inv_pos.2 (r26_sqrt_pos hH hJ (hcS t))) (fun t => r26_sqrt_pos hH hJ (hcS t))
      hz hzp hz0 k
    have hfun : (fun t => xiCoordC H (P.x (P.T * t)) (r26ZAt H J (c t) (ζ t))) =
        fun t => (((Real.sqrt (r26β H J (c t)))⁻¹ * (vecToC (ζ t)).re +
          (Real.sqrt (r26β H J (c t)))⁻¹ *
            HryniewiczCriterion.omega0 (J (c t) (r26e H (c t)))
              (HryniewiczCriterion.xiFrame2 H (c t)) * (vecToC (ζ t)).im : ℝ) : ℂ) +
          ((Real.sqrt (r26β H J (c t)) * (vecToC (ζ t)).im : ℝ) : ℂ) * Complex.I := by
      funext t
      exact r26_coord hH hJ (hcS t) (ζ t)
    unfold HasXiLoopWind
    rw [hfun]
    exact hA

end FiniteEnergyPlane

namespace FiniteEnergyPlane

lemma c1x_xiCoordC_eq (H : V 1 → ℝ) (x v : V 1) :
    xiCoordC H x v =
      ((HryniewiczCriterion.omega0 v (HryniewiczCriterion.xiFrame2 H x) : ℝ) : ℂ) +
        ((HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame1 H x) v : ℝ) : ℂ) *
          Complex.I := by
  have hc : xiCoordC H x v =
      ⟨HryniewiczCriterion.omega0 v (HryniewiczCriterion.xiFrame2 H x),
        HryniewiczCriterion.omega0 (HryniewiczCriterion.xiFrame1 H x) v⟩ := rfl
  rw [hc]
  apply Complex.ext <;> simp

/-- `xiCoordC H x` is real-linear. -/
lemma c1x_xiCoordC_add_smul (H : V 1 → ℝ) (x v v' : V 1) (a b : ℝ) :
    xiCoordC H x (a • v + b • v') = a * xiCoordC H x v + b * xiCoordC H x v' := by
  simp only [c1x_xiCoordC_eq, HryniewiczCriterion.omega0, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  push_cast
  ring

lemma c1x_xiCoordC_zero (H : V 1 → ℝ) (x : V 1) : xiCoordC H x 0 = 0 := by
  simp [c1x_xiCoordC_eq, HryniewiczCriterion.omega0]

lemma c1x_omega0_continuous :
    Continuous (fun p : HryniewiczCriterion.R4 × HryniewiczCriterion.R4 =>
      HryniewiczCriterion.omega0 p.1 p.2) := by
  unfold HryniewiczCriterion.omega0
  fun_prop

lemma c1x_omega0_eq (u v : V 1) : omega0 u v = HryniewiczCriterion.omega0 u v := by
  simp [omega0, HryniewiczCriterion.omega0, dot, j0, Fin.sum_univ_four]; ring

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

lemma c1x_quatQ1_continuous : Continuous HryniewiczCriterion.quatQ1 := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [HryniewiczCriterion.quatQ1] <;> fun_prop

lemma c1x_quatQ2_continuous : Continuous HryniewiczCriterion.quatQ2 := by
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [HryniewiczCriterion.quatQ2] <;> fun_prop

lemma c1x_frame_continuousAt (H : V 1 → ℝ) (hH : ContDiff ℝ ∞ H)
    (Q : HryniewiczCriterion.R4 → HryniewiczCriterion.R4) (hQ : Continuous Q) {x₀ : V 1}
    (hx : 0 < fderiv ℝ H x₀ x₀) :
    ContinuousAt (fun x => (HryniewiczCriterion.euclidNorm x)⁻¹ •
      HryniewiczCriterion.xiFrameRaw H Q x) x₀ := by
  have hdc : Continuous (fderiv ℝ H) := hH.continuous_fderiv (by simp)
  have hraw : ContinuousAt (fun x => HryniewiczCriterion.xiFrameRaw H Q x) x₀ := by
    unfold HryniewiczCriterion.xiFrameRaw
    exact hQ.continuousAt.sub
      (((hdc.continuousAt.clm_apply hQ.continuousAt).div
        (hdc.continuousAt.clm_apply continuousAt_id) hx.ne').smul continuousAt_id)
  have hdot : Continuous (fun x : HryniewiczCriterion.R4 => HryniewiczCriterion.dot4 x x) := by
    unfold HryniewiczCriterion.dot4
    fun_prop
  have hn : Continuous (fun x : HryniewiczCriterion.R4 => HryniewiczCriterion.euclidNorm x) :=
    Real.continuous_sqrt.comp hdot
  have hne : HryniewiczCriterion.euclidNorm x₀ ≠ 0 := by
    intro h
    have h1 := HryniewiczCriterion.r26_euclidNorm_sq x₀
    have h2 := HryniewiczCriterion.r26_dot4_pos (HryniewiczCriterion.r26_ne_zero_of_dH_pos
      (H := H) hx)
    rw [h] at h1
    linarith
  exact (hn.continuousAt.inv₀ hne).smul hraw

/-- Let `S = H⁻¹(1)` be a strictly star-shaped level. If `X, Y : ℂ → V 1` are continuous at `z₀`
and `X(z₀) ∈ S`, then `z ↦ xiCoordC H (X z) (Y z)`, the coordinates of `Y(z)` in the global frame of
`ξ_{X(z)}`, is continuous at `z₀`. -/
theorem continuousAt_xiCoordC_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    {X Y : ℂ → V 1} {z₀ : ℂ} (hX : ContinuousAt X z₀) (hY : ContinuousAt Y z₀)
    (hX1 : H (X z₀) = 1) : ContinuousAt (fun z => xiCoordC H (X z) (Y z)) z₀ := by
  have hpos : 0 < fderiv ℝ H (X z₀) (X z₀) := hH.2.2 _ hX1
  have hZ1 : ContinuousAt (fun z => HryniewiczCriterion.xiFrame1 H (X z)) z₀ :=
    (c1x_frame_continuousAt H hH.1 _ c1x_quatQ2_continuous hpos).comp hX
  have hZ2 : ContinuousAt (fun z => HryniewiczCriterion.xiFrame2 H (X z)) z₀ :=
    (c1x_frame_continuousAt H hH.1 _ c1x_quatQ1_continuous hpos).comp hX
  simp only [c1x_xiCoordC_eq]
  have h1 : ContinuousAt (fun z => HryniewiczCriterion.omega0 (Y z)
      (HryniewiczCriterion.xiFrame2 H (X z))) z₀ :=
    c1x_omega0_continuous.continuousAt.comp (hY.prodMk hZ2)
  have h2 : ContinuousAt (fun z => HryniewiczCriterion.omega0
      (HryniewiczCriterion.xiFrame1 H (X z)) (Y z)) z₀ :=
    c1x_omega0_continuous.continuousAt.comp (hZ1.prodMk hY)
  exact (Complex.continuous_ofReal.continuousAt.comp h1).add
    ((Complex.continuous_ofReal.continuousAt.comp h2).mul continuousAt_const)

/-- For `x ∈ S = H⁻¹(1)` and `a, b ∈ ξ_x`, the global-frame coordinates `ψ_x = xiCoordC H x` satisfy
`Im(conj ψ_x(a) · ψ_x(b)) = ω₀(a, b)`. -/
theorem im_conj_xiCoordC_mul_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H) {x : V 1}
    (hx : H x = 1) {a b : V 1} (ha : IsInXi H x a) (hb : IsInXi H x b) :
    (starRingEnd ℂ (xiCoordC H x a) * xiCoordC H x b).im = omega0 a b := by
  have h12 := r26_e12 hH hx
  rw [r26_omega0_eq]
  conv_rhs => rw [r26_decomp hH hx ha, r26_decomp hH hx hb]
  rw [r26_omega0_bilin, HryniewiczCriterion.r26_omega0_self,
    HryniewiczCriterion.r26_omega0_self,
    HryniewiczCriterion.r26_omega0_antisymm (HryniewiczCriterion.xiFrame2 H x) (r26e H x), h12]
  simp only [c1x_xiCoordC_eq, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, r26e]
  ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    {X Y : ℂ → V 1} {z₀ : ℂ} (hX : ContinuousAt X z₀) (hY : ContinuousAt Y z₀)
    (hX1 : H (X z₀) = 1) : ContinuousAt (fun z => xiCoordC H (X z) (Y z)) z₀ :=
  continuousAt_xiCoordC_aux H hH hX hY hX1
