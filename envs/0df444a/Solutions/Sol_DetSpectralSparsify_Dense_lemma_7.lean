-- Prove2me | solution 1 for DetSpectralSparsify.Dense.lemma_7
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T23:44:31.867924+00:00
-- url     : https://prove2.me/submissions/b21d687f-f971-4d2c-8402-7df5c26a464b

import Definitions.Def_DetSpectralSparsify_Dense_Multigraph

set_option autoImplicit false

open Matrix

namespace DetSpectralSparsify.Dense

open scoped RealInnerProductSpace

lemma l7_contr {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (T : E →L[ℝ] E) (hT : ∀ x, 0 ≤ ⟪x, T x⟫) (x : E) {s : ℝ} (hs : 0 ≤ s) :
    ‖NormedSpace.exp (s • (-T)) x‖ ≤ ‖x‖ := by
  set X : E →L[ℝ] E := -T with hX
  let y : ℝ → E := fun s => NormedSpace.exp (s • X) x
  have hy : ∀ s, HasDerivAt y (X (y s)) s := by
    intro s
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) X s).clm_apply (hasDerivAt_const s x)
    have hc : Commute (NormedSpace.exp (s • X)) X :=
      ((Commute.refl X).smul_left s).exp_left
    have : (NormedSpace.exp (s • X) * X) x + (NormedSpace.exp (s • X)) 0 = X (y s) := by
      rw [map_zero, add_zero, hc.eq]; rfl
    rw [this] at h
    exact h
  let g : ℝ → ℝ := fun s => ⟪y s, y s⟫
  have hg : ∀ s, HasDerivAt g (⟪y s, X (y s)⟫ + ⟪X (y s), y s⟫) s := fun s =>
    (hy s).inner ℝ (hy s)
  have hanti : Antitone g := by
    apply antitone_of_deriv_nonpos
    · exact fun s => (hg s).differentiableAt
    · intro s
      rw [(hg s).deriv, real_inner_comm (X (y s)) (y s)]
      have := hT (y s)
      have e : X (y s) = -(T (y s)) := rfl
      rw [e, inner_neg_left]
      linarith [real_inner_comm (y s) (T (y s))]
  have h0 : y 0 = x := by simp [y]
  have := hanti hs
  have h2 : ‖y s‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    have e1 : g s = ‖y s‖ ^ 2 := real_inner_self_eq_norm_sq _
    have e2 : g 0 = ‖x‖ ^ 2 := by simp only [g, h0]; exact real_inner_self_eq_norm_sq _
    linarith
  nlinarith [norm_nonneg (y s), norm_nonneg x]

lemma l7_map_exp {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ)
    (hcont : Continuous (toEuclideanCLM (𝕜 := ℝ) (n := Fin r))) :
    toEuclideanCLM (𝕜 := ℝ) (NormedSpace.exp M) = NormedSpace.exp (toEuclideanCLM (𝕜 := ℝ) M) := by
  let _ : NormedRing (Matrix (Fin r) (Fin r) ℝ) := Matrix.linftyOpNormedRing
  let _ : NormedAlgebra ℝ (Matrix (Fin r) (Fin r) ℝ) := Matrix.linftyOpNormedAlgebra
  let _ : NormedAlgebra ℚ (Matrix (Fin r) (Fin r) ℝ) := NormedAlgebra.restrictScalars ℚ ℝ _
  exact NormedSpace.map_exp (𝔸 := Matrix (Fin r) (Fin r) ℝ)
    (𝔹 := EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r))
    (toEuclideanCLM (𝕜 := ℝ) (n := Fin r)).toAlgEquiv.toRingEquiv.toRingHom hcont M

lemma l7_comm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Y : E →L[ℝ] E) (s : ℝ) : Commute (NormedSpace.exp (s • Y)) Y :=
  ((Commute.refl Y).smul_left s).exp_left

lemma l7_f1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X Y : E →L[ℝ] E) :
    NormedSpace.exp ((1 : ℝ) • X) * NormedSpace.exp (((1 : ℝ) - 1) • Y) = NormedSpace.exp X := by
  simp

lemma l7_f0 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (X Y : E →L[ℝ] E) :
    NormedSpace.exp ((0 : ℝ) • X) * NormedSpace.exp (((1 : ℝ) - 0) • Y) = NormedSpace.exp Y := by
  simp

lemma l7_alg {R : Type*} [Ring R] (a b X Y : R) :
    a * X * b + -(a * (Y * b)) = a * (X - Y) * b := by noncomm_ring

lemma l7_op_le_one {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosSemidef) {s : ℝ}
    (hs : 0 ≤ s) :
    ‖NormedSpace.exp (s • (-(toEuclideanCLM (𝕜 := ℝ) A)))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  have := l7_contr (toEuclideanCLM (𝕜 := ℝ) A) (fun x => by
    rw [inner_toEuclideanCLM]
    simpa using hA.dotProduct_mulVec_nonneg x.ofLp) x hs
  simpa using this

theorem l7_aux {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    opNorm (NormedSpace.exp (-A) - NormedSpace.exp (-B)) ≤ opNorm (A - B) := by
  have hcont : Continuous (toEuclideanCLM (𝕜 := ℝ) (n := Fin r)) :=
    LinearMap.continuous_of_finiteDimensional
      ((toEuclideanCLM (𝕜 := ℝ) (n := Fin r)).toAlgEquiv.toLinearMap)
  set φ := toEuclideanCLM (𝕜 := ℝ) (n := Fin r) with hφ
  have hexp : ∀ M : Matrix (Fin r) (Fin r) ℝ,
      φ (NormedSpace.exp M) = NormedSpace.exp (φ M) := fun M => l7_map_exp M hcont
  unfold opNorm
  rw [← hφ, map_sub, map_sub, hexp, hexp, map_neg, map_neg]
  set X : _ →L[ℝ] _ := -φ A with hX
  set Y : _ →L[ℝ] _ := -φ B with hY
  have hXY : ‖X - Y‖ = ‖φ A - φ B‖ := by
    rw [← norm_neg]; congr 1; simp only [hX, hY]; abel
  let f : ℝ → _ := fun t => NormedSpace.exp (t • X) * NormedSpace.exp ((1 - t) • Y)
  have hf : ∀ t, HasDerivAt f (NormedSpace.exp (t • X) * X * NormedSpace.exp ((1 - t) • Y) +
      -(NormedSpace.exp (t • X) * (Y * NormedSpace.exp ((1 - t) • Y)))) t := by
    intro t
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
    have h2 := (hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (1 - t)).scomp t
      ((hasDerivAt_id t).const_sub 1)
    refine (h1.clm_comp h2).congr_deriv ?_
    have hc : Commute (NormedSpace.exp ((1 - t) • Y)) Y :=
      l7_comm Y (1 - t)
    simp only [Function.comp_def, id] at *
    rw [hc.eq]
    simp [mul_neg]
    rfl
  have hbound : ∀ t ∈ Set.Icc (0:ℝ) 1, ‖NormedSpace.exp (t • X) * X * NormedSpace.exp ((1 - t) • Y) +
      -(NormedSpace.exp (t • X) * (Y * NormedSpace.exp ((1 - t) • Y)))‖ ≤ ‖X - Y‖ := by
    intro t ht
    have e := l7_alg (NormedSpace.exp (t • X)) (NormedSpace.exp ((1 - t) • Y)) X Y
    rw [e]
    have a1 : ‖NormedSpace.exp (t • X)‖ ≤ 1 := l7_op_le_one A hA ht.1
    have a2 : ‖NormedSpace.exp ((1 - t) • Y)‖ ≤ 1 := l7_op_le_one B hB (by linarith [ht.2])
    calc _ ≤ ‖NormedSpace.exp (t • X)‖ * ‖X - Y‖ * ‖NormedSpace.exp ((1 - t) • Y)‖ :=
          (norm_mul_le _ _).trans (by gcongr; exact norm_mul_le _ _)
      _ ≤ 1 * ‖X - Y‖ * 1 := by gcongr
      _ = ‖X - Y‖ := by ring
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f)
    (f' := fun t => NormedSpace.exp (t • X) * X * NormedSpace.exp ((1 - t) • Y) +
      -(NormedSpace.exp (t • X) * (Y * NormedSpace.exp ((1 - t) • Y))))
    (s := Set.Icc (0:ℝ) 1) (x := 0) (y := 1) (C := ‖X - Y‖)
    (fun t _ => (hf t).hasDerivWithinAt) hbound (convex_Icc 0 1)
    (by simp) (by simp)
  have f1 : f 1 = NormedSpace.exp X := l7_f1 X Y
  have f0 : f 0 = NormedSpace.exp Y := l7_f0 X Y
  rw [f1, f0] at key
  rw [hXY] at key
  simpa using key

end DetSpectralSparsify.Dense

open DetSpectralSparsify.Dense in
theorem solution {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℝ) (hA : A.PosSemidef)
    (hB : B.PosSemidef) :
    opNorm (NormedSpace.exp (-A) - NormedSpace.exp (-B)) ≤ opNorm (A - B) :=
  l7_aux A B hA hB
