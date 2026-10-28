-- Prove2me | solution 1 for FunctionalInequalities.Analysis.exists_affine_normalization_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:32:09.717554+00:00
-- url     : https://prove2.me/submissions/d08e17ba-bf7b-4cfb-97aa-3ece777110ab

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Normalization
import Theorems.Thm_FunctionalInequalities_Analysis_abs_simplexCoord_le_one_of_max_readable
import Theorems.Thm_FunctionalInequalities_Analysis_closedBall_subset_stdSimplex_and_box_subset_closedBall_readable
import Theorems.Thm_FunctionalInequalities_Analysis_exists_max_simplexEdgeMatrix_det_readable

noncomputable section
open Set Matrix
section LT11D4AffineNormalizationAssembly
open Set Metric
set_option maxHeartbeats 4000000 in
/-- **Affine normalisation of convex bodies** (John-type, via a maximal-volume simplex; weak Letwin
route, Caffarelli's argument): there is a constant `C` depending only on the space such that every
compact convex set with nonempty interior is affinely equivalent to a set squeezed between the unit
ball and the ball of radius `C`. -/
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Set E, IsCompact K → Convex ℝ K → (interior K).Nonempty →
      ∃ e : E ≃ᵃ[ℝ] E, closedBall (0 : E) 1 ⊆ e '' K ∧ e '' K ⊆ closedBall (0 : E) C := by
  classical
  let n : ℕ := Module.finrank ℝ E
  let L : E ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    (stdOrthonormalBasis ℝ E).repr
  by_cases hn : n = 0
  · have hzero : ∀ x : E, x = 0 := by
      intro x
      apply L.injective
      apply PiLp.ext
      intro i
      exact Fin.elim0 (hn ▸ i)
    refine ⟨1, zero_lt_one, ?_⟩
    intro K _ _ hint
    obtain ⟨y, hy⟩ := hint
    refine ⟨AffineEquiv.refl ℝ E, ?_, ?_⟩
    · intro x _
      refine ⟨y, interior_subset hy, ?_⟩
      change y = x
      rw [hzero y, hzero x]
    · intro x _
      rw [hzero x]
      simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    let F := EuclideanSpace ℝ (Fin n)
    let c : F :=
      (1 / ((n : ℝ) + 1)) • ∑ i, EuclideanSpace.single i (1 : ℝ)
    let ρ : ℝ := 1 / (2 * ((n : ℝ) + 1) * Real.sqrt n)
    have hρ : 0 < ρ := by
      dsimp [ρ]
      positivity
    let C : ℝ := ρ⁻¹ * (Real.sqrt n + ‖c‖) + 1
    have hC : 0 < C := by
      dsimp [C]
      positivity
    refine ⟨C, hC, ?_⟩
    intro K hK hconv hint
    let KF : Set F := L '' K
    have hKF : IsCompact KF := hK.image L.continuous
    have hconvF : Convex ℝ KF :=
      hconv.linear_image L.toLinearMap
    have hintF : (interior KF).Nonempty := by
      change (interior (L '' K)).Nonempty
      have hInt : L '' interior K = interior (L '' K) :=
        L.toHomeomorph.image_interior K
      rw [← hInt]
      exact Set.Nonempty.image L hint
    obtain ⟨v, hv, hdet, hmax⟩ :=
      FunctionalInequalities.Analysis.exists_max_simplexEdgeMatrix_det_readable hKF hintF
    let M : Matrix (Fin n) (Fin n) ℝ := FunctionalInequalities.Analysis.simplexEdgeMatrix v
    have hM : M.det ≠ 0 := abs_pos.mp hdet
    have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
    have h₁ :
        (Matrix.toLpLin 2 2 M⁻¹).comp (Matrix.toLpLin 2 2 M) =
          LinearMap.id := by
      apply LinearMap.ext
      intro y
      apply PiLp.ext
      intro i
      change
        ((Matrix.toLpLin 2 2 M⁻¹)
          ((Matrix.toLpLin 2 2 M) y)).ofLp i = y.ofLp i
      rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp]
      change (M⁻¹.mulVec (M.mulVec y.ofLp)) i = y.ofLp i
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hunit]
      simp
    have h₂ :
        (Matrix.toLpLin 2 2 M).comp (Matrix.toLpLin 2 2 M⁻¹) =
          LinearMap.id := by
      apply LinearMap.ext
      intro y
      apply PiLp.ext
      intro i
      change
        ((Matrix.toLpLin 2 2 M)
          ((Matrix.toLpLin 2 2 M⁻¹) y)).ofLp i = y.ofLp i
      rw [Matrix.toLpLin_apply, Matrix.toLpLin_apply, WithLp.ofLp_toLp]
      change (M.mulVec (M⁻¹.mulVec y.ofLp)) i = y.ofLp i
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hunit]
      simp
    let T : F ≃ₗ[ℝ] F :=
      LinearEquiv.ofLinearMap
        (Matrix.toLpLin 2 2 M⁻¹) (Matrix.toLpLin 2 2 M) h₁ h₂
    have hTcoord (y : F) :
        (T y).ofLp = M⁻¹.mulVec y.ofLp := by
      change ((Matrix.toLpLin 2 2 M⁻¹) y).ofLp = M⁻¹.mulVec y.ofLp
      rw [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    let A : F ≃ᵃ[ℝ] F :=
      AffineEquiv.mk' (fun y : F => T (y - v 0)) T 0 (by
        intro y
        simp [sub_eq_add_neg])
    have hAcoord (y : F) :
        (A y).ofLp = M⁻¹.mulVec (y - v 0 : F).ofLp := by
      change (T (y - v 0)).ofLp = M⁻¹.mulVec (y - v 0 : F).ofLp
      exact hTcoord (y - v 0)
    let box : Set F :=
      {y | (∀ j, |y j| ≤ 1) ∧ |1 - ∑ j, y j| ≤ 1}
    let simplex : Set F :=
      {y | (∀ j, 0 ≤ y j) ∧ ∑ j, y j ≤ 1}
    have hAKbox : A '' KF ⊆ box := by
      rintro z ⟨y, hy, rfl⟩
      change
        (∀ j, |(A y).ofLp j| ≤ 1) ∧
          |1 - ∑ j, (A y).ofLp j| ≤ 1
      rw [hAcoord y]
      exact FunctionalInequalities.Analysis.abs_simplexCoord_le_one_of_max_readable hv hM hmax hy
    have hsimplexAK : simplex ⊆ A '' KF := by
      intro y hy
      change (∀ i, 0 ≤ y.ofLp i) ∧ ∑ i, y.ofLp i ≤ 1 at hy
      let w : Fin (n + 1) → ℝ :=
        Fin.cases (1 - ∑ j, y.ofLp j) y.ofLp
      let p : F := ∑ i, w i • v i
      have hw0 : ∀ i, 0 ≤ w i := by
        intro i
        refine Fin.cases ?_ ?_ i
        · exact sub_nonneg.mpr hy.2
        · intro j
          exact hy.1 j
      have hw1 : ∑ i, w i = 1 := by
        simp [w, Fin.sum_univ_succ]
      have hp : p ∈ KF := by
        apply hconvF.sum_mem
        · intro i _
          exact hw0 i
        · exact hw1
        · intro i _
          exact hv i
      have hpform :
          p = v 0 + ∑ j, y.ofLp j • (v j.succ - v 0) := by
        change (∑ i, w i • v i) =
          v 0 + ∑ j, y.ofLp j • (v j.succ - v 0)
        rw [Fin.sum_univ_succ]
        change
          (1 - ∑ j, y.ofLp j) • v 0 + ∑ j, y.ofLp j • v j.succ =
            v 0 + ∑ j, y.ofLp j • (v j.succ - v 0)
        simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul,
          sub_smul, one_smul]
        abel
      have hMp :
          M.mulVec y.ofLp = (p - v 0 : F).ofLp := by
        rw [hpform]
        ext i
        simp [M, FunctionalInequalities.Analysis.simplexEdgeMatrix, Matrix.mulVec, dotProduct, Finset.sum_apply]
        apply Finset.sum_congr rfl
        intro j _
        ring
      have hcoord :
          M⁻¹.mulVec (p - v 0 : F).ofLp = y.ofLp := by
        rw [← hMp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hunit]
        simp
      refine ⟨p, hp, ?_⟩
      apply PiLp.ext
      intro i
      exact congrFun ((hAcoord p).trans hcoord) i
    have hballs :
        closedBall c ρ ⊆ A '' KF ∧
          A '' KF ⊆ closedBall (0 : F) (Real.sqrt n) := by
      have hgeom := FunctionalInequalities.Analysis.closedBall_subset_stdSimplex_and_box_subset_closedBall_readable hnpos
      exact ⟨hgeom.1.trans hsimplexAK, hAKbox.trans hgeom.2⟩
    let V : F ≃ᵃ[ℝ] F := AffineEquiv.constVAdd ℝ F (-c)
    let H : F ≃ᵃ[ℝ] F :=
      (LinearEquiv.smulOfNeZero ℝ F ρ⁻¹ (inv_ne_zero hρ.ne')).toAffineEquiv
    let B : F ≃ᵃ[ℝ] F := (A.trans V).trans H
    have hBapply (z : F) : B z = ρ⁻¹ • (A z - c) := by
      change ρ⁻¹ • (-c + A z) = ρ⁻¹ • (A z - c)
      congr 1
      abel
    have hinner : closedBall (0 : F) 1 ⊆ B '' KF := by
      intro x hx
      have hx' : ‖x‖ ≤ 1 := by
        simpa only [mem_closedBall, dist_zero_right] using hx
      have hu : c + ρ • x ∈ closedBall c ρ := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left,
          norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hx' hρ.le
      obtain ⟨z, hz, hAz⟩ := hballs.1 hu
      refine ⟨z, hz, ?_⟩
      rw [hBapply, hAz, add_sub_cancel_left, smul_smul,
        inv_mul_cancel₀ hρ.ne', one_smul]
    have houter : B '' KF ⊆ closedBall (0 : F) C := by
      rintro x ⟨z, hz, rfl⟩
      have hAz : ‖A z‖ ≤ Real.sqrt n := by
        have hmem := hballs.2 ⟨z, hz, rfl⟩
        simpa only [mem_closedBall, dist_zero_right] using hmem
      rw [mem_closedBall, dist_zero_right, hBapply,
        norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
      calc
        ρ⁻¹ * ‖A z - c‖ ≤ ρ⁻¹ * (‖A z‖ + ‖c‖) :=
          mul_le_mul_of_nonneg_left (norm_sub_le _ _) (inv_nonneg.mpr hρ.le)
        _ ≤ ρ⁻¹ * (Real.sqrt n + ‖c‖) :=
          mul_le_mul_of_nonneg_left (add_le_add hAz (le_refl ‖c‖))
            (inv_nonneg.mpr hρ.le)
        _ ≤ C := by
          dsimp [C]
          linarith
    let e : E ≃ᵃ[ℝ] E :=
      L.toLinearEquiv.toAffineEquiv.trans
        (B.trans L.symm.toLinearEquiv.toAffineEquiv)
    have he (x : E) : e x = L.symm (B (L x)) := rfl
    refine ⟨e, ?_, ?_⟩
    · intro x hx
      have hxF : L x ∈ closedBall (0 : F) 1 := by
        simpa only [mem_closedBall, dist_zero_right, L.norm_map] using hx
      obtain ⟨z, hz, hzx⟩ := hinner hxF
      obtain ⟨k, hk, hkz⟩ := hz
      refine ⟨k, hk, ?_⟩
      rw [he, hkz, hzx, L.symm_apply_apply]
    · rintro x ⟨k, hk, rfl⟩
      have hkF : L k ∈ KF := ⟨k, hk, rfl⟩
      have hBx : B (L k) ∈ closedBall (0 : F) C :=
        houter ⟨L k, hkF, rfl⟩
      rw [he]
      simpa only [mem_closedBall, dist_zero_right, L.symm.norm_map] using hBx
