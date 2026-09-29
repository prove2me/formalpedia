-- Prove2me | solution 1 for DoCarmoDG.christoffel_system
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T06:45:58.265976+00:00
-- url     : https://prove2.me/submissions/d224cb35-16d4-4522-a3d7-283775fae5c3

import Mathlib
import Definitions.Def_DoCarmo_surface_patch
import Definitions.Def_DoCarmo_local_theory_curves

open DoCarmoDG

/-! ## coordinate helpers -/

theorem W7a_DoCarmoDG_inner3 (x y : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  rw [PiLp.inner_apply, Fin.sum_univ_three]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem W7a_DoCarmoDG_normsq3 (x : EuclideanSpace ℝ (Fin 3)) :
    ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]

theorem W7a_DoCarmoDG_cross0 (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u v 0 = u 1 * v 2 - u 2 * v 1 := by simp [cross]

theorem W7a_DoCarmoDG_cross1 (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u v 1 = u 2 * v 0 - u 0 * v 2 := by simp [cross]

theorem W7a_DoCarmoDG_cross2 (u v : EuclideanSpace ℝ (Fin 3)) :
    cross u v 2 = u 0 * v 1 - u 1 * v 0 := by simp [cross]

theorem W7a_DoCarmoDG_hasDerivAt_euc {f : ℝ → EuclideanSpace ℝ (Fin 3)}
    {f' : EuclideanSpace ℝ (Fin 3)} {t : ℝ}
    (h : ∀ i, HasDerivAt (fun s => f s i) (f' i) t) : HasDerivAt f f' t := by
  have h1 : HasDerivAt (fun s => EuclideanSpace.equiv (Fin 3) ℝ (f s))
      (EuclideanSpace.equiv (Fin 3) ℝ f') t := hasDerivAt_pi.2 (fun i => by simpa using h i)
  have h2 := (EuclideanSpace.equiv (Fin 3) ℝ).symm.hasFDerivAt.comp_hasDerivAt t h1
  have e : (⇑(EuclideanSpace.equiv (Fin 3) ℝ).symm ∘ fun s => EuclideanSpace.equiv (Fin 3) ℝ (f s))
      = f := by funext s; simp
  rw [e] at h2
  first
    | exact h2.congr_deriv (by simp)
    | (convert h2 using 1 <;> first | rfl | simp)

theorem W7a_DoCarmoDG_comp {f : ℝ → EuclideanSpace ℝ (Fin 3)}
    {f' : EuclideanSpace ℝ (Fin 3)} {t : ℝ} (h : HasDerivAt f f' t) (i : Fin 3) :
    HasDerivAt (fun s => f s i) (f' i) t :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt t h

theorem W7a_DoCarmoDG_hasDerivAt_cross {u v : ℝ → EuclideanSpace ℝ (Fin 3)}
    {u' v' : EuclideanSpace ℝ (Fin 3)} {t : ℝ} (hu : HasDerivAt u u' t)
    (hv : HasDerivAt v v' t) :
    HasDerivAt (fun s => cross (u s) (v s)) (cross u' (v t) + cross (u t) v') t := by
  have cu := W7a_DoCarmoDG_comp hu
  have cv := W7a_DoCarmoDG_comp hv
  have h0 : HasDerivAt (fun s => cross (u s) (v s) 0) ((cross u' (v t) + cross (u t) v') 0) t := by
    simp only [PiLp.add_apply, W7a_DoCarmoDG_cross0]
    refine (((cu 1).mul (cv 2)).sub ((cu 2).mul (cv 1))).congr_deriv ?_
    ring
  have h1 : HasDerivAt (fun s => cross (u s) (v s) 1) ((cross u' (v t) + cross (u t) v') 1) t := by
    simp only [PiLp.add_apply, W7a_DoCarmoDG_cross1]
    refine (((cu 2).mul (cv 0)).sub ((cu 0).mul (cv 2))).congr_deriv ?_
    ring
  have h2 : HasDerivAt (fun s => cross (u s) (v s) 2) ((cross u' (v t) + cross (u t) v') 2) t := by
    simp only [PiLp.add_apply, W7a_DoCarmoDG_cross2]
    refine (((cu 0).mul (cv 1)).sub ((cu 1).mul (cv 0))).congr_deriv ?_
    ring
  apply W7a_DoCarmoDG_hasDerivAt_euc
  intro i
  fin_cases i
  exacts [h0, h1, h2]

theorem W7a_DoCarmoDG_deriv_zero {f : ℝ → ℝ} {d c s : ℝ} (h : HasDerivAt f d s)
    (hev : f =ᶠ[nhds s] fun _ => c) : d = 0 := by
  rw [← h.deriv, hev.deriv_eq, deriv_const]

theorem W7a_DoCarmoDG_decomp (u v w : EuclideanSpace ℝ (Fin 3)) (hc : cross u v ≠ 0) :
    w = ((inner ℝ w u * inner ℝ v v - inner ℝ w v * inner ℝ u v) /
          (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2)) • u +
        ((inner ℝ w v * inner ℝ u u - inner ℝ w u * inner ℝ u v) /
          (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2)) • v +
        inner ℝ (‖cross u v‖⁻¹ • cross u v) w • (‖cross u v‖⁻¹ • cross u v) := by
  have hcn : ‖cross u v‖ ≠ 0 := norm_ne_zero_iff.2 hc
  have hW : ‖cross u v‖ ^ 2 = inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 := by
    rw [W7a_DoCarmoDG_normsq3, W7a_DoCarmoDG_cross0, W7a_DoCarmoDG_cross1,
      W7a_DoCarmoDG_cross2, W7a_DoCarmoDG_inner3, W7a_DoCarmoDG_inner3, W7a_DoCarmoDG_inner3]
    ring
  have hN : inner ℝ (‖cross u v‖⁻¹ • cross u v) w • (‖cross u v‖⁻¹ • cross u v) =
      (inner ℝ (cross u v) w / ‖cross u v‖ ^ 2) • cross u v := by
    rw [real_inner_smul_left, smul_smul]
    congr 1
    field_simp
  rw [hN, hW]
  have hW0 : inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2 ≠ 0 := by
    rw [← hW]; exact pow_ne_zero 2 hcn
  have key : (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2) • w =
      (inner ℝ w u * inner ℝ v v - inner ℝ w v * inner ℝ u v) • u +
      (inner ℝ w v * inner ℝ u u - inner ℝ w u * inner ℝ u v) • v +
      inner ℝ (cross u v) w • cross u v := by
    simp only [W7a_DoCarmoDG_inner3]
    ext i
    fin_cases i <;> simp [W7a_DoCarmoDG_cross0, W7a_DoCarmoDG_cross1, W7a_DoCarmoDG_cross2] <;>
      ring
  calc w = (inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2)⁻¹ •
        ((inner ℝ u u * inner ℝ v v - inner ℝ u v ^ 2) • w) := by
          rw [smul_smul, inv_mul_cancel₀ hW0, one_smul]
    _ = _ := by
          rw [key, smul_add, smul_add, smul_smul, smul_smul, smul_smul, div_eq_inv_mul,
            div_eq_inv_mul, div_eq_inv_mul]

theorem W7a_DoCarmoDG_triple_swap (T n w : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (cross T n) w = -inner ℝ (cross T w) n := by
  simp only [W7a_DoCarmoDG_inner3, W7a_DoCarmoDG_cross0, W7a_DoCarmoDG_cross1,
    W7a_DoCarmoDG_cross2]
  ring

theorem W7a_DoCarmoDG_cross_smul_self (k : ℝ) (n : EuclideanSpace ℝ (Fin 3)) :
    cross (k • n) n = 0 := by
  ext i; fin_cases i <;> simp [cross] <;> ring

theorem W7a_DoCarmoDG_cross_expand (T n : EuclideanSpace ℝ (Fin 3)) (c d : ℝ)
    (hTT : inner ℝ T T = 1) (hTn : inner ℝ T n = 0) :
    cross T (c • T - d • cross T n) = d • n := by
  rw [W7a_DoCarmoDG_inner3] at hTT hTn
  ext i; fin_cases i <;> simp [cross]
  · linear_combination (-d * T 0) * hTn + (d * n 0) * hTT
  · linear_combination (-d * T 1) * hTn + (d * n 1) * hTT
  · linear_combination (-d * T 2) * hTn + (d * n 2) * hTT

/-! ## curves -/

theorem W7a_DoCarmoDG_orth (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha) :
    ∀ s ∈ Set.Ioo a b, inner ℝ (deriv alpha s) (deriv (deriv alpha) s) = 0 := by
  obtain ⟨hsm, hunit⟩ := halpha
  have hd1 : ContDiffOn ℝ 1 (deriv alpha) (Set.Ioo a b) :=
    hsm.deriv_of_isOpen isOpen_Ioo
    (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp)
  intro s hs
  have h1 := ((hd1.differentiableOn (by simp) s hs).differentiableAt
    (isOpen_Ioo.mem_nhds hs)).hasDerivAt
  have h2 := HasDerivAt.inner ℝ h1 h1
  have hev : (fun t => inner ℝ (deriv alpha t) (deriv alpha t)) =ᶠ[nhds s] fun _ => (1:ℝ) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    rw [real_inner_self_eq_norm_sq, hunit t ht, one_pow]
  have h3 := h2.deriv
  rw [hev.deriv_eq, deriv_const, real_inner_comm (deriv alpha s)] at h3
  linarith

theorem W7a_DoCarmoDG_trihedron (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) :
    ∀ s ∈ Set.Ioo a b,
      ‖tangent alpha s‖ = 1 ∧ ‖normal alpha s‖ = 1 ∧ ‖binormal alpha s‖ = 1 ∧
      inner ℝ (tangent alpha s) (normal alpha s) = 0 := by
  intro s hs
  have horth := W7a_DoCarmoDG_orth a b alpha halpha s hs
  have ht : ‖tangent alpha s‖ = 1 := halpha.2 s hs
  have hks := hk s hs
  have hkpos : 0 < curvature alpha s := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hks)
  have hn : ‖normal alpha s‖ = 1 := by
    unfold normal
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hkpos.le]
    unfold curvature at hks ⊢
    exact inv_mul_cancel₀ hks
  have htn : inner ℝ (tangent alpha s) (normal alpha s) = 0 := by
    unfold normal tangent
    rw [real_inner_smul_right, horth, mul_zero]
  set T := tangent alpha s with hT
  set N := normal alpha s with hN
  have hb : binormal alpha s = cross T N := rfl
  have ht2 : T 0 ^ 2 + T 1 ^ 2 + T 2 ^ 2 = 1 := by rw [← W7a_DoCarmoDG_normsq3, ht]; norm_num
  have hn2 : N 0 ^ 2 + N 1 ^ 2 + N 2 ^ 2 = 1 := by rw [← W7a_DoCarmoDG_normsq3, hn]; norm_num
  have htn' : T 0 * N 0 + T 1 * N 1 + T 2 * N 2 = 0 := by rw [← W7a_DoCarmoDG_inner3]; exact htn
  have hb2 : ‖binormal alpha s‖ ^ 2 = 1 := by
    rw [hb, W7a_DoCarmoDG_normsq3, W7a_DoCarmoDG_cross0, W7a_DoCarmoDG_cross1,
      W7a_DoCarmoDG_cross2]
    have : (T 1 * N 2 - T 2 * N 1) ^ 2 + (T 2 * N 0 - T 0 * N 2) ^ 2 +
        (T 0 * N 1 - T 1 * N 0) ^ 2 =
        (T 0 ^ 2 + T 1 ^ 2 + T 2 ^ 2) * (N 0 ^ 2 + N 1 ^ 2 + N 2 ^ 2) -
          (T 0 * N 0 + T 1 * N 1 + T 2 * N 2) ^ 2 := by ring
    rw [this, ht2, hn2, htn']
    norm_num
  refine ⟨ht, hn, ?_, htn⟩
  have := norm_nonneg (binormal alpha s)
  nlinarith

/-- Smoothness of the first derivatives of an arc-length curve. -/
theorem W7a_DoCarmoDG_derivs (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha) :
    ∀ s ∈ Set.Ioo a b,
      HasDerivAt alpha (deriv alpha s) s ∧
      HasDerivAt (deriv alpha) (deriv (deriv alpha) s) s ∧
      HasDerivAt (deriv (deriv alpha)) (deriv (deriv (deriv alpha)) s) s := by
  obtain ⟨hsm, -⟩ := halpha
  have hT2 : ContDiffOn ℝ 2 (deriv alpha) (Set.Ioo a b) :=
    hsm.deriv_of_isOpen isOpen_Ioo
    (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (le_top : (3 : ℕ∞) ≤ ⊤) | simp)
  have hA1 : ContDiffOn ℝ 1 (deriv (deriv alpha)) (Set.Ioo a b) :=
    hT2.deriv_of_isOpen isOpen_Ioo (by first | norm_num | rfl | simp)
  intro s hs
  refine ⟨?_, ?_, ?_⟩
  · exact ((hsm.differentiableOn (by simp) s hs).differentiableAt
      (isOpen_Ioo.mem_nhds hs)).hasDerivAt
  · exact ((hT2.differentiableOn two_ne_zero s hs).differentiableAt
      (isOpen_Ioo.mem_nhds hs)).hasDerivAt
  · exact ((hA1.differentiableOn one_ne_zero s hs).differentiableAt
      (isOpen_Ioo.mem_nhds hs)).hasDerivAt

theorem W7a_DoCarmoDG_frame (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) (s : ℝ) (hs : s ∈ Set.Ioo a b) :
    ∃ N' : EuclideanSpace ℝ (Fin 3), HasDerivAt (normal alpha) N' s ∧
      N' = -(curvature alpha s) • tangent alpha s - torsion alpha s • binormal alpha s ∧
      HasDerivAt (binormal alpha) (torsion alpha s • normal alpha s) s ∧
      HasDerivAt (tangent alpha) (curvature alpha s • normal alpha s) s ∧
      deriv (deriv (deriv alpha)) s =
        curvature alpha s • N' + deriv (curvature alpha) s • normal alpha s := by
  have hD := W7a_DoCarmoDG_derivs a b alpha halpha
  obtain ⟨-, hTd, hAd⟩ := hD s hs
  have hks := hk s hs
  have hA0 : deriv (deriv alpha) s ≠ 0 := by
    intro h; apply hks; simp [curvature, h]
  have hkdiff : DifferentiableAt ℝ (curvature alpha) s := hAd.differentiableAt.norm ℝ hA0
  have hkd := hkdiff.hasDerivAt
  obtain ⟨N', hnD⟩ : ∃ N', HasDerivAt (normal alpha) N' s :=
    ⟨_, (hkd.inv hks).smul hAd⟩
  have hAeq : ∀ y ∈ Set.Ioo a b,
      deriv (deriv alpha) y = curvature alpha y • normal alpha y := by
    intro y hy
    exact (smul_inv_smul₀ (hk y hy) _).symm
  have hA3 : deriv (deriv (deriv alpha)) s =
      curvature alpha s • N' + deriv (curvature alpha) s • normal alpha s := by
    have h1 := hkd.smul hnD
    have h2 : HasDerivAt (deriv (deriv alpha))
        (curvature alpha s • N' + deriv (curvature alpha) s • normal alpha s) s := by
      apply h1.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds hs] with y hy using hAeq y hy
    exact hAd.unique h2
  have htri := W7a_DoCarmoDG_trihedron a b alpha halpha hk
  obtain ⟨hT1, hn1, hb1, hTn⟩ := htri s hs
  -- ⟨N', n⟩ = 0
  have hNn : inner ℝ N' (normal alpha s) = 0 := by
    have h := HasDerivAt.inner ℝ hnD hnD
    have := W7a_DoCarmoDG_deriv_zero h (c := 1) (by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with y hy
      rw [real_inner_self_eq_norm_sq, (htri y hy).2.1, one_pow])
    have h2 := real_inner_comm N' (normal alpha s)
    linarith
  -- ⟨T, N'⟩ = -k
  have hTN : inner ℝ (tangent alpha s) N' = -curvature alpha s := by
    have h := HasDerivAt.inner ℝ (show HasDerivAt (tangent alpha) _ s from hTd) hnD
    have := W7a_DoCarmoDG_deriv_zero h (c := 0) (by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with y hy
      exact (htri y hy).2.2.2)
    have hAn : inner ℝ (deriv (deriv alpha) s) (normal alpha s) = curvature alpha s := by
      rw [hAeq s hs, real_inner_smul_left, real_inner_self_eq_norm_sq, hn1]; ring
    rw [hAn] at this
    linarith
  -- binormal derivative
  have hbD0 := W7a_DoCarmoDG_hasDerivAt_cross (show HasDerivAt (tangent alpha) _ s from hTd) hnD
  rw [hAeq s hs, W7a_DoCarmoDG_cross_smul_self, zero_add] at hbD0
  have hbD : HasDerivAt (binormal alpha) (cross (tangent alpha s) N') s := hbD0
  have htau : torsion alpha s = inner ℝ (cross (tangent alpha s) N') (normal alpha s) := by
    unfold torsion; rw [hbD.deriv]
  have hc : cross (tangent alpha s) (normal alpha s) ≠ 0 := by
    intro h
    have : ‖binormal alpha s‖ = 0 := by
      show ‖cross (tangent alpha s) (normal alpha s)‖ = 0
      rw [h, norm_zero]
    rw [hb1] at this; exact one_ne_zero this
  have hcn : ‖cross (tangent alpha s) (normal alpha s)‖ = 1 := hb1
  have hdec := W7a_DoCarmoDG_decomp (tangent alpha s) (normal alpha s) N' hc
  have hTT : inner ℝ (tangent alpha s) (tangent alpha s) = 1 := by
    rw [real_inner_self_eq_norm_sq, hT1, one_pow]
  have hnn : inner ℝ (normal alpha s) (normal alpha s) = 1 := by
    rw [real_inner_self_eq_norm_sq, hn1, one_pow]
  have hNT : inner ℝ N' (tangent alpha s) = -curvature alpha s := by
    rw [real_inner_comm]; exact hTN
  have hbN : inner ℝ (cross (tangent alpha s) (normal alpha s)) N' = -torsion alpha s := by
    rw [W7a_DoCarmoDG_triple_swap, htau]
  rw [hcn, inv_one, one_smul, hbN, hTT, hnn, hTn, hNT, hNn] at hdec
  have hN'eq : N' = -(curvature alpha s) • tangent alpha s -
      torsion alpha s • binormal alpha s := by
    rw [hdec]
    show _ = _ - torsion alpha s • cross (tangent alpha s) (normal alpha s)
    simp [sub_eq_add_neg, neg_smul]
  refine ⟨N', hnD, hN'eq, ?_, ?_, hA3⟩
  · have := hbD
    rw [hN'eq] at this
    rwa [show binormal alpha s = cross (tangent alpha s) (normal alpha s) from rfl,
      W7a_DoCarmoDG_cross_expand _ _ _ _ hTT hTn] at this
  · rw [← hAeq s hs]; exact hTd

theorem W7a_DoCarmoDG_frenet_formulas
    (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) :
    ∀ s ∈ Set.Ioo a b,
      HasDerivAt (tangent alpha) (curvature alpha s • normal alpha s) s ∧
      HasDerivAt (normal alpha)
        (-(curvature alpha s) • tangent alpha s - torsion alpha s • binormal alpha s) s ∧
      HasDerivAt (binormal alpha) (torsion alpha s • normal alpha s) s := by
  intro s hs
  obtain ⟨N', hn, hN', hb, ht, -⟩ := W7a_DoCarmoDG_frame a b alpha halpha hk s hs
  exact ⟨ht, hN' ▸ hn, hb⟩

theorem W7a_DoCarmoDG_torsion_formula
    (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) :
    ∀ s ∈ Set.Ioo a b,
      torsion alpha s =
        -(inner ℝ (cross (deriv alpha s) (deriv (deriv alpha) s))
            (deriv (deriv (deriv alpha)) s)) / (curvature alpha s) ^ 2 := by
  intro s hs
  obtain ⟨N', -, hN', -, -, hA3⟩ := W7a_DoCarmoDG_frame a b alpha halpha hk s hs
  obtain ⟨hT1, hn1, hb1, hTn⟩ := W7a_DoCarmoDG_trihedron a b alpha halpha hk s hs
  have hks := hk s hs
  have hA : deriv (deriv alpha) s = curvature alpha s • normal alpha s :=
    (smul_inv_smul₀ hks _).symm
  have hbn : inner ℝ (binormal alpha s) (normal alpha s) = 0 := by
    show inner ℝ (cross (tangent alpha s) (normal alpha s)) (normal alpha s) = 0
    simp only [W7a_DoCarmoDG_inner3, W7a_DoCarmoDG_cross0, W7a_DoCarmoDG_cross1,
      W7a_DoCarmoDG_cross2]
    ring
  have hbb : inner ℝ (binormal alpha s) (binormal alpha s) = 1 := by
    rw [real_inner_self_eq_norm_sq, hb1, one_pow]
  have hbt : inner ℝ (binormal alpha s) (tangent alpha s) = 0 := by
    show inner ℝ (cross (tangent alpha s) (normal alpha s)) (tangent alpha s) = 0
    simp only [W7a_DoCarmoDG_inner3, W7a_DoCarmoDG_cross0, W7a_DoCarmoDG_cross1,
      W7a_DoCarmoDG_cross2]
    ring
  have hcross : cross (deriv alpha s) (deriv (deriv alpha) s) =
      curvature alpha s • binormal alpha s := by
    rw [hA]
    show _ = curvature alpha s • cross (tangent alpha s) (normal alpha s)
    ext i; fin_cases i <;> simp [cross, tangent] <;> ring
  rw [hcross, hA3, hN']
  simp only [inner_add_right, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hbn, hbb, hbt]
  field_simp
  ring

theorem W7a_DoCarmoDG_triple_zero (u v w N : EuclideanSpace ℝ (Fin 3)) (hN : N ≠ 0)
    (hu : inner ℝ u N = 0) (hv : inner ℝ v N = 0) (hw : inner ℝ w N = 0) :
    inner ℝ (cross u v) w = 0 := by
  rw [W7a_DoCarmoDG_inner3] at hu hv hw
  simp only [W7a_DoCarmoDG_inner3, W7a_DoCarmoDG_cross0, W7a_DoCarmoDG_cross1,
    W7a_DoCarmoDG_cross2]
  set D := (u 1 * v 2 - u 2 * v 1) * w 0 + (u 2 * v 0 - u 0 * v 2) * w 1 +
    (u 0 * v 1 - u 1 * v 0) * w 2 with hD
  have h0 : D * N 0 = 0 := by
    rw [hD]
    linear_combination (v 1 * w 2 - v 2 * w 1) * hu + (w 1 * u 2 - w 2 * u 1) * hv +
      (u 1 * v 2 - u 2 * v 1) * hw
  have h1 : D * N 1 = 0 := by
    rw [hD]
    linear_combination (v 2 * w 0 - v 0 * w 2) * hu + (w 2 * u 0 - w 0 * u 2) * hv +
      (u 2 * v 0 - u 0 * v 2) * hw
  have h2 : D * N 2 = 0 := by
    rw [hD]
    linear_combination (v 0 * w 1 - v 1 * w 0) * hu + (w 0 * u 1 - w 1 * u 0) * hv +
      (u 0 * v 1 - u 1 * v 0) * hw
  by_contra hD0
  apply hN
  ext i
  fin_cases i
  · exact (mul_eq_zero.1 h0).resolve_left hD0
  · exact (mul_eq_zero.1 h1).resolve_left hD0
  · exact (mul_eq_zero.1 h2).resolve_left hD0

theorem W7a_DoCarmoDG_torsion_eq_zero_iff_plane_curve
    (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) :
    (∀ s ∈ Set.Ioo a b, torsion alpha s = 0) ↔
      ∃ p N : EuclideanSpace ℝ (Fin 3), N ≠ 0 ∧
        ∀ s ∈ Set.Ioo a b, inner ℝ (alpha s - p) N = 0 := by
  have hD := W7a_DoCarmoDG_derivs a b alpha halpha
  constructor
  · intro hτ
    by_cases hab : a < b
    · have hs0 : (a + b) / 2 ∈ Set.Ioo a b := ⟨by linarith, by linarith⟩
      have hbD : ∀ y ∈ Set.Ioo a b, HasDerivAt (binormal alpha) 0 y := by
        intro y hy
        obtain ⟨-, -, -, hb, -⟩ := W7a_DoCarmoDG_frame a b alpha halpha hk y hy
        rwa [hτ y hy, zero_smul] at hb
      have hbc : ∀ y ∈ Set.Ioo a b, binormal alpha y = binormal alpha ((a + b) / 2) :=
        fun y hy => isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
          (fun x hx => (hbD x hx).differentiableAt.differentiableWithinAt)
          (fun x hx => (hbD x hx).deriv) hy hs0
      refine ⟨alpha ((a + b) / 2), binormal alpha ((a + b) / 2), ?_, ?_⟩
      · intro h
        have := (W7a_DoCarmoDG_trihedron a b alpha halpha hk _ hs0).2.2.1
        rw [h, norm_zero] at this
        exact zero_ne_one this
      · have hfD : ∀ y ∈ Set.Ioo a b, HasDerivAt
            (fun z => inner ℝ (alpha z - alpha ((a + b) / 2)) (binormal alpha ((a + b) / 2)))
            0 y := by
          intro y hy
          have h := HasDerivAt.inner ℝ (((hD y hy).1).sub_const (alpha ((a + b) / 2)))
            (hasDerivAt_const y (binormal alpha ((a + b) / 2)))
          have hbt : inner ℝ (deriv alpha y) (binormal alpha y) = 0 := by
            show inner ℝ (deriv alpha y) (cross (tangent alpha y) (normal alpha y)) = 0
            simp only [tangent, W7a_DoCarmoDG_inner3, W7a_DoCarmoDG_cross0,
              W7a_DoCarmoDG_cross1, W7a_DoCarmoDG_cross2]
            ring
          rw [hbc y hy] at hbt
          rw [inner_zero_right, hbt, zero_add] at h
          exact h
        intro s hs
        have := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
          (fun x hx => (hfD x hx).differentiableAt.differentiableWithinAt)
          (fun x hx => (hfD x hx).deriv) hs hs0
        rw [this, sub_self, inner_zero_left]
    · refine ⟨0, EuclideanSpace.single 0 1, ?_, fun s hs => absurd (hs.1.trans hs.2) hab⟩
      intro h
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
      simp at this
  · rintro ⟨p, N, hN, hpl⟩ s hs
    have hT : ∀ y ∈ Set.Ioo a b, inner ℝ (deriv alpha y) N = 0 := by
      intro y hy
      have h := HasDerivAt.inner ℝ (((hD y hy).1).sub_const p) (hasDerivAt_const y N)
      have := W7a_DoCarmoDG_deriv_zero h (c := 0) (by
        filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz using hpl z hz)
      rwa [inner_zero_right, zero_add] at this
    have hA : ∀ y ∈ Set.Ioo a b, inner ℝ (deriv (deriv alpha) y) N = 0 := by
      intro y hy
      have h := HasDerivAt.inner ℝ ((hD y hy).2.1) (hasDerivAt_const y N)
      have := W7a_DoCarmoDG_deriv_zero h (c := 0) (by
        filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz using hT z hz)
      rwa [inner_zero_right, zero_add] at this
    have hA' : inner ℝ (deriv (deriv (deriv alpha)) s) N = 0 := by
      have h := HasDerivAt.inner ℝ ((hD s hs).2.2) (hasDerivAt_const s N)
      have := W7a_DoCarmoDG_deriv_zero h (c := 0) (by
        filter_upwards [isOpen_Ioo.mem_nhds hs] with z hz using hA z hz)
      rwa [inner_zero_right, zero_add] at this
    rw [W7a_DoCarmoDG_torsion_formula a b alpha halpha hk s hs,
      W7a_DoCarmoDG_triple_zero _ _ _ N hN (hT s hs) (hA s hs) hA']
    simp

theorem W7a_DoCarmoDG_triple_lin (R : Matrix (Fin 3) (Fin 3) ℝ)
    (u v w u' v' w' : EuclideanSpace ℝ (Fin 3))
    (hu : ∀ i, u' i = R i 0 * u 0 + R i 1 * u 1 + R i 2 * u 2)
    (hv : ∀ i, v' i = R i 0 * v 0 + R i 1 * v 1 + R i 2 * v 2)
    (hw : ∀ i, w' i = R i 0 * w 0 + R i 1 * w 1 + R i 2 * w 2) :
    inner ℝ (cross u' v') w' = R.det * inner ℝ (cross u v) w := by
  simp only [W7a_DoCarmoDG_inner3, W7a_DoCarmoDG_cross0, W7a_DoCarmoDG_cross1,
    W7a_DoCarmoDG_cross2, hu, hv, hw, Matrix.det_fin_three]
  ring

theorem W7a_DoCarmoDG_rigid_motion_invariance
    (a b : ℝ) (alpha : ℝ → EuclideanSpace ℝ (Fin 3))
    (M : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hM : IsRigidMotion M)
    (halpha : IsArcLengthCurve (Set.Ioo a b) alpha)
    (hk : ∀ s ∈ Set.Ioo a b, curvature alpha s ≠ 0) :
    IsArcLengthCurve (Set.Ioo a b) (M ∘ alpha) ∧
      ∀ s ∈ Set.Ioo a b,
        curvature (M ∘ alpha) s = curvature alpha s ∧
        torsion (M ∘ alpha) s = torsion alpha s := by
  obtain ⟨ρ, c, hdet, hMx⟩ := hM
  have hMf : M ∘ alpha = fun y => ρ (alpha y) + c := funext fun y => hMx _
  let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ρ.toContinuousLinearEquiv.toContinuousLinearMap
  have hL : ∀ z, L z = ρ z := fun z => rfl
  have hlin : ∀ (f : ℝ → EuclideanSpace ℝ (Fin 3)) (y : ℝ), DifferentiableAt ℝ f y →
      HasDerivAt (fun z => ρ (f z)) (ρ (deriv f y)) y := by
    intro f y hf
    exact L.hasFDerivAt.comp_hasDerivAt y hf.hasDerivAt
  have hD := W7a_DoCarmoDG_derivs a b alpha halpha
  have D1 : ∀ y ∈ Set.Ioo a b, deriv (M ∘ alpha) y = ρ (deriv alpha y) := by
    intro y hy
    rw [hMf]
    exact ((hlin alpha y (hD y hy).1.differentiableAt).add_const c).deriv
  have D2 : ∀ y ∈ Set.Ioo a b, deriv (deriv (M ∘ alpha)) y = ρ (deriv (deriv alpha) y) := by
    intro y hy
    have hev : deriv (M ∘ alpha) =ᶠ[nhds y] fun z => ρ (deriv alpha z) := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz using D1 z hz
    rw [hev.deriv_eq]
    exact (hlin (deriv alpha) y (hD y hy).2.1.differentiableAt).deriv
  have D3 : ∀ y ∈ Set.Ioo a b,
      deriv (deriv (deriv (M ∘ alpha))) y = ρ (deriv (deriv (deriv alpha)) y) := by
    intro y hy
    have hev : deriv (deriv (M ∘ alpha)) =ᶠ[nhds y] fun z => ρ (deriv (deriv alpha) z) := by
      filter_upwards [isOpen_Ioo.mem_nhds hy] with z hz using D2 z hz
    rw [hev.deriv_eq]
    exact (hlin (deriv (deriv alpha)) y (hD y hy).2.2.differentiableAt).deriv
  have hMarc : IsArcLengthCurve (Set.Ioo a b) (M ∘ alpha) := by
    refine ⟨?_, fun s hs => ?_⟩
    · rw [hMf]
      exact (L.contDiff.comp_contDiffOn halpha.1).add contDiffOn_const
    · rw [D1 s hs, LinearIsometryEquiv.norm_map]
      exact halpha.2 s hs
  have hcurv : ∀ s ∈ Set.Ioo a b, curvature (M ∘ alpha) s = curvature alpha s := by
    intro s hs
    unfold curvature
    rw [D2 s hs, LinearIsometryEquiv.norm_map]
  have hkM : ∀ s ∈ Set.Ioo a b, curvature (M ∘ alpha) s ≠ 0 := fun s hs => by
    rw [hcurv s hs]; exact hk s hs
  -- matrix of ρ
  let B := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  let R := LinearMap.toMatrix B B (ρ.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _)
  have hR : ∀ u : EuclideanSpace ℝ (Fin 3), ∀ i,
      ρ u i = R i 0 * u 0 + R i 1 * u 1 + R i 2 * u 2 := by
    intro u i
    have := congrFun (LinearMap.toMatrix_mulVec_repr B B
      (ρ.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _) u) i
    simpa [B, R, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using this.symm
  have hRdet : R.det = 1 := by
    have h1 : R.det = LinearMap.det (ρ.toLinearEquiv : EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] _) :=
      LinearMap.det_toMatrix B _
    have hU := ρ.toMatrix_mem_unitaryGroup (EuclideanSpace.basisFun (Fin 3) ℝ)
      (EuclideanSpace.basisFun (Fin 3) ℝ)
    have h2 := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary hU)
    have h3 : R.det * R.det = 1 := by simpa [R, B] using h2
    rw [h1] at h3 ⊢
    nlinarith
  refine ⟨hMarc, fun s hs => ⟨hcurv s hs, ?_⟩⟩
  rw [W7a_DoCarmoDG_torsion_formula a b _ hMarc hkM s hs,
    W7a_DoCarmoDG_torsion_formula a b alpha halpha hk s hs, hcurv s hs, D1 s hs, D2 s hs,
    D3 s hs, W7a_DoCarmoDG_triple_lin R _ _ _ _ _ _ (hR _) (hR _) (hR _), hRdet, one_mul]

theorem solution
    (U : Set (ℝ × ℝ)) (hU : IsOpen U) (x : ℝ → ℝ → EuclideanSpace ℝ (Fin 3))
    (hx : IsRegularPatch U x)
    (G111 G211 G112 G212 G122 G222 : ℝ → ℝ → ℝ)
    (hG : IsChristoffel U x G111 G211 G112 G212 G122 G222) :
    ∀ p ∈ U,
      G111 p.1 p.2 * coeffE x p.1 p.2 + G211 p.1 p.2 * coeffF x p.1 p.2 =
          (1 / 2) * deriv (fun t => coeffE x t p.2) p.1 ∧
      G111 p.1 p.2 * coeffF x p.1 p.2 + G211 p.1 p.2 * coeffG x p.1 p.2 =
          deriv (fun t => coeffF x t p.2) p.1 - (1 / 2) * deriv (fun t => coeffE x p.1 t) p.2 ∧
      G112 p.1 p.2 * coeffE x p.1 p.2 + G212 p.1 p.2 * coeffF x p.1 p.2 =
          (1 / 2) * deriv (fun t => coeffE x p.1 t) p.2 ∧
      G112 p.1 p.2 * coeffF x p.1 p.2 + G212 p.1 p.2 * coeffG x p.1 p.2 =
          (1 / 2) * deriv (fun t => coeffG x t p.2) p.1 ∧
      G122 p.1 p.2 * coeffE x p.1 p.2 + G222 p.1 p.2 * coeffF x p.1 p.2 =
          deriv (fun t => coeffF x p.1 t) p.2 - (1 / 2) * deriv (fun t => coeffG x t p.2) p.1 ∧
      G122 p.1 p.2 * coeffF x p.1 p.2 + G222 p.1 p.2 * coeffG x p.1 p.2 =
          (1 / 2) * deriv (fun t => coeffG x p.1 t) p.2 := by
  intro p hp
  obtain ⟨hsm, hreg⟩ := hx
  set f := Function.uncurry x with hfdef
  have hdiff : ∀ q ∈ U, DifferentiableAt ℝ f q := fun q hq =>
    (hsm.contDiffAt (hU.mem_nhds hq)).differentiableAt (by simp)
  have hf1 : ContDiffOn ℝ 1 (fderiv ℝ f) U := hsm.fderiv_of_isOpen hU
    (by first | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | simp)
  have hdd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    (hf1.contDiffAt (hU.mem_nhds hp)).differentiableAt one_ne_zero
  set H := fderiv ℝ (fderiv ℝ f) p with hH
  have hsymm : H ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) = H ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)) :=
    (hsm.contDiffAt (hU.mem_nhds hp)).isSymmSndFDerivAt
      (by simp; first | exact WithTop.coe_le_coe.2 le_top | exact (WithTop.coe_le_coe (a := (2:ℕ∞)) (b := ⊤)).2 le_top | exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤) | norm_num | decide) _ _
  have hpp : ((p.1, p.2) : ℝ × ℝ) ∈ U := by simpa using hp
  have hU1 : ∀ᶠ t in nhds p.1, ((t, p.2) : ℝ × ℝ) ∈ U := by
    have hc : ContinuousAt (fun t : ℝ => ((t, p.2) : ℝ × ℝ)) p.1 := by fun_prop
    exact hc.preimage_mem_nhds (hU.mem_nhds hpp)
  have hU2 : ∀ᶠ t in nhds p.2, ((p.1, t) : ℝ × ℝ) ∈ U := by
    have hc : ContinuousAt (fun t : ℝ => ((p.1, t) : ℝ × ℝ)) p.2 := by fun_prop
    exact hc.preimage_mem_nhds (hU.mem_nhds hpp)
  have hPU : ∀ q ∈ U, HasDerivAt (fun t => x t q.2) (fderiv ℝ f q ((1 : ℝ), (0 : ℝ))) q.1 := by
    intro q hq
    have hl : HasDerivAt (fun t : ℝ => ((t, q.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) q.1 :=
      (hasDerivAt_id q.1).prodMk (hasDerivAt_const q.1 q.2)
    exact (hdiff q hq).hasFDerivAt.comp_hasDerivAt q.1 hl
  have hPV : ∀ q ∈ U, HasDerivAt (fun t => x q.1 t) (fderiv ℝ f q ((0 : ℝ), (1 : ℝ))) q.2 := by
    intro q hq
    have hl : HasDerivAt (fun t : ℝ => ((q.1, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) q.2 :=
      (hasDerivAt_const q.2 q.1).prodMk (hasDerivAt_id q.2)
    exact (hdiff q hq).hasFDerivAt.comp_hasDerivAt q.2 hl
  have lineU : ∀ w : ℝ × ℝ, HasDerivAt (fun t => fderiv ℝ f (t, p.2) w)
      (H ((1 : ℝ), (0 : ℝ)) w) p.1 := by
    intro w
    have hl : HasDerivAt (fun t : ℝ => ((t, p.2) : ℝ × ℝ)) ((1 : ℝ), (0 : ℝ)) p.1 :=
      (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
    have h1 := hdd.hasFDerivAt.comp_hasDerivAt p.1 hl
    have h2 := h1.clm_apply (hasDerivAt_const p.1 w)
    simpa using h2
  have lineV : ∀ w : ℝ × ℝ, HasDerivAt (fun t => fderiv ℝ f (p.1, t) w)
      (H ((0 : ℝ), (1 : ℝ)) w) p.2 := by
    intro w
    have hl : HasDerivAt (fun t : ℝ => ((p.1, t) : ℝ × ℝ)) ((0 : ℝ), (1 : ℝ)) p.2 :=
      (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
    have h1 := hdd.hasFDerivAt.comp_hasDerivAt p.2 hl
    have h2 := h1.clm_apply (hasDerivAt_const p.2 w)
    simpa using h2
  have hxuU : HasDerivAt (fun t => partialU x t p.2) (H ((1 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)))
      p.1 := by
    apply (lineU _).congr_of_eventuallyEq
    filter_upwards [hU1] with t ht
    exact (hPU (t, p.2) ht).deriv
  have hxuV : HasDerivAt (fun t => partialU x p.1 t) (H ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)))
      p.2 := by
    apply (lineV _).congr_of_eventuallyEq
    filter_upwards [hU2] with t ht
    exact (hPU (p.1, t) ht).deriv
  have hxvU : HasDerivAt (fun t => partialV x t p.2) (H ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ)))
      p.1 := by
    apply (lineU _).congr_of_eventuallyEq
    filter_upwards [hU1] with t ht
    exact (hPV (t, p.2) ht).deriv
  have hxvV : HasDerivAt (fun t => partialV x p.1 t) (H ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ)))
      p.2 := by
    apply (lineV _).congr_of_eventuallyEq
    filter_upwards [hU2] with t ht
    exact (hPV (p.1, t) ht).deriv
  have e11 : partialU (partialU x) p.1 p.2 = H ((1 : ℝ), (0 : ℝ)) ((1 : ℝ), (0 : ℝ)) := hxuU.deriv
  have e12 : partialV (partialU x) p.1 p.2 = H ((0 : ℝ), (1 : ℝ)) ((1 : ℝ), (0 : ℝ)) := hxuV.deriv
  have e22 : partialV (partialV x) p.1 p.2 = H ((0 : ℝ), (1 : ℝ)) ((0 : ℝ), (1 : ℝ)) := hxvV.deriv
  have dEu : deriv (fun t => coeffE x t p.2) p.1 = _ := (hxuU.inner ℝ hxuU).deriv
  have dEv : deriv (fun t => coeffE x p.1 t) p.2 = _ := (hxuV.inner ℝ hxuV).deriv
  have dFu : deriv (fun t => coeffF x t p.2) p.1 = _ := (hxuU.inner ℝ hxvU).deriv
  have dFv : deriv (fun t => coeffF x p.1 t) p.2 = _ := (hxuV.inner ℝ hxvV).deriv
  have dGu : deriv (fun t => coeffG x t p.2) p.1 = _ := (hxvU.inner ℝ hxvU).deriv
  have dGv : deriv (fun t => coeffG x p.1 t) p.2 = _ := (hxvV.inner ℝ hxvV).deriv
  obtain ⟨c1, c2, c3⟩ := hG p hp
  rw [e11] at c1
  rw [e12] at c2
  rw [e22] at c3
  have hNu : inner ℝ (unitNormal x p.1 p.2) (partialU x p.1 p.2) = 0 := by
    unfold unitNormal
    rw [real_inner_smul_left]
    simp only [W7a_DoCarmoDG_inner3, W7a_DoCarmoDG_cross0, W7a_DoCarmoDG_cross1,
      W7a_DoCarmoDG_cross2]
    ring
  have hNv : inner ℝ (unitNormal x p.1 p.2) (partialV x p.1 p.2) = 0 := by
    unfold unitNormal
    rw [real_inner_smul_left]
    simp only [W7a_DoCarmoDG_inner3, W7a_DoCarmoDG_cross0, W7a_DoCarmoDG_cross1,
      W7a_DoCarmoDG_cross2]
    ring
  have i1 := congrArg (fun w => inner ℝ w (partialU x p.1 p.2)) c1
  have i2 := congrArg (fun w => inner ℝ w (partialV x p.1 p.2)) c1
  have i3 := congrArg (fun w => inner ℝ w (partialU x p.1 p.2)) c2
  have i4 := congrArg (fun w => inner ℝ w (partialV x p.1 p.2)) c2
  have i5 := congrArg (fun w => inner ℝ w (partialU x p.1 p.2)) c3
  have i6 := congrArg (fun w => inner ℝ w (partialV x p.1 p.2)) c3
  simp only [inner_add_left, real_inner_smul_left, hNu, hNv, mul_zero, add_zero] at i1 i2 i3 i4 i5 i6
  rw [dEu, dEv, dFu, dFv, dGu, dGv]
  simp only [hsymm] at i3 i4 i5 i6 ⊢
  unfold coeffE coeffF coeffG
  simp only [W7a_DoCarmoDG_inner3] at i1 i2 i3 i4 i5 i6 ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · linear_combination -i1
  · linear_combination -i2
  · linear_combination -i3
  · linear_combination -i4
  · linear_combination -i5
  · linear_combination -i6
