-- Prove2me | solution 1 for FiniteEnergyPlane.exists_uniform_loop_gap
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-29T00:49:28.984255+00:00
-- url     : https://prove2.me/submissions/b20fedfc-e937-4ca9-82aa-7040cc4768be

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_integral_norm_sq_le_of_skew

open scoped RealInnerProductSpace
open MeasureTheory Set CauchyRiemannIndex

/-! Pairwise estimates for approximate eigenvectors of the asymptotic loop operator. -/

set_option linter.all false


namespace HCAG

variable {n : ℕ}

abbrev Op (n : ℕ) := Vec n →L[ℝ] Vec n

/-- matrices as operators -/
noncomputable def TL (n : ℕ) : Mat n ≃L[ℝ] (Op n) :=
  (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin n ⊕ Fin n)).toAlgEquiv.toLinearEquiv.toContinuousLinearEquiv

lemma TL_apply (M : Mat n) (v : Vec n) : TL n M v = Matrix.toEuclideanLin M v := rfl

noncomputable abbrev Jop (n : ℕ) : Op n := TL n (J₀ n)

lemma inner_TL_left (M : Mat n) (v w : Vec n) :
    ⟪TL n M v, w⟫ = ⟪v, TL n (Matrix.transpose M) w⟫ := by
  have h := Matrix.toEuclideanLin_conjTranspose_eq_adjoint M
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  rw [TL_apply, TL_apply, h, LinearMap.adjoint_inner_right]

lemma inner_Jop_left (v w : Vec n) : ⟪Jop n v, w⟫ = -⟪v, Jop n w⟫ := by
  rw [Jop, inner_TL_left, Matrix.J_transpose, map_neg, ContinuousLinearMap.neg_apply,
    inner_neg_right]

lemma inner_self_Jop (v : Vec n) : ⟪v, Jop n v⟫ = 0 := by
  have h := inner_Jop_left v v
  rw [real_inner_comm] at h
  linarith

lemma Jop_Jop (v : Vec n) : Jop n (Jop n v) = -v := by
  show (Matrix.toEuclideanCLM (𝕜 := ℝ) (J₀ n)) ((Matrix.toEuclideanCLM (𝕜 := ℝ) (J₀ n)) v) = -v
  rw [← ContinuousLinearMap.mul_apply, ← map_mul, show J₀ n * J₀ n = -1 from Matrix.J_squared _ _,
    map_neg, map_one]
  rfl

lemma norm_Jop (v : Vec n) : ‖Jop n v‖ = ‖v‖ := by
  have h : ‖Jop n v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_Jop_left, Jop_Jop,
      inner_neg_right, neg_neg]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

lemma inner_symm {M : Mat n} (hM : M.IsSymm) (v w : Vec n) : ⟪TL n M v, w⟫ = ⟪v, TL n M w⟫ := by
  rw [inner_TL_left, hM.eq]

/-- the residual `-J₀ u' - S u - λ u` -/
noncomputable def rsd (M : Mat n) (l : ℝ) (u u' : Vec n) : Vec n := -(Jop n u') - TL n M u - l • u

lemma rsd_eq (M : Mat n) (l : ℝ) (u u' : Vec n) :
    rsd M l u u' = -(Matrix.toEuclideanLin (J₀ n) u') - Matrix.toEuclideanLin M u - l • u := rfl

/-- pointwise: the symmetric part cancels in `⟨r₁, v⟩ - ⟨u, r₂⟩` -/
lemma pair_identity {M : Mat n} (hM : M.IsSymm) (l₁ l₂ : ℝ) (u u' v v' : Vec n) :
    ⟪rsd M l₁ u u', v⟫ - ⟪u, rsd M l₂ v v'⟫ =
      -(⟪Jop n u', v⟫ + ⟪Jop n u, v'⟫) + (l₂ - l₁) * ⟪u, v⟫ := by
  simp only [rsd, inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
    real_inner_smul_left, real_inner_smul_right, inner_symm hM]
  rw [inner_Jop_left u v']
  ring

/-- `u' - a J₀ u = J₀ (r + S u + (λ - a) u)`, hence its size is controlled by the residual. -/
lemma norm_twist_le (M : Mat n) (K : ℝ) (hK : ‖TL n M‖ ≤ K) (l a : ℝ) (u u' : Vec n) :
    ‖u' - Jop n (a • u)‖ ≤ ‖rsd M l u u'‖ + (K + |l - a|) * ‖u‖ := by
  have e : u' - Jop n (a • u) = Jop n (rsd M l u u' + TL n M u + (l - a) • u) := by
    simp only [rsd, map_add, map_sub, map_neg, map_smul, Jop_Jop, neg_neg]
    module
  rw [e, norm_Jop]
  have h1 := norm_add_le (rsd M l u u' + TL n M u) ((l - a) • u)
  have h2 := norm_add_le (rsd M l u u') (TL n M u)
  rw [norm_smul, Real.norm_eq_abs] at h1
  have := (TL n M).le_opNorm u
  have := mul_le_mul_of_nonneg_right hK (norm_nonneg u)
  nlinarith [norm_nonneg u, abs_nonneg (l - a)]

/-- `|⟨r, v⟩| ≤ d` after integration, from `∫ |r|² ≤ d²` and `∫ |v|² = 1` -/
lemma abs_integral_inner_le (r v : ℝ → Vec n) (hr : Continuous r) (hv : Continuous v) (d : ℝ)
    (hd : 0 < d) (hr2 : ∫ t in (0:ℝ)..1, ‖r t‖ ^ 2 ≤ d ^ 2) (hv2 : ∫ t in (0:ℝ)..1, ‖v t‖ ^ 2 = 1) :
    |∫ t in (0:ℝ)..1, ⟪r t, v t⟫| ≤ d := by
  have hpt : ∀ t, |⟪r t, v t⟫| ≤ ‖r t‖ ^ 2 / (2 * d) + d / 2 * ‖v t‖ ^ 2 := by
    intro t
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (‖r t‖ - d * ‖v t‖)]
  refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
  have h := intervalIntegral.integral_mono_on (f := fun t => |⟪r t, v t⟫|)
    (g := fun t => ‖r t‖ ^ 2 / (2 * d) + d / 2 * ‖v t‖ ^ 2) (μ := volume) zero_le_one
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun t _ => hpt t
  refine h.trans ?_
  rw [intervalIntegral.integral_add (f := fun t => ‖r t‖ ^ 2 / (2 * d))
    (g := fun t => d / 2 * ‖v t‖ ^ 2) (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_div,
    intervalIntegral.integral_const_mul, hv2]
  have : (∫ t in (0:ℝ)..1, ‖r t‖ ^ 2) / (2 * d) ≤ d ^ 2 / (2 * d) :=
    div_le_div_of_nonneg_right hr2 (by positivity)
  have e : d ^ 2 / (2 * d) = d / 2 := by field_simp
  linarith

/-- Approximate eigenvectors at well-separated levels are almost orthogonal. -/
lemma gram_bound (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) (u u' v v' : ℝ → Vec n)
    (hu : ∀ t, HasDerivAt u (u' t) t) (hu' : Continuous u') (hpu : Function.Periodic u 1)
    (hv : ∀ t, HasDerivAt v (v' t) t) (hv' : Continuous v') (hpv : Function.Periodic v 1)
    (l₁ l₂ d : ℝ) (hd : 0 < d) (hu1 : ∫ t in (0:ℝ)..1, ‖u t‖ ^ 2 = 1)
    (hv1 : ∫ t in (0:ℝ)..1, ‖v t‖ ^ 2 = 1)
    (hru : ∫ t in (0:ℝ)..1, ‖rsd (Sinf t) l₁ (u t) (u' t)‖ ^ 2 ≤ d ^ 2)
    (hrv : ∫ t in (0:ℝ)..1, ‖rsd (Sinf t) l₂ (v t) (v' t)‖ ^ 2 ≤ d ^ 2) :
    |l₂ - l₁| * |∫ t in (0:ℝ)..1, ⟪u t, v t⟫| ≤ 2 * d := by
  have huc : Continuous u := continuous_iff_continuousAt.2 fun t => (hu t).continuousAt
  have hvc : Continuous v := continuous_iff_continuousAt.2 fun t => (hv t).continuousAt
  have cS : Continuous fun t => TL n (Sinf t) := (TL n).continuous.comp hSinf.1
  have cru : Continuous fun t => rsd (Sinf t) l₁ (u t) (u' t) :=
    ((Jop n).continuous.comp hu').neg.sub (cS.clm_apply huc) |>.sub (huc.const_smul l₁)
  have crv : Continuous fun t => rsd (Sinf t) l₂ (v t) (v' t) :=
    ((Jop n).continuous.comp hv').neg.sub (cS.clm_apply hvc) |>.sub (hvc.const_smul l₂)
  have h1 := abs_integral_inner_le _ _ cru hvc d hd hru hv1
  have h2 := abs_integral_inner_le _ _ crv huc d hd hrv hu1
  -- the `J₀` boundary term integrates to zero
  have hφ : ∀ t, HasDerivAt (fun t => ⟪Jop n (u t), v t⟫)
      (⟪Jop n (u t), v' t⟫ + ⟪Jop n (u' t), v t⟫) t := fun t =>
    ((Jop n).hasFDerivAt.comp_hasDerivAt t (hu t)).inner ℝ (hv t)
  have hP : ∫ t in (0:ℝ)..1, (⟪Jop n (u t), v' t⟫ + ⟪Jop n (u' t), v t⟫) = 0 := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hφ t)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    have e1 := hpu 0; have e2 := hpv 0
    simp only [zero_add] at e1 e2
    rw [e1, e2, sub_self]
  have hid : ∀ t, ⟪rsd (Sinf t) l₁ (u t) (u' t), v t⟫ - ⟪u t, rsd (Sinf t) l₂ (v t) (v' t)⟫ =
      (-1) * (⟪Jop n (u t), v' t⟫ + ⟪Jop n (u' t), v t⟫) + (l₂ - l₁) * ⟪u t, v t⟫ := by
    intro t
    rw [pair_identity (hSinf.2.2 t)]
    ring
  have hI : (∫ t in (0:ℝ)..1, ⟪rsd (Sinf t) l₁ (u t) (u' t), v t⟫) -
      (∫ t in (0:ℝ)..1, ⟪u t, rsd (Sinf t) l₂ (v t) (v' t)⟫) =
      (l₂ - l₁) * ∫ t in (0:ℝ)..1, ⟪u t, v t⟫ := by
    rw [← intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp only [hid]
    rw [intervalIntegral.integral_add (f := fun t => (-1) * (⟪Jop n (u t), v' t⟫ + ⟪Jop n (u' t), v t⟫))
      (g := fun t => (l₂ - l₁) * ⟪u t, v t⟫) (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, hP]
    ring
  rw [← abs_mul, ← hI]
  have e : (∫ t in (0:ℝ)..1, ⟪u t, rsd (Sinf t) l₂ (v t) (v' t)⟫) =
      ∫ t in (0:ℝ)..1, ⟪rsd (Sinf t) l₂ (v t) (v' t), u t⟫ := by
    congr 1; funext t; exact real_inner_comm _ _
  rw [e]
  refine (abs_sub _ _).trans ?_
  linarith

end HCAG

/-! Too many almost-orthonormal approximate eigenvectors in a short window are impossible. -/

set_option linter.all false


namespace HCAG

variable {n : ℕ}

lemma gram_lower {N : ℕ} (G : Fin N → Fin N → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hG : ∀ i j, |G i j - if i = j then 1 else 0| ≤ η) (x : Fin N → ℝ) :
    (1 - η * N) * ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, x i * x j * G i j := by
  have hdiag : ∀ i, ∑ j, x i * x j * (if i = j then (1:ℝ) else 0) = x i ^ 2 := by
    intro i
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have hsplit : ∑ i, ∑ j, x i * x j * G i j = ∑ i, x i ^ 2 +
      ∑ i, ∑ j, x i * x j * (G i j - if i = j then 1 else 0) := by
    simp only [mul_sub, Finset.sum_sub_distrib, hdiag]
    ring
  have hbd : |∑ i, ∑ j, x i * x j * (G i j - if i = j then 1 else 0)| ≤
      η * (∑ i, |x i|) ^ 2 := by
    calc _ ≤ ∑ i, ∑ j, |x i * x j * (G i j - if i = j then 1 else 0)| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ i, ∑ j, η * (|x i| * |x j|) :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [abs_mul, abs_mul]
            have := mul_le_mul_of_nonneg_left (hG i j)
              (mul_nonneg (abs_nonneg (x i)) (abs_nonneg (x j)))
            linarith
      _ = η * (∑ i, |x i|) ^ 2 := by
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
  have hcs : (∑ i, |x i|) ^ 2 ≤ N * ∑ i, x i ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => |x i|)
    simpa [sq_abs] using this
  have := neg_abs_le (∑ i, ∑ j, x i * x j * (G i j - if i = j then 1 else 0))
  have := mul_le_mul_of_nonneg_left hcs hη
  nlinarith

lemma norm_sum_smul_sq_le {N : ℕ} (x : Fin N → ℝ) (g : Fin N → Vec n) :
    ‖∑ j, x j • g j‖ ^ 2 ≤ (∑ j, x j ^ 2) * ∑ j, ‖g j‖ ^ 2 := by
  have h1 : ‖∑ j, x j • g j‖ ≤ ∑ j, |x j| * ‖g j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp [norm_smul, Real.norm_eq_abs]))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => |x j|) (fun j => ‖g j‖)
  calc _ ≤ (∑ j, |x j| * ‖g j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by simpa [sq_abs] using h2

lemma norm_sum_smul_sq_eq {N : ℕ} (x : Fin N → ℝ) (v : Fin N → Vec n) :
    ‖∑ j, x j • v j‖ ^ 2 = ∑ i, ∑ j, x i * x j * ⟪v i, v j⟫ := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

/-- Poincaré inequality on `[0, 1]` for a curve vanishing at the points `k / m`. -/
lemma poincare_grid (w w' : ℝ → Vec n) (hw : ∀ t, HasDerivAt w (w' t) t) (hw' : Continuous w')
    (a : ℝ) (m : ℕ) (hm : 0 < m) (hz : ∀ k < m, w ((k : ℝ) / m) = 0) :
    ∫ t in (0:ℝ)..1, ‖w t‖ ^ 2 ≤ 4 / (m : ℝ) ^ 2 * ∫ t in (0:ℝ)..1, ‖w' t - Jop n (a • w t)‖ ^ 2 := by
  have hwc : Continuous w := continuous_iff_continuousAt.2 fun t => (hw t).continuousAt
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hT : ∀ v, ⟪v, (a • Jop n) v⟫ = 0 := by
    intro v
    rw [ContinuousLinearMap.smul_apply, real_inner_smul_right, inner_self_Jop, mul_zero]
  have hc1 : Continuous fun t => ‖w t‖ ^ 2 := hwc.norm.pow 2
  have hc2 : Continuous fun t => ‖w' t - Jop n (a • w t)‖ ^ 2 :=
    (hw'.sub ((Jop n).continuous.comp (hwc.const_smul a))).norm.pow 2
  have hk : ∀ k < m, ∫ t in ((k : ℕ) : ℝ) / m..((k + 1 : ℕ) : ℝ) / m, ‖w t‖ ^ 2 ≤
      4 / (m : ℝ) ^ 2 * ∫ t in ((k : ℕ) : ℝ) / m..((k + 1 : ℕ) : ℝ) / m,
        ‖w' t - Jop n (a • w t)‖ ^ 2 := by
    intro k hk
    have e : ((k + 1 : ℕ) : ℝ) / m = (k : ℝ) / m + 1 / m := by push_cast; ring
    rw [e]
    have := FiniteEnergyPlane.integral_norm_sq_le_of_skew (a • Jop n) hT w w' hw hw' ((k : ℝ) / m)
      (1 / m) (by positivity) (hz k hk)
    have e2 : ∀ t, w' t - (a • Jop n) (w t) = w' t - Jop n (a • w t) := fun t => by
      rw [ContinuousLinearMap.smul_apply, map_smul]
    simp only [e2] at this
    have e3 : 4 * (1 / (m : ℝ)) ^ 2 = 4 / (m : ℝ) ^ 2 := by field_simp
    rwa [e3] at this
  have hsum := fun (f : ℝ → ℝ) (hf : Continuous f) =>
    intervalIntegral.sum_integral_adjacent_intervals (f := f) (μ := volume)
      (a := fun k : ℕ => (k : ℝ) / m) (n := m) fun k _ => hf.intervalIntegrable _ _
  have h0 : ((0 : ℕ) : ℝ) / m = 0 := by simp
  have h1 : ((m : ℕ) : ℝ) / m = 1 := div_self hm'.ne'
  have s1 := hsum _ hc1
  have s2 := hsum _ hc2
  simp only [h0, h1] at s1 s2
  rw [← s1, ← s2, Finset.mul_sum]
  exact Finset.sum_le_sum fun k hkr => hk k (Finset.mem_range.1 hkr)

end HCAG

/-! Counting approximate eigenvectors in a window. -/

set_option linter.all false


namespace HCAG

variable {n : ℕ}

lemma int_twist_le (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) (K : ℝ)
    (hK : ∀ t, ‖TL n (Sinf t)‖ ≤ K) (hK0 : 0 ≤ K) (u u' : ℝ → Vec n)
    (hu : ∀ t, HasDerivAt u (u' t) t) (hu' : Continuous u') (l a δ d : ℝ) (hla : |l - a| ≤ δ)
    (hd0 : 0 ≤ d) (hd1 : d ≤ 1) (h1 : ∫ t in (0:ℝ)..1, ‖u t‖ ^ 2 = 1)
    (hr : ∫ t in (0:ℝ)..1, ‖rsd (Sinf t) l (u t) (u' t)‖ ^ 2 ≤ d ^ 2) :
    ∫ t in (0:ℝ)..1, ‖u' t - Jop n (a • u t)‖ ^ 2 ≤ 2 + 2 * (K + δ) ^ 2 := by
  have huc : Continuous u := continuous_iff_continuousAt.2 fun t => (hu t).continuousAt
  have cS : Continuous fun t => TL n (Sinf t) := (TL n).continuous.comp hSinf.1
  have cr : Continuous fun t => rsd (Sinf t) l (u t) (u' t) :=
    ((Jop n).continuous.comp hu').neg.sub (cS.clm_apply huc) |>.sub (huc.const_smul l)
  have cg : Continuous fun t => u' t - Jop n (a • u t) :=
    hu'.sub ((Jop n).continuous.comp (huc.const_smul a))
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hla
  have hpt : ∀ t, ‖u' t - Jop n (a • u t)‖ ^ 2 ≤
      2 * ‖rsd (Sinf t) l (u t) (u' t)‖ ^ 2 + 2 * (K + δ) ^ 2 * ‖u t‖ ^ 2 := by
    intro t
    have h := norm_twist_le (Sinf t) K (hK t) l a (u t) (u' t)
    have h2 : (K + |l - a|) * ‖u t‖ ≤ (K + δ) * ‖u t‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have h' := h.trans (by linarith : ‖rsd (Sinf t) l (u t) (u' t)‖ + (K + |l - a|) * ‖u t‖ ≤
      ‖rsd (Sinf t) l (u t) (u' t)‖ + (K + δ) * ‖u t‖)
    have := pow_le_pow_left₀ (norm_nonneg _) h' 2
    nlinarith [sq_nonneg (‖rsd (Sinf t) l (u t) (u' t)‖ - (K + δ) * ‖u t‖)]
  have hint := intervalIntegral.integral_mono_on (μ := volume)
    (f := fun t => ‖u' t - Jop n (a • u t)‖ ^ 2)
    (g := fun t => 2 * ‖rsd (Sinf t) l (u t) (u' t)‖ ^ 2 + 2 * (K + δ) ^ 2 * ‖u t‖ ^ 2) zero_le_one
    ((cg.norm.pow 2).intervalIntegrable _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun t _ => hpt t
  rw [intervalIntegral.integral_add (f := fun t => 2 * ‖rsd (Sinf t) l (u t) (u' t)‖ ^ 2)
    (g := fun t => 2 * (K + δ) ^ 2 * ‖u t‖ ^ 2) (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, h1] at hint
  have : d ^ 2 ≤ 1 := by nlinarith
  nlinarith

/-- More than `2n m` almost-orthonormal approximate eigenvectors at separated levels in a window
of length `δ` are impossible for suitable `m`. -/
theorem core (Sinf : ℝ → Mat n) (hSinf : IsSymLoop Sinf) (K δ a d : ℝ)
    (hK : ∀ t, ‖TL n (Sinf t)‖ ≤ K) (hK0 : 0 ≤ K) (hδ : 0 < δ) (hd : 0 < d) (hd1 : d ≤ 1)
    (m N : ℕ) (hm : 0 < m) (hNm : 2 * n * m < N) (hdN : 4 * d * (N : ℝ) ^ 2 ≤ δ)
    (hmN : 8 * (N : ℝ) * (2 + 2 * (K + δ) ^ 2) < (m : ℝ) ^ 2)
    (lam : Fin N → ℝ) (hlam : ∀ j, lam j ∈ Icc a (a + δ))
    (hsep : ∀ i j, i ≠ j → δ / N ≤ |lam i - lam j|)
    (u u' : Fin N → ℝ → Vec n) (hu : ∀ j t, HasDerivAt (u j) (u' j t) t)
    (hu' : ∀ j, Continuous (u' j)) (hp : ∀ j, Function.Periodic (u j) 1)
    (h1 : ∀ j, ∫ t in (0:ℝ)..1, ‖u j t‖ ^ 2 = 1)
    (hr : ∀ j, ∫ t in (0:ℝ)..1, ‖rsd (Sinf t) (lam j) (u j t) (u' j t)‖ ^ 2 ≤ d ^ 2) : False := by
  classical
  have huc : ∀ j, Continuous (u j) := fun j =>
    continuous_iff_continuousAt.2 fun t => (hu j t).continuousAt
  have hN0 : 0 < N := by omega
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN0
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  -- almost orthonormality
  set G : Fin N → Fin N → ℝ := fun i j => ∫ t in (0:ℝ)..1, ⟪u i t, u j t⟫ with hGdef
  set η := 2 * d * N / δ with hηdef
  have hη : 0 ≤ η := by positivity
  have hG : ∀ i j, |G i j - if i = j then 1 else 0| ≤ η := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [G, if_true, real_inner_self_eq_norm_sq, h1, sub_self, abs_zero]
      exact hη
    · simp only [hij, if_false, sub_zero]
      have hb := gram_bound Sinf hSinf (u i) (u' i) (u j) (u' j) (hu i) (hu' i) (hp i) (hu j)
        (hu' j) (hp j) (lam i) (lam j) d hd (h1 i) (h1 j) (hr i) (hr j)
      have hs := hsep j i (Ne.symm hij)
      have hδN : 0 < δ / N := by positivity
      have h3 : δ / N * |G i j| ≤ 2 * d :=
        le_trans (mul_le_mul_of_nonneg_right hs (abs_nonneg _)) hb
      have e : η = 2 * d / (δ / N) := by rw [hηdef]; field_simp
      rw [e, le_div_iff₀ hδN]
      linarith
  -- a nonzero combination vanishing on the grid `k / m`
  let Φ : (Fin N → ℝ) →ₗ[ℝ] (Fin m → Vec n) :=
    { toFun := fun x k => ∑ j, x j • u j (((k : ℕ) : ℝ) / m)
      map_add' := fun x y => by
        funext k; simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        funext k; simp [Finset.smul_sum, smul_smul] }
  have hdim : Module.finrank ℝ (Fin m → Vec n) < Module.finrank ℝ (Fin N → ℝ) := by
    rw [Module.finrank_pi_fintype, Module.finrank_fin_fun]
    simp only [finrank_euclideanSpace, Fintype.card_sum, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul]
    nlinarith
  obtain ⟨x, hxk, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := Φ) hdim)
  rw [LinearMap.mem_ker] at hxk
  set w : ℝ → Vec n := fun t => ∑ j, x j • u j t
  set w' : ℝ → Vec n := fun t => ∑ j, x j • u' j t
  have hw : ∀ t, HasDerivAt w (w' t) t := fun t =>
    HasDerivAt.fun_sum fun j _ => (hu j t).const_smul (x j)
  have hw' : Continuous w' := continuous_finset_sum _ fun j _ => (hu' j).const_smul (x j)
  have hz : ∀ k < m, w ((k : ℝ) / m) = 0 := fun k hk => by
    have := congrFun hxk ⟨k, hk⟩
    simpa [Φ, w] using this
  -- upper bound by the grid Poincaré inequality
  have hP := poincare_grid w w' hw hw' a m hm hz
  set X := ∑ j, x j ^ 2
  set B := 2 + 2 * (K + δ) ^ 2
  have htw : ∀ t, w' t - Jop n (a • w t) = ∑ j, x j • (u' j t - Jop n (a • u j t)) := by
    intro t
    simp only [w, w', Finset.smul_sum, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_comm]
  have cg : ∀ j, Continuous fun t => u' j t - Jop n (a • u j t) := fun j =>
    (hu' j).sub ((Jop n).continuous.comp ((huc j).const_smul a))
  have hup : ∫ t in (0:ℝ)..1, ‖w' t - Jop n (a • w t)‖ ^ 2 ≤ X * (N * B) := by
    have hpt : ∀ t, ‖w' t - Jop n (a • w t)‖ ^ 2 ≤
        X * ∑ j, ‖u' j t - Jop n (a • u j t)‖ ^ 2 := fun t => by
      rw [htw]; exact norm_sum_smul_sq_le x _
    have hc : Continuous fun t => ‖w' t - Jop n (a • w t)‖ ^ 2 :=
      (hw'.sub ((Jop n).continuous.comp ((continuous_finset_sum _ fun j _ =>
        (huc j).const_smul (x j)).const_smul a))).norm.pow 2
    have hcs : Continuous fun t => ∑ j, ‖u' j t - Jop n (a • u j t)‖ ^ 2 :=
      continuous_finset_sum _ fun j _ => (cg j).norm.pow 2
    have hint := intervalIntegral.integral_mono_on (μ := volume) zero_le_one
      (hc.intervalIntegrable 0 1) ((hcs.intervalIntegrable 0 1).const_mul X) fun t _ => hpt t
    simp only [intervalIntegral.integral_const_mul] at hint
    have e2 := intervalIntegral.integral_finsetSum (μ := volume) (a := 0) (b := 1)
      (s := Finset.univ) (f := fun j t => ‖u' j t - Jop n (a • u j t)‖ ^ 2)
      fun j _ => ((cg j).norm.pow 2).intervalIntegrable _ _
    rw [e2] at hint
    have hsum : ∑ j, ∫ t in (0:ℝ)..1, ‖u' j t - Jop n (a • u j t)‖ ^ 2 ≤ N * B := by
      have := Finset.sum_le_sum (s := Finset.univ) fun j _ =>
        int_twist_le Sinf hSinf K hK hK0 (u j) (u' j) (hu j) (hu' j) (lam j) a δ d
          (by rw [abs_le]; constructor <;> linarith [(hlam j).1, (hlam j).2]) hd.le hd1 (h1 j) (hr j)
      refine this.trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hX0 : 0 ≤ X := Finset.sum_nonneg fun j _ => sq_nonneg _
    exact hint.trans (mul_le_mul_of_nonneg_left hsum hX0)
  -- lower bound by almost orthonormality
  have hlow : (1 - η * N) * X ≤ ∫ t in (0:ℝ)..1, ‖w t‖ ^ 2 := by
    refine (gram_lower G η hη hG x).trans (le_of_eq ?_)
    have e : ∀ t, ‖w t‖ ^ 2 = ∑ i, ∑ j, x i * x j * ⟪u i t, u j t⟫ := fun t =>
      norm_sum_smul_sq_eq x (fun j => u j t)
    simp only [e]
    rw [intervalIntegral.integral_finsetSum fun i _ => Continuous.intervalIntegrable
      (continuous_finset_sum _ fun j _ => by fun_prop) _ _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j _ => Continuous.intervalIntegrable
      (by fun_prop) _ _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
  have hηN : η * N ≤ 1 / 2 := by
    rw [hηdef, div_mul_eq_mul_div, div_le_iff₀ hδ]
    nlinarith
  have hXpos : 0 < X := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hx0
    have := Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
    have hj' : x j ≠ 0 := by simpa using hj
    have : 0 < x j ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hj'))
    linarith
  -- combine
  have hcomb : X / 2 ≤ 4 / (m : ℝ) ^ 2 * (X * (N * B)) := by
    have h1' : X / 2 ≤ (1 - η * N) * X := by nlinarith
    exact h1'.trans (hlow.trans (hP.trans (mul_le_mul_of_nonneg_left hup (by positivity))))
  have : X * (m : ℝ) ^ 2 ≤ X * (8 * N * B) := by
    have hm2 : (0:ℝ) < (m : ℝ) ^ 2 := by positivity
    have e : 4 / (m : ℝ) ^ 2 * (X * (N * B)) * (m : ℝ) ^ 2 = 4 * (X * (N * B)) := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_right hcomb hm2.le
    rw [e] at h2
    nlinarith
  have := le_of_mul_le_mul_left this hXpos
  linarith

end HCAG

/-! Uniform spectral gaps of the asymptotic loop operator. -/

set_option linter.all false


namespace FiniteEnergyPlane

open HCAG

theorem exists_uniform_loop_gap_aux {n : ℕ} (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c > 0, ∀ a : ℝ, ∃ l ∈ Set.Icc a (a + δ), ∀ u u' : ℝ → CauchyRiemannIndex.Vec n,
      (∀ t, HasDerivAt u (u' t) t) → Continuous u' → Function.Periodic u 1 →
      c * ∫ t in (0:ℝ)..1, ‖u t‖ ^ 2 ≤ ∫ t in (0:ℝ)..1,
        ‖-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (u' t)) -
          Matrix.toEuclideanLin (Sinf t) (u t) - l • u t‖ ^ 2 := by
  classical
  -- a bound for `S∞`
  obtain ⟨K0, hK0⟩ : ∃ K0, ∀ t, ‖TL n (Sinf t)‖ ≤ K0 := by
    have hc : Continuous fun t => TL n (Sinf t) := (TL n).continuous.comp hSinf.1
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (0:ℝ) 1) hc.continuousOn
    refine ⟨M, fun t => ?_⟩
    obtain ⟨y, hy, hyt⟩ := hSinf.2.1.exists_mem_Ico₀ zero_lt_one t
    rw [hyt]
    exact hM y (Ico_subset_Icc_self hy)
  set K := max K0 0
  have hK : ∀ t, ‖TL n (Sinf t)‖ ≤ K := fun t => (hK0 t).trans (le_max_left _ _)
  have hK0' : 0 ≤ K := le_max_right _ _
  set B : ℝ := 2 + 2 * (K + δ) ^ 2
  have hB : 0 < B := by positivity
  set m : ℕ := ⌈8 * (2 * n + 1) * B⌉₊ + 1
  set N : ℕ := 2 * n * m + 1
  have hm : 0 < m := Nat.succ_pos _
  have hNpos : (0:ℝ) < N := by positivity
  set d := min 1 (δ / (4 * (N : ℝ) ^ 2))
  have hd : 0 < d := lt_min one_pos (by positivity)
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdN : 4 * d * (N : ℝ) ^ 2 ≤ δ := by
    have := min_le_right 1 (δ / (4 * (N : ℝ) ^ 2))
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hmN : 8 * (N : ℝ) * B < (m : ℝ) ^ 2 := by
    have h1 : 8 * (2 * n + 1) * B < (m : ℝ) := by
      have := Nat.le_ceil (8 * (2 * (n : ℝ) + 1) * B)
      simp only [m]; push_cast; linarith
    have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
    have h2 : (N : ℝ) ≤ (2 * n + 1) * m := by
      simp only [N]; push_cast; nlinarith
    have h3 : 8 * (N : ℝ) * B ≤ 8 * ((2 * n + 1) * m) * B := by gcongr
    nlinarith
  refine ⟨d ^ 2, by positivity, fun a => ?_⟩
  by_contra hcon
  push_neg at hcon
  set lam : Fin N → ℝ := fun j => a + (j : ℝ) * (δ / N)
  have hlam : ∀ j, lam j ∈ Icc a (a + δ) := by
    intro j
    have hj : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast j.isLt
    have h0 : 0 ≤ ((j : ℕ) : ℝ) * (δ / N) := by positivity
    have h1 : ((j : ℕ) : ℝ) * (δ / N) ≤ δ := by
      rw [← mul_div_assoc, div_le_iff₀ hNpos]; nlinarith
    exact ⟨by simp only [lam]; linarith, by simp only [lam]; linarith⟩
  have hsep : ∀ i j, i ≠ j → δ / N ≤ |lam i - lam j| := by
    intro i j hij
    have hne : (i : ℕ) ≠ (j : ℕ) := Fin.val_ne_of_ne hij
    have h1 : (1:ℝ) ≤ |((i : ℕ) : ℝ) - (j : ℕ)| := by
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      · have : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
    have e : lam i - lam j = (((i : ℕ) : ℝ) - (j : ℕ)) * (δ / N) := by simp only [lam]; ring
    rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < δ / N)]
    nlinarith [(by positivity : (0:ℝ) < δ / N)]
  choose u u' hu hu' hp hlt using fun j : Fin N => hcon (lam j) (hlam j)
  -- normalize
  set F : Fin N → ℝ := fun j => ∫ t in (0:ℝ)..1, ‖u j t‖ ^ 2
  have hF : ∀ j, 0 < F j := by
    intro j
    have h0 : 0 ≤ ∫ t in (0:ℝ)..1, ‖-(Matrix.toEuclideanLin (J₀ n) (u' j t)) -
        Matrix.toEuclideanLin (Sinf t) (u j t) - lam j • u j t‖ ^ 2 :=
      intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
    have := h0.trans_lt (hlt j)
    exact pos_of_mul_pos_right this (sq_nonneg d)
  set κ : Fin N → ℝ := fun j => (Real.sqrt (F j))⁻¹
  have hκ2 : ∀ j, κ j ^ 2 * F j = 1 := by
    intro j
    simp only [κ, inv_pow, Real.sq_sqrt (hF j).le]
    exact inv_mul_cancel₀ (hF j).ne'
  have hκ0 : ∀ j, 0 ≤ κ j ^ 2 := fun j => sq_nonneg _
  set v : Fin N → ℝ → Vec n := fun j t => κ j • u j t
  set v' : Fin N → ℝ → Vec n := fun j t => κ j • u' j t
  have hv : ∀ j t, HasDerivAt (v j) (v' j t) t := fun j t => (hu j t).const_smul (κ j)
  have hv' : ∀ j, Continuous (v' j) := fun j => (hu' j).const_smul (κ j)
  have hpv : ∀ j, Function.Periodic (v j) 1 := fun j t => by
    simp only [v]; rw [hp j t]
  have h1 : ∀ j, ∫ t in (0:ℝ)..1, ‖v j t‖ ^ 2 = 1 := by
    intro j
    have e : ∀ t, ‖v j t‖ ^ 2 = κ j ^ 2 * ‖u j t‖ ^ 2 := fun t => by
      simp only [v, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    simp only [e, intervalIntegral.integral_const_mul]
    exact hκ2 j
  have hr : ∀ j, ∫ t in (0:ℝ)..1, ‖rsd (Sinf t) (lam j) (v j t) (v' j t)‖ ^ 2 ≤ d ^ 2 := by
    intro j
    have e : ∀ t, ‖rsd (Sinf t) (lam j) (v j t) (v' j t)‖ ^ 2 = κ j ^ 2 *
        ‖-(Matrix.toEuclideanLin (J₀ n) (u' j t)) - Matrix.toEuclideanLin (Sinf t) (u j t) -
          lam j • u j t‖ ^ 2 := fun t => by
      have : rsd (Sinf t) (lam j) (v j t) (v' j t) = κ j • rsd (Sinf t) (lam j) (u j t) (u' j t) := by
        simp only [rsd, v, v', map_smul, smul_sub, smul_neg, smul_comm (κ j) (lam j)]
      rw [this, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, rsd_eq]
    simp only [e, intervalIntegral.integral_const_mul]
    have := mul_le_mul_of_nonneg_left (hlt j).le (hκ0 j)
    calc _ ≤ κ j ^ 2 * (d ^ 2 * F j) := this
      _ = d ^ 2 * (κ j ^ 2 * F j) := by ring
      _ = d ^ 2 := by rw [hκ2 j, mul_one]
  exact core Sinf hSinf K δ a d hK hK0' hδ hd hd1 m N hm (by omega) hdN hmN lam hlam hsep v v'
    hv hv' hpv h1 hr

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Filter Topology
open scoped ContDiff

theorem solution {n : ℕ} (Sinf : ℝ → CauchyRiemannIndex.Mat n)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf) (δ : ℝ) (hδ : 0 < δ) :
    ∃ c > 0, ∀ a : ℝ, ∃ l ∈ Set.Icc a (a + δ), ∀ u u' : ℝ → CauchyRiemannIndex.Vec n,
      (∀ t, HasDerivAt u (u' t) t) → Continuous u' → Function.Periodic u 1 →
      c * ∫ t in (0:ℝ)..1, ‖u t‖ ^ 2 ≤ ∫ t in (0:ℝ)..1,
        ‖-(Matrix.toEuclideanLin (CauchyRiemannIndex.J₀ n) (u' t)) -
          Matrix.toEuclideanLin (Sinf t) (u t) - l • u t‖ ^ 2 :=
  exists_uniform_loop_gap_aux Sinf hSinf δ hδ
