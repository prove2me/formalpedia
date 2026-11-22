-- Prove2me | solution 1 for EllipsoidGLS.Rounded.eq_34
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:40:51.181511+00:00
-- url     : https://prove2.me/submissions/7d6579b8-0be2-4f88-b7b7-8793dabb0a09

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_EllipsoidGLS_Rounded_Basic
import Definitions.Def_EllipsoidGLS_Rounded_Run

open Matrix EllipsoidGLS.Rounded MeasureTheory
open scoped Pointwise

private lemma euclNorm_pos {n : ℕ} {c : Fin n → ℝ} (hc : c ≠ 0) : 0 < euclNorm c := by
  unfold euclNorm
  apply Real.sqrt_pos.mpr
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  have h1 : 0 < c i * c i := mul_self_pos.mpr hi
  have h2 : c i * c i ≤ ∑ j : Fin n, c j * c j :=
    Finset.single_le_sum (fun j _ => mul_self_nonneg (c j)) (Finset.mem_univ i)
  exact lt_of_lt_of_le h1 h2

private lemma ellipsoidBall_zero_one (m : ℕ) :
    LinearOptimization.ellipsoidBall (0 : Fin m → ℝ) 1 = {u : Fin m → ℝ | u ⬝ᵥ u ≤ 1} := by
  ext u
  simp [LinearOptimization.ellipsoidBall, LinearOptimization.ellipsoid]

private lemma volume_ellipsoidBall_zero_one_ne_top (m : ℕ) :
    volume (LinearOptimization.ellipsoidBall (0 : Fin m → ℝ) 1) ≠ ⊤ := by
  rw [ellipsoidBall_zero_one]
  have hsub : {u : Fin m → ℝ | u ⬝ᵥ u ≤ 1} ⊆ Set.univ.pi (fun _ : Fin m => Set.Icc (-1 : ℝ) 1) := by
    intro u hu j _
    have h1 : u j * u j ≤ u ⬝ᵥ u :=
      Finset.single_le_sum (fun i _ => mul_self_nonneg (u i)) (Finset.mem_univ j)
    have h2 : u j * u j ≤ 1 := h1.trans hu
    constructor <;> nlinarith
  have hlt : volume (Set.univ.pi (fun _ : Fin m => Set.Icc (-1 : ℝ) 1)) < ⊤ :=
    (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top
  exact ((measure_mono hsub).trans_lt hlt).ne

private lemma ofReal_unitBallVol (m : ℕ) :
    ENNReal.ofReal (unitBallVol m) =
      volume (LinearOptimization.ellipsoidBall (0 : Fin m → ℝ) 1) := by
  unfold unitBallVol
  exact ENNReal.ofReal_toReal (volume_ellipsoidBall_zero_one_ne_top m)

private lemma smul_ellipsoidBall_zero_one {m : ℕ} {a : ℝ} (ha : 0 < a) :
    a • LinearOptimization.ellipsoidBall (0 : Fin m → ℝ) 1 =
      {u : Fin m → ℝ | u ⬝ᵥ u ≤ a ^ 2} := by
  rw [ellipsoidBall_zero_one]
  ext u
  constructor
  · rintro ⟨v, hv, rfl⟩
    simp only [Set.mem_ofPred_eq] at hv ⊢
    have hdot : (a • v) ⬝ᵥ (a • v) = a ^ 2 * (v ⬝ᵥ v) := by
      simp [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hdot]
    nlinarith [sq_nonneg a]
  · intro hu
    simp only [Set.mem_ofPred_eq] at hu
    refine ⟨a⁻¹ • u, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      have hdot : (a⁻¹ • u) ⬝ᵥ (a⁻¹ • u) = (a ^ 2)⁻¹ * (u ⬝ᵥ u) := by
        simp [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hdot]
      have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
      rw [inv_mul_le_iff₀ ha2]
      linarith
    · simp [smul_smul, mul_inv_cancel₀ ha.ne']

theorem solution {n : ℕ} (hn : 2 ≤ n) (K : Set (Fin n → ℝ)) (hK : Convex ℝ K)
    (c x₀ y : Fin n → ℝ) (hc : c ≠ 0) (r : ℝ) (hr : 0 < r)
    (hdisc : {z | euclNorm (z - x₀) ≤ r ∧ c ⬝ᵥ z = c ⬝ᵥ x₀} ⊆ K)
    (hy : y ∈ K) (hxy : c ⬝ᵥ x₀ < c ⬝ᵥ y)
    (t : ℝ) (ht₀ : c ⬝ᵥ x₀ ≤ t) (ht₁ : t ≤ c ⬝ᵥ y) :
    ENNReal.ofReal
        (unitBallVol (n - 1) * r ^ (n - 1) * (c ⬝ᵥ y - c ⬝ᵥ x₀) / (n * euclNorm c) *
          ((c ⬝ᵥ y - t) / (c ⬝ᵥ y - c ⬝ᵥ x₀)) ^ n) ≤
      MeasureTheory.volume {z | z ∈ K ∧ t ≤ c ⬝ᵥ z} := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hc_pos : 0 < euclNorm c := euclNorm_pos hc
  have hΔ_pos : 0 < c ⬝ᵥ y - c ⬝ᵥ x₀ := sub_pos.mpr hxy
  set lam : ℝ := (c ⬝ᵥ y - t) / (c ⬝ᵥ y - c ⬝ᵥ x₀)
  have hlam_nonneg : 0 ≤ lam := div_nonneg (sub_nonneg.mpr ht₁) hΔ_pos.le
  have hlam_le_one : lam ≤ 1 := (div_le_one hΔ_pos).mpr (by linarith)
  -- Step 1: Extend c / ‖c‖ to an orthonormal basis of EuclideanSpace ℝ (Fin (m + 1))
  let e₀ : EuclideanSpace ℝ (Fin (m + 1)) := WithLp.toLp 2 ((euclNorm c)⁻¹ • c)
  have he₀_norm : ‖e₀‖ = 1 := by
    have hinner : @inner ℝ _ _ e₀ e₀ = 1 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      have hcc : c ⬝ᵥ c = (euclNorm c) ^ 2 := by
        unfold euclNorm
        rw [Real.sq_sqrt]
        exact Finset.sum_nonneg fun i _ => mul_self_nonneg (c i)
      simp only [e₀, star_trivial]
      have hdot : ((euclNorm c)⁻¹ • c) ⬝ᵥ ((euclNorm c)⁻¹ • c) =
          ((euclNorm c) ^ 2)⁻¹ * (c ⬝ᵥ c) := by
        simp [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [hdot, hcc, inv_mul_cancel₀ (sq_pos_of_pos hc_pos).ne']
    have hsq : ‖e₀‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq, hinner]
    nlinarith [norm_nonneg e₀]
  have horth_single :
      Orthonormal ℝ (({0} : Set (Fin (m + 1))).domRestrict (fun _ => e₀)) := by
    refine ⟨fun ⟨i, _⟩ => he₀_norm, ?_⟩
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    exfalso
    simp only [Set.mem_singleton_iff] at hi hj
    exact hij (Subtype.ext (hi.trans hj.symm))
  obtain ⟨b, hb⟩ :=
    horth_single.exists_orthonormalBasis_extension_of_card_eq
      (finrank_euclideanSpace (𝕜 := ℝ) (ι := Fin (m + 1)))
  have hb0 : b 0 = e₀ := hb 0 (Set.mem_singleton 0)
  let bv : Fin (m + 1) → Fin (m + 1) → ℝ := fun j => WithLp.ofLp (b j)
  have hbv_dot : ∀ j k : Fin (m + 1), bv j ⬝ᵥ bv k = if j = k then 1 else 0 := by
    intro j k
    have h1 : @inner ℝ _ _ (b k) (b j) = bv j ⬝ᵥ bv k := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [bv]
    rw [← h1, orthonormal_iff_ite.mp b.orthonormal k j]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk, Ne.symm hjk]
  have hbv0 : bv 0 = (euclNorm c)⁻¹ • c := by
    simp [bv, hb0, e₀]
  have hc_eq : c = euclNorm c • bv 0 := by
    rw [hbv0, smul_smul, mul_inv_cancel₀ hc_pos.ne', one_smul]
  have hc_dot_bv : ∀ j : Fin m, c ⬝ᵥ bv j.succ = 0 := by
    intro j
    rw [hc_eq, smul_dotProduct, hbv_dot 0 j.succ]
    simp [(Fin.succ_ne_zero j).symm]
  -- Step 2: Matrices Q (orthogonal) and M (first column y - x₀, remaining columns bv j.succ)
  let Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Matrix.of fun i j => bv j i
  let M : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    Matrix.of fun i j => if j = 0 then (y - x₀) i else bv j i
  have hQtQ : Qᵀ * Q = 1 := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply, Q]
    exact hbv_dot j k
  have hQ_det_abs : |Q.det| = 1 := by
    have h1 : Q.det ^ 2 = 1 := by
      calc Q.det ^ 2 = Qᵀ.det * Q.det := by rw [Matrix.det_transpose, sq]
        _ = (Qᵀ * Q).det := (Matrix.det_mul Qᵀ Q).symm
        _ = 1 := by rw [hQtQ, Matrix.det_one]
    have h2 : |Q.det| ^ 2 = 1 := by rw [sq_abs, h1]
    nlinarith [abs_nonneg Q.det]
  let B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := Qᵀ * M
  have hB_entry : ∀ r k : Fin (m + 1),
      B r k = if k = 0 then bv r ⬝ᵥ (y - x₀) else if r = k then 1 else 0 := by
    intro r k
    simp only [B, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Q, M]
    by_cases hk : k = 0
    · subst hk
      simp only [↓reduceIte]
      rfl
    · simp only [hk, ↓reduceIte]
      exact hbv_dot r k
  have hB_lower : B.IsLowerTriangular := by
    intro r k hrk
    have hlt : r < k := OrderDual.toDual_lt_toDual.mp hrk
    rw [hB_entry]
    have hk0 : k ≠ 0 := by
      intro h
      subst h
      exact (Fin.not_lt_zero r) hlt
    simp [hk0, ne_of_lt hlt]
  have hB_det : B.det = (c ⬝ᵥ y - c ⬝ᵥ x₀) / euclNorm c := by
    rw [Matrix.det_of_isLowerTriangular B hB_lower, Fin.prod_univ_succ]
    have hprod : (∏ j : Fin m, B j.succ j.succ) = 1 := by
      refine Finset.prod_eq_one fun j _ => ?_
      rw [hB_entry]
      simp [Fin.succ_ne_zero]
    rw [hprod, mul_one, hB_entry 0 0]
    simp only [↓reduceIte, hbv0, smul_dotProduct, dotProduct_sub]
    ring
  have hM_det_abs : |M.det| = (c ⬝ᵥ y - c ⬝ᵥ x₀) / euclNorm c := by
    have h1 : |B.det| = |M.det| := by
      calc |B.det| = |Qᵀ.det * M.det| := by rw [Matrix.det_mul]
        _ = |Q.det| * |M.det| := by rw [Matrix.det_transpose, abs_mul]
        _ = |M.det| := by rw [hQ_det_abs, one_mul]
    rw [← h1, hB_det, abs_of_pos (div_pos hΔ_pos hc_pos)]
  -- Step 3: Standard cone C₀ and affine inclusion T '' C₀ ⊆ {z ∈ K | t ≤ c ⬝ᵥ z}
  let C₀ : Set (Fin (m + 1) → ℝ) :=
    {w | w 0 ∈ Set.Ioc 0 lam ∧
      (fun j : Fin m => w j.succ) ⬝ᵥ (fun j : Fin m => w j.succ) ≤ (r * w 0) ^ 2}
  have hM_mulVec : ∀ w : Fin (m + 1) → ℝ,
      M.mulVec w = w 0 • (y - x₀) + ∑ j : Fin m, w j.succ • bv j.succ := by
    intro w
    ext i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply,
      Finset.sum_apply, smul_eq_mul, M, Matrix.of_apply, ↓reduceIte, Fin.succ_ne_zero]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ => by ring
  let T : (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) := fun w => y - M.mulVec w
  have hT_sub : T '' C₀ ⊆ {z | z ∈ K ∧ t ≤ c ⬝ᵥ z} := by
    rintro _ ⟨w, ⟨⟨hs_pos, hs_le⟩, hu_le⟩, rfl⟩
    set s := w 0
    set u : Fin m → ℝ := fun j => w j.succ
    set wsum : Fin (m + 1) → ℝ := ∑ j : Fin m, u j • bv j.succ
    set v : Fin (m + 1) → ℝ := s⁻¹ • wsum
    set z : Fin (m + 1) → ℝ := x₀ - v
    have hwsum_c : c ⬝ᵥ wsum = 0 := by
      simp only [wsum, dotProduct_sum, dotProduct_smul, smul_eq_mul, hc_dot_bv, mul_zero,
        Finset.sum_const_zero]
    have hwsum_dot : wsum ⬝ᵥ wsum = u ⬝ᵥ u := by
      simp only [wsum, sum_dotProduct, dotProduct_sum, smul_dotProduct, dotProduct_smul,
        smul_eq_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hinner : (∑ k : Fin m, u k * (bv k.succ ⬝ᵥ bv j.succ)) = u j := by
        calc ∑ k : Fin m, u k * (bv k.succ ⬝ᵥ bv j.succ)
            = ∑ k : Fin m, if k = j then u k else 0 := by
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [hbv_dot k.succ j.succ]
              by_cases hkj : k = j
              · subst hkj; simp
              · simp [hkj]
          _ = u j := by simp
      rw [hinner]
    have hz_mem : z ∈ K := by
      apply hdisc
      refine ⟨?_, ?_⟩
      · unfold euclNorm
        have hsub : z - x₀ = -v := by simp [z]
        rw [hsub, neg_dotProduct, dotProduct_neg, neg_neg]
        have hv_dot : v ⬝ᵥ v = (s ^ 2)⁻¹ * (u ⬝ᵥ u) := by
          simp only [v, smul_dotProduct, dotProduct_smul, smul_eq_mul, hwsum_dot]
          ring
        rw [hv_dot]
        have hle : (s ^ 2)⁻¹ * (u ⬝ᵥ u) ≤ r ^ 2 := by
          have hs2 : 0 < s ^ 2 := sq_pos_of_pos hs_pos
          rw [inv_mul_le_iff₀ hs2]
          calc u ⬝ᵥ u ≤ (r * s) ^ 2 := hu_le
            _ = s ^ 2 * r ^ 2 := by ring
        exact (Real.sqrt_le_sqrt hle).trans_eq (Real.sqrt_sq hr.le)
      · simp only [z, dotProduct_sub, v, dotProduct_smul, smul_eq_mul, hwsum_c, mul_zero, sub_zero]
    have hTw : T w = (1 - s) • y + s • z := by
      have hsv : s • v = wsum := by
        simp [v, smul_smul, mul_inv_cancel₀ hs_pos.ne']
      ext i
      simp only [T, hM_mulVec, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, z]
      have hwi : (s • v) i = wsum i := congrFun hsv i
      simp only [Pi.smul_apply, smul_eq_mul] at hwi
      change y i - (s * (y i - x₀ i) + wsum i) = (1 - s) * y i + s * (x₀ i - v i)
      linarith
    have hs_le_one : s ≤ 1 := hs_le.trans hlam_le_one
    refine ⟨?_, ?_⟩
    · rw [hTw]
      exact hK hy hz_mem (sub_nonneg.mpr hs_le_one) hs_pos.le (by ring)
    · rw [hTw, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have hcz : c ⬝ᵥ z = c ⬝ᵥ x₀ := by
        simp only [z, dotProduct_sub, v, dotProduct_smul, smul_eq_mul, hwsum_c, mul_zero, sub_zero]
      rw [hcz]
      have hprod : s * (c ⬝ᵥ y - c ⬝ᵥ x₀) ≤ c ⬝ᵥ y - t := by
        have := mul_le_mul_of_nonneg_right hs_le hΔ_pos.le
        rwa [div_mul_cancel₀ _ hΔ_pos.ne'] at this
      linarith
  -- Step 4: Volume of T '' C₀ via linear map determinant and translation invariance
  have hvol_T : volume (T '' C₀) =
      ENNReal.ofReal ((c ⬝ᵥ y - c ⬝ᵥ x₀) / euclNorm c) * volume C₀ := by
    have hT_eq : T '' C₀ = (fun z => y + z) '' (Matrix.toLin' (-M) '' C₀) := by
      rw [← Set.image_comp]
      congr 1
      ext w i
      simp [T, Function.comp, Matrix.toLin'_apply, sub_eq_add_neg]
    rw [hT_eq]
    have htrans : volume ((fun z => y + z) '' (Matrix.toLin' (-M) '' C₀)) =
        volume (Matrix.toLin' (-M) '' C₀) := by
      rw [Set.image_add_left, measure_preimage_add]
    rw [htrans, Measure.addHaar_image_linearMap, LinearMap.det_toLin', Matrix.det_neg,
      abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, hM_det_abs]
  -- Step 5: Volume of C₀ via piFinSuccAbove and Tonelli's theorem
  let e : (Fin (m + 1) → ℝ) ≃ᵐ ℝ × (Fin m → ℝ) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  let S : Set (ℝ × (Fin m → ℝ)) :=
    {p | p.1 ∈ Set.Ioc 0 lam ∧ p.2 ⬝ᵥ p.2 ≤ (r * p.1) ^ 2}
  have hS_meas : MeasurableSet S := by
    have h1 : MeasurableSet {p : ℝ × (Fin m → ℝ) | p.1 ∈ Set.Ioc 0 lam} :=
      measurableSet_Ioc.preimage measurable_fst
    have hcont : Continuous (fun p : ℝ × (Fin m → ℝ) => p.2 ⬝ᵥ p.2 - (r * p.1) ^ 2) := by
      refine Continuous.sub ?_ ?_
      · exact continuous_finsetSum _ fun i _ =>
          ((continuous_apply i).comp continuous_snd).mul ((continuous_apply i).comp continuous_snd)
      · exact (continuous_const.mul continuous_fst).pow 2
    have h2 : MeasurableSet {p : ℝ × (Fin m → ℝ) | p.2 ⬝ᵥ p.2 ≤ (r * p.1) ^ 2} := by
      have heq : {p : ℝ × (Fin m → ℝ) | p.2 ⬝ᵥ p.2 ≤ (r * p.1) ^ 2} =
          (fun p => p.2 ⬝ᵥ p.2 - (r * p.1) ^ 2) ⁻¹' Set.Iic 0 := by
        ext p; simp
      rw [heq]
      exact measurableSet_Iic.preimage hcont.measurable
    exact h1.inter h2
  have hC₀_eq : C₀ = e ⁻¹' S := by
    ext w
    simp [C₀, S, e, MeasurableEquiv.piFinSuccAbove]
    intro _ _
    rfl
  have hV_nonneg : 0 ≤ unitBallVol m := ENNReal.toReal_nonneg
  have hvol_C₀ : volume C₀ =
      ENNReal.ofReal (unitBallVol m * r ^ m * (lam ^ (m + 1) / (m + 1))) := by
    have hmp : MeasurePreserving e volume (volume.prod volume) :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    rw [hC₀_eq, hmp.measure_preimage hS_meas.nullMeasurableSet, Measure.prod_apply hS_meas]
    have hslice : ∀ s : ℝ,
        volume (Prod.mk s ⁻¹' S) =
          (Set.Ioc 0 lam).indicator
            (fun s => ENNReal.ofReal (unitBallVol m * r ^ m) * ENNReal.ofReal (s ^ m)) s := by
      intro s
      by_cases hs : s ∈ Set.Ioc 0 lam
      · rw [Set.indicator_of_mem hs]
        have hpre : Prod.mk s ⁻¹' S = (r * s) • LinearOptimization.ellipsoidBall (0 : Fin m → ℝ) 1 := by
          rw [smul_ellipsoidBall_zero_one (mul_pos hr hs.1)]
          ext u
          simp [S, hs.1, hs.2]
        rw [hpre, Measure.addHaar_smul_of_nonneg _ (mul_pos hr hs.1).le,
          Module.finrank_fin_fun, ← ofReal_unitBallVol, mul_pow,
          ENNReal.ofReal_mul (pow_nonneg hr.le m),
          ENNReal.ofReal_mul hV_nonneg]
        ring
      · rw [Set.indicator_of_notMem hs]
        have hpre : Prod.mk s ⁻¹' S = ∅ := by
          ext u
          simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false, S, Set.mem_ofPred_eq]
          intro h
          exact hs h.1
        rw [hpre, measure_empty]
    simp_rw [hslice]
    rw [lintegral_indicator measurableSet_Ioc,
      lintegral_const_mul _ (by fun_prop)]
    have hint_eq :
        ∫⁻ s in Set.Ioc 0 lam, ENNReal.ofReal (s ^ m) ∂volume =
          ENNReal.ofReal (lam ^ (m + 1) / (m + 1)) := by
      have hint : IntegrableOn (fun s : ℝ => s ^ m) (Set.Ioc 0 lam) volume :=
        (continuous_pow m).continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 lam)] (fun s : ℝ => s ^ m) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
        exact pow_nonneg hs.1.le m
      rw [← ofReal_integral_eq_lintegral_ofReal hint hnn,
        ← intervalIntegral.integral_of_le hlam_nonneg, integral_pow]
      simp
    rw [hint_eq, ← ENNReal.ofReal_mul (mul_nonneg hV_nonneg (pow_nonneg hr.le m))]
  -- Step 6: Combine everything
  calc ENNReal.ofReal
        (unitBallVol (m + 1 - 1) * r ^ (m + 1 - 1) * (c ⬝ᵥ y - c ⬝ᵥ x₀) /
            ((m + 1 : ℕ) * euclNorm c) *
          ((c ⬝ᵥ y - t) / (c ⬝ᵥ y - c ⬝ᵥ x₀)) ^ (m + 1))
      = ENNReal.ofReal ((c ⬝ᵥ y - c ⬝ᵥ x₀) / euclNorm c) *
          ENNReal.ofReal (unitBallVol m * r ^ m * (lam ^ (m + 1) / (m + 1))) := by
        rw [← ENNReal.ofReal_mul (div_pos hΔ_pos hc_pos).le]
        congr 1
        simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, lam]
        field_simp
    _ = volume (T '' C₀) := by rw [hvol_T, hvol_C₀]
    _ ≤ volume {z | z ∈ K ∧ t ≤ c ⬝ᵥ z} := measure_mono hT_sub
