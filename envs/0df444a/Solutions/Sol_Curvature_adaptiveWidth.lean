-- Prove2me | solution 1 for Curvature.adaptiveWidth
-- status  : ACCEPTED   (prove)
-- author  : @ssakaue
-- created : 2026-11-24T07:32:48.750205+00:00
-- url     : https://prove2.me/submissions/5c54186f-66ec-4883-999c-039ae543a1bc

import Definitions.Def_Curvature_AdaptivePredictor

section
set_option autoImplicit false
namespace Curvature

variable {d : ℕ}


theorem dotProduct_le_norm₂_mul (x y : Vec d) :
    dotProduct x y ≤ norm₂ x * norm₂ y := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hsq : dotProduct x y ^ 2 ≤ (norm₂ x * norm₂ y) ^ 2 := by
    rw [mul_pow, norm₂_sq, norm₂_sq]
    simpa only [pow_two, dotProduct] using h
  exact le_of_sq_le_sq hsq (mul_nonneg (norm₂_nonneg x) (norm₂_nonneg y))


end Curvature
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}


theorem adaptiveRate_pos (i : ℕ) : 0 < adaptiveRate i := by
  unfold adaptiveRate
  positivity

theorem adaptiveRate_le (i : ℕ) : adaptiveRate i ≤ 1 / 8 := by
  unfold adaptiveRate
  apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
  have hpow : 1 ≤ (2 : ℝ)^i := one_le_pow₀ (by norm_num)
  linarith only [hpow]

theorem adaptiveRate_succ (i : ℕ) : adaptiveRate (i + 1) = adaptiveRate i / 2 := by
  simp only [adaptiveRate, pow_succ]
  ring

theorem adaptiveStart_lt_iff (i T : ℕ) : adaptiveStart i < T ↔ 2^i ≤ T := by
  unfold adaptiveStart
  have := Nat.one_le_two_pow (n := i)
  omega

theorem adaptiveNegative_nonneg (T : ℕ) (r : ℕ → ℝ) : 0 ≤ adaptiveNegative T r :=
  Finset.sum_nonneg fun t _ => le_max_left 0 (-r t)

theorem adaptiveNegative_le (M : ℝ) (hM : 0 ≤ M) (T : ℕ) (r : ℕ → ℝ)
    (hr : ∀ t < T, |r t| ≤ M) : adaptiveNegative T r ≤ M * T := by
  unfold adaptiveNegative
  calc
    _ ≤ ∑ _ ∈ Finset.range T, M := Finset.sum_le_sum fun t ht =>
      max_le hM ((neg_le_abs (r t)).trans (hr t (Finset.mem_range.mp ht)))
    _ = _ := by simp [mul_comm]

theorem adaptiveLoss_sum_identity (θ : ℝ) (T : ℕ) (r : ℕ → ℝ) :
    (∑ t ∈ Finset.range T, adaptiveLoss θ (r t)) =
      (1 - θ) * (∑ t ∈ Finset.range T, r t) - 2 * θ * adaptiveNegative T r := by
  unfold adaptiveNegative
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro t _
  by_cases ht : 0 ≤ r t
  · rw [adaptiveLoss, abs_of_nonneg ht, max_eq_left (neg_nonpos.mpr ht)]
    ring
  · have hn := le_of_not_ge ht
    rw [adaptiveLoss, abs_of_nonpos hn, max_eq_right (neg_nonneg.mpr hn)]
    ring

theorem masterRatewise_of_signed {C : ℝ} (hC : 0 ≤ C) (T i : ℕ) (r : ℕ → ℝ)
    (hsigned : (∑ t ∈ Finset.range T, adaptiveLoss (2 * adaptiveRate i) (r t)) ≤
      2 * C / adaptiveRate i) :
    (∑ t ∈ Finset.range T, r t) ≤
      8 * C / (3 * adaptiveRate i) + (16/3) * adaptiveRate i * adaptiveNegative T r := by
  have hr := adaptiveRate_pos i
  have hrate := adaptiveRate_le i
  have hN := adaptiveNegative_nonneg T r
  rw [adaptiveLoss_sum_identity] at hsigned
  by_cases hp : 0 ≤ ∑ t ∈ Finset.range T, r t
  · have hcoef := mul_le_mul_of_nonneg_right
      (show (3/4 : ℝ) ≤ 1 - 2 * adaptiveRate i by linarith only [hrate]) hp
    have hdiv : 8 * C / (3 * adaptiveRate i) = (4/3) * (2 * C / adaptiveRate i) := by
      ring
    rw [hdiv]
    linarith only [hsigned, hcoef]
  · exact (le_of_not_ge hp).trans (by positivity)

private theorem exists_dyadic_neighbors {x : ℝ} (hx : 1 ≤ x) :
    ∃ i : ℕ, (2 : ℝ)^i ≤ x ∧ x < (2 : ℝ)^(i+1) := by
  have hexists : ∃ n : ℕ, x < (2 : ℝ)^n := by
    obtain ⟨n, hn⟩ := exists_nat_gt x
    exact ⟨n, hn.trans (by exact_mod_cast (Nat.lt_two_pow_self : n < 2^n))⟩
  have hfind := Nat.find_spec hexists
  cases he : Nat.find hexists with
  | zero => simp [he, not_lt_of_ge hx] at hfind
  | succ i =>
    refine ⟨i, le_of_not_gt (Nat.find_min hexists ?_), ?_⟩
    · rw [he]
      exact Nat.lt_succ_self i
    · simpa only [he] using hfind

/-- Select an awake learner and optimize the rate-dependent upper bound. -/
theorem adaptiveRegret_of_masterRatewise {C M n R : ℝ} {T : ℕ}
    (hC : 0 < C) (hMC : M ≤ C) (hT : 0 < T) (hn : 0 ≤ n)
    (hnT : n ≤ M * T)
    (hrate : ∀ i : ℕ, 2^i ≤ T →
      R ≤ 8*C / (3 * adaptiveRate i) + (16/3) * adaptiveRate i * n) :
    R ≤ 24 * (C + Real.sqrt (C * n)) := by
  by_cases ht : n < C
  · have hT1 : 1 ≤ T := by omega
    have h := hrate 0 (by simpa only [pow_zero] using hT1)
    norm_num [adaptiveRate] at h
    linarith only [h, ht, hC, Real.sqrt_nonneg (C*n)]
  · have hnC := le_of_not_gt ht
    let s := Real.sqrt (n / C)
    have hs1 : 1 ≤ s := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ((one_le_div hC).mpr hnC)
    have hs : 0 < s := zero_lt_one.trans_le hs1
    have hsSq : s^2 = n / C := Real.sq_sqrt (div_nonneg hn hC.le)
    have hCsn : C * s^2 = n := by
      rw [hsSq, mul_div_cancel₀ _ hC.ne']
    have hCsSqrt : C*s = Real.sqrt (C*n) := by
      symm
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).mpr
      calc
        C*n = C*(C*s^2) := by rw [hCsn]
        _ = (C*s)^2 := by ring
    obtain ⟨i, hlo, hhi⟩ := exists_dyadic_neighbors hs1
    have hTc : 1 ≤ (T : ℝ) := by exact_mod_cast hT
    have hsT : s ≤ (T : ℝ) := by
      apply (Real.sqrt_le_left (by positivity)).mpr
      apply (div_le_iff₀ hC).mpr
      have hCT := mul_le_mul_of_nonneg_right hMC (Nat.cast_nonneg T : 0 ≤ (T : ℝ))
      have hTT := mul_le_mul_of_nonneg_right hTc (Nat.cast_nonneg T : 0 ≤ (T : ℝ))
      have hbound := mul_le_mul_of_nonneg_right hTT hC.le
      nlinarith only [hnT, hCT, hbound]
    have hactive : 2^i ≤ T := by
      exact_mod_cast hlo.trans hsT
    have hfirst : 8 * C / (3 * adaptiveRate i) ≤ (64/3) * (C*s) := by
      rw [show 8*C / (3 * adaptiveRate i) = (64/3) * (C*(2:ℝ)^i) by
        unfold adaptiveRate
        field_simp
        ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlo hC.le) (by norm_num)
    have hsecond : (16/3) * adaptiveRate i * n ≤ (4/3) * (C*s) := by
      rw [← hCsn]
      unfold adaptiveRate
      field_simp
      rw [pow_succ] at hhi
      linarith only [hhi]
    have h := hrate i hactive
    rw [hCsSqrt] at hfirst hsecond
    linarith only [h, hfirst, hsecond, hC, Real.sqrt_nonneg (C*n)]

/-- Transfer linearized regret to convex loss using the observed subgradients. -/
theorem adaptiveConvexTransfer {K : Set (Vec d)} (hK : IsCompact K)
    (T : ℕ) (w g : ℕ → Vec d) (f : ℕ → Vec d → ℝ) (u : Vec d) (hu : u ∈ K)
    (hw : ∀ t < T, w t ∈ K) (hcont : ∀ t < T, ContinuousOn (f t) K)
    (hsub : ∀ t < T, ∀ v ∈ K, f t (w t) - f t v ≤ excess (g t) (w t) v) :
    (∑ t ∈ Finset.range T, (f t (w t) - f t u)) ≤
      (∑ t ∈ Finset.range T, excess (g t) (w t) u) ∧
    adaptiveNegative T (fun t => excess (g t) (w t) u) ≤
      ∑ t ∈ Finset.range T, (f t u - sInf (f t '' K)) := by
  constructor
  · exact Finset.sum_le_sum fun t ht => hsub t (Finset.mem_range.mp ht) u hu
  · apply Finset.sum_le_sum
    intro t ht
    have ht' := Finset.mem_range.mp ht
    have hbelow := (hK.image_of_continuousOn (hcont t ht')).bddBelow
    refine max_le (sub_nonneg.mpr (csInf_le hbelow ⟨u, hu, rfl⟩)) ?_
    have hminw := csInf_le hbelow ⟨w t, hw t ht', rfl⟩
    linarith only [hminw, hsub t ht' u hu]

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ}


theorem adaptiveScale_bounds {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1) (a : ℝ) :
    (1 - θ) / (1 + θ) ≤ adaptiveScale θ a ∧
      adaptiveScale θ a ≤ (1 + θ) / (1 - θ) := by
  have hp : 0 < 1 + θ := by positivity
  have hm : 0 < 1 - θ := sub_pos.mpr hθ'
  have hl : (1 - θ) / (1 + θ) ≤ 1 := (div_le_one hp).mpr (by linarith only [hθ])
  have hu : 1 ≤ (1 + θ) / (1 - θ) := (one_le_div hm).mpr (by linarith only [hθ])
  unfold adaptiveScale
  split <;> (try split) <;> constructor <;> first | rfl | exact hl | exact hu | exact hl.trans hu

theorem adaptiveScale_pos {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1) (a : ℝ) :
    0 < adaptiveScale θ a :=
  (div_pos (sub_pos.mpr hθ') (by positivity)).trans_le (adaptiveScale_bounds hθ hθ' a).1

theorem adaptiveScale_le_seventeen_fifteenths {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/16)
    (a : ℝ) : adaptiveScale θ a ≤ 17/15 := by
  have hlt : θ < 1 := by linarith only [hθ']
  refine (adaptiveScale_bounds hθ hlt a).2.trans ((div_le_iff₀ (sub_pos.mpr hlt)).mpr ?_)
  linarith only [hθ']

theorem adaptiveScaledInput_norm {G : ℝ} (g : Vec d) (hg : norm₂ g ≤ G)
    (i : ℕ) (a : ℝ) : norm₂ (adaptiveScale (adaptiveRate i / 2) a • g) ≤ 2 * G := by
  have hθ : 0 ≤ adaptiveRate i / 2 := by have := adaptiveRate_pos i; positivity
  have hθ' : adaptiveRate i / 2 ≤ 1/16 := by linarith only [adaptiveRate_le i]
  have hp := adaptiveScale_pos hθ (by linarith only [hθ']) a
  have hmax := adaptiveScale_le_seventeen_fifteenths hθ hθ' a
  rw [norm₂_smul, abs_of_pos hp]
  exact mul_le_mul (hmax.trans (by norm_num)) hg (norm₂_nonneg _) (by norm_num)

private theorem adaptiveScale_cancel {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ < 1) (a : ℝ) :
    adaptiveLoss θ a + adaptiveLoss θ (adaptiveScale θ a * (-a)) = 0 := by
  have hp : 0 < 1 + θ := by positivity
  have hm : 0 < 1 - θ := sub_pos.mpr hθ'
  rw [adaptiveLoss, adaptiveLoss, abs_mul, abs_neg,
    abs_of_pos (adaptiveScale_pos hθ hθ' a)]
  rcases lt_trichotomy 0 a with ha | rfl | ha
  · rw [abs_of_pos ha]
    simp only [adaptiveScale, if_pos ha]
    field_simp [hp.ne']
    ring
  · simp
  · rw [abs_of_neg ha]
    simp only [adaptiveScale, if_neg (not_lt_of_ge ha.le), if_pos ha]
    field_simp [hm.ne']
    ring

/-- The scalar comparison between a mixture prediction and a scaled base learner. -/
theorem adaptiveScalarBridge {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1/5) (r a : ℝ) :
    adaptiveLoss (4 * θ) r ≤ adaptiveLoss θ a +
      adaptiveLoss θ (adaptiveScale θ a * (r - a)) := by
  have hlt : θ < 1 := by linarith only [hθ']
  let s := adaptiveScale θ a
  have hs : 0 < s := adaptiveScale_pos hθ hlt a
  have hp : 0 < 1 + θ := by positivity
  have hm : 0 < 1 - θ := sub_pos.mpr hlt
  obtain ⟨hslo, hshi⟩ := adaptiveScale_bounds hθ hlt a
  have hlo : 1 - 4 * θ ≤ s * (1 - θ) := calc
    _ ≤ (1 - θ) / (1 + θ) * (1 - θ) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hp]
      nlinarith only [hθ, sq_nonneg θ]
    _ ≤ _ := mul_le_mul_of_nonneg_right hslo hm.le
  have hhi : s * (1 + θ) ≤ 1 + 4 * θ := calc
    _ ≤ (1 + θ) / (1 - θ) * (1 + θ) := mul_le_mul_of_nonneg_right hshi hp.le
    _ ≤ _ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hm]
      nlinarith only [mul_nonneg hθ (show 0 ≤ 1 - 5*θ by linarith only [hθ'])]
  have habs : |r - a| - |-a| ≤ |r| := by
    simpa only [sub_neg_eq_add, sub_add_cancel] using abs_sub_abs_le_abs_sub (r-a) (-a)
  have hcancel := adaptiveScale_cancel hθ hlt a
  change adaptiveLoss θ a + adaptiveLoss θ (s * (-a)) = 0 at hcancel
  simp only [adaptiveLoss, abs_mul s, abs_of_pos hs] at hcancel
  change adaptiveLoss (4 * θ) r ≤ adaptiveLoss θ a + adaptiveLoss θ (s * (r-a))
  calc
    _ ≤ s*r - θ*s*|r| := by
      unfold adaptiveLoss
      rcases le_total 0 r with hr | hr
      · rw [abs_of_nonneg hr]
        nlinarith only [mul_le_mul_of_nonneg_right hlo hr]
      · rw [abs_of_nonpos hr]
        nlinarith only [mul_le_mul_of_nonpos_right hhi hr]
    _ ≤ s*r - θ*s*(|r-a| - |-a|) :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left habs (mul_nonneg hθ hs.le)) _
    _ = _ := by
      simp only [adaptiveLoss, abs_mul s, abs_of_pos hs]
      linarith only [hcancel]

theorem adaptiveDormantBound (i : ℕ) (M : ℝ) (hM : 0 ≤ M) (r : ℕ → ℝ)
    (hr : ∀ t < adaptiveStart i, r t ≤ M) :
    (∑ t ∈ Finset.range (adaptiveStart i), adaptiveLoss (2 * adaptiveRate i) (r t)) ≤
      M / (8 * adaptiveRate i) := by
  have hs : (adaptiveStart i : ℝ) ≤ (2 : ℝ)^i := by
    exact_mod_cast (Nat.sub_le (2^i) 1)
  have hsum :
      (∑ t ∈ Finset.range (adaptiveStart i), adaptiveLoss (2 * adaptiveRate i) (r t)) ≤
      M * (adaptiveStart i : ℝ) := by
    calc
      _ ≤ ∑ _ ∈ Finset.range (adaptiveStart i), M := by
        apply Finset.sum_le_sum
        intro t ht
        have hn := mul_nonneg (show 0 ≤ 2 * adaptiveRate i by have := adaptiveRate_pos i; positivity)
          (abs_nonneg (r t))
        unfold adaptiveLoss
        linarith only [hr t (Finset.mem_range.mp ht), hn]
      _ = _ := by simp [mul_comm]
  refine hsum.trans ((mul_le_mul_of_nonneg_left hs hM).trans_eq ?_)
  unfold adaptiveRate
  field_simp

/-- Combine the mixture and scaled base learner bounds with the rounds before the learner starts. -/
theorem adaptiveMasterSigned_of_awake (T i : ℕ) (hawake : 2^i ≤ T)
    (M C₀ : ℝ) (hM : 0 ≤ M) (r a : ℕ → ℝ) (hr : ∀ t < T, r t ≤ M)
    (hmix : (∑ t ∈ Finset.Ico (adaptiveStart i) T, adaptiveLoss (adaptiveRate i / 2) (a t)) ≤
      256 * M * Real.log 2 / adaptiveRate i + (7/3) * M)
    (hbase : (∑ t ∈ Finset.Ico (adaptiveStart i) T,
      adaptiveLoss (adaptiveRate i / 2) (adaptiveScale (adaptiveRate i / 2) (a t) *
        (r t - a t))) ≤ 2 * C₀ / adaptiveRate i) :
    (∑ t ∈ Finset.range T, adaptiveLoss (2 * adaptiveRate i) (r t)) ≤
      2 * (C₀ + 256 * M) / adaptiveRate i := by
  have he : 0 < adaptiveRate i := adaptiveRate_pos i
  have he' := adaptiveRate_le i
  have hθ : 0 ≤ adaptiveRate i/2 := by positivity
  have hθ' : adaptiveRate i/2 ≤ 1/5 := by linarith only [he']
  have hstart := (adaptiveStart_lt_iff i T).mpr hawake
  have hdormant := adaptiveDormantBound i M hM r fun t ht => hr t (ht.trans hstart)
  have hbridge : (∑ t ∈ Finset.Ico (adaptiveStart i) T,
      adaptiveLoss (2 * adaptiveRate i) (r t)) ≤
      (∑ t ∈ Finset.Ico (adaptiveStart i) T, adaptiveLoss (adaptiveRate i/2) (a t)) +
      (∑ t ∈ Finset.Ico (adaptiveStart i) T,
        adaptiveLoss (adaptiveRate i/2) (adaptiveScale (adaptiveRate i/2) (a t) *
          (r t - a t))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro t _
    rw [show 2 * adaptiveRate i = 4 * (adaptiveRate i/2) by ring]
    exact adaptiveScalarBridge hθ hθ' (r t) (a t)
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith only [h]
  have hscale : 0 ≤ M / adaptiveRate i := div_nonneg hM he.le
  have hmix' : 256*M*Real.log 2 / adaptiveRate i ≤ 256*(M / adaptiveRate i) := by
    rw [show 256*M*Real.log 2 / adaptiveRate i = (256*(M / adaptiveRate i))*Real.log 2 by ring]
    exact mul_le_of_le_one_right (by positivity) hlog
  have hconst : (7/3) * M ≤ (7/24) * (M / adaptiveRate i) := by
    have hm := mul_le_mul_of_nonneg_left he' hscale
    rw [div_mul_cancel₀ _ he.ne'] at hm
    linarith only [hm]
  rw [← Finset.sum_range_add_sum_Ico _ hstart.le]
  have hD : M / (8 * adaptiveRate i) = (1/8) * (M / adaptiveRate i) := by ring
  have hC : 2 * (C₀ + 256*M) / adaptiveRate i =
      2*C₀ / adaptiveRate i + 512*(M / adaptiveRate i) := by ring
  rw [hD] at hdormant
  rw [hC]
  linarith only [hdormant, hbridge, hmix, hbase, hmix', hconst, hscale]

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature


theorem adaptiveEta_pos {M : ℝ} (hM : 0 < M) (i : ℕ) : 0 < adaptiveEta M i :=
  div_pos (adaptiveRate_pos i) (by positivity)

theorem binaryLeftWeight_pos (η x y : ℝ) : 0 < binaryLeftWeight η x y := by
  unfold binaryLeftWeight
  positivity

theorem binaryLeftWeight_lt_one (η x y : ℝ) : binaryLeftWeight η x y < 1 := by
  unfold binaryLeftWeight
  exact (div_lt_one (by positivity)).mpr (lt_add_of_pos_right _ (Real.exp_pos _))

theorem binaryMean_mono {q x y x' y' : ℝ} (hq : q ∈ Set.Icc 0 1)
    (hx : x ≤ x') (hy : y ≤ y') : binaryMean q x y ≤ binaryMean q x' y' :=
  add_le_add (mul_le_mul_of_nonneg_left hx hq.1)
    (mul_le_mul_of_nonneg_left hy (sub_nonneg.mpr hq.2))

@[simp] theorem binaryMean_same (q a : ℝ) : binaryMean q a a = a := by
  unfold binaryMean
  ring

private theorem binaryMean_exp_pos {η q x y : ℝ} (hq : q ∈ Set.Icc 0 1) :
    0 < binaryMean q (Real.exp (-η*x)) (Real.exp (-η*y)) := by
  unfold binaryMean
  by_cases hq0 : q = 0
  · simpa [hq0] using Real.exp_pos (-η*y)
  · exact add_pos_of_pos_of_nonneg
      (mul_pos (lt_of_le_of_ne hq.1 (Ne.symm hq0)) (Real.exp_pos _))
      (mul_nonneg (sub_nonneg.mpr hq.2) (Real.exp_pos _).le)

theorem binaryMix_mono {η q x y x' y' : ℝ} (hη : 0 < η) (hq : q ∈ Set.Icc 0 1)
    (hx : x ≤ x') (hy : y ≤ y') : binaryMix η q x y ≤ binaryMix η q x' y' := by
  have hExp (a b : ℝ) (hab : a ≤ b) : Real.exp (-η*b) ≤ Real.exp (-η*a) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hab (neg_nonpos.mpr hη.le))
  have hmean := binaryMean_mono hq (hExp _ _ hx) (hExp _ _ hy)
  have hlog := Real.log_le_log (binaryMean_exp_pos hq) hmean
  exact div_le_div_of_nonneg_right (neg_le_neg hlog) hη.le

theorem binaryMix_translate {η q : ℝ} (hη : 0 < η) (hq : q ∈ Set.Icc 0 1)
    (x y c : ℝ) : binaryMix η q (x+c) (y+c) = binaryMix η q x y + c := by
  have hfact (a : ℝ) : Real.exp (-η*(a+c)) = Real.exp (-η*a) * Real.exp (-η*c) := by
    rw [mul_add, Real.exp_add]
  have hm : binaryMean q (Real.exp (-η*x) * Real.exp (-η*c))
      (Real.exp (-η*y) * Real.exp (-η*c)) =
    binaryMean q (Real.exp (-η*x)) (Real.exp (-η*y)) * Real.exp (-η*c) := by
    unfold binaryMean
    ring
  unfold binaryMix
  rw [hfact, hfact, hm, Real.log_mul (binaryMean_exp_pos hq).ne' (Real.exp_pos _).ne',
    Real.log_exp]
  field_simp
  ring

@[simp] theorem binaryMix_same {η : ℝ} (hη : 0 < η) (q x : ℝ) : binaryMix η q x x = x := by
  unfold binaryMix
  rw [binaryMean_same, Real.log_exp]
  field_simp

theorem binaryMix_left_le {η : ℝ} (hη : 0 < η) (x y : ℝ) :
    binaryMix η (1/2) x y ≤ x + Real.log 2 / η := by
  have hmean : Real.exp (-η*x) / 2 ≤ binaryMean (1/2) (Real.exp (-η*x))
      (Real.exp (-η*y)) := by
    unfold binaryMean
    linarith only [Real.exp_pos (-η*y)]
  have hlog := Real.log_le_log (by positivity : 0 < Real.exp (-η*x) / 2) hmean
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at hlog
  unfold binaryMix
  apply (div_le_iff₀ hη).mpr
  have he : (x + Real.log 2 / η)*η = x*η + Real.log 2 := by
    rw [add_mul, div_mul_cancel₀ _ hη.ne']
  rw [he]
  linarith only [hlog]

theorem binaryMix_right_le {η : ℝ} (hη : 0 < η) (x y : ℝ) :
    binaryMix η (1/2) x y ≤ y + Real.log 2 / η := by
  have hsym : binaryMix η (1/2) x y = binaryMix η (1/2) y x := by
    unfold binaryMix
    have hmean (a b : ℝ) : binaryMean (1/2) a b = binaryMean (1/2) b a := by
      unfold binaryMean
      ring
    rw [hmean]
  rw [hsym]
  exact binaryMix_left_le hη y x

theorem binaryMix_increment (η x y v w : ℝ) :
    binaryMix η (1/2) (x+v) (y+w) - binaryMix η (1/2) x y =
      binaryMix η (binaryLeftWeight η x y) v w := by
  let X := Real.exp (-η*x)
  let Y := Real.exp (-η*y)
  let V := Real.exp (-η*v)
  let W := Real.exp (-η*w)
  have hsum : 0 < X+Y := by dsimp [X,Y]; positivity
  have hnew : 0 < (X*V+Y*W)/2 := by dsimp [X,Y,V,W]; positivity
  have hold : 0 < (X+Y)/2 := by positivity
  have hq : 1 - X/(X+Y) = Y/(X+Y) := by
    field_simp [hsum.ne']
    ring
  change -Real.log (binaryMean (1/2) (Real.exp (-η*(x+v)))
      (Real.exp (-η*(y+w))))/η -
      -Real.log (binaryMean (1/2) X Y)/η =
      -Real.log (binaryMean (X/(X+Y)) V W)/η
  rw [mul_add, mul_add, Real.exp_add, Real.exp_add]
  change -Real.log (binaryMean (1/2) (X*V) (Y*W))/η -
    -Real.log (binaryMean (1/2) X Y)/η = -Real.log (binaryMean (X/(X+Y)) V W)/η
  have hratio : binaryMean (X/(X+Y)) V W = ((X*V+Y*W)/2) / ((X+Y)/2) := by
    unfold binaryMean
    rw [hq]
    field_simp [hsum.ne']
  have havg (a b : ℝ) : binaryMean (1/2) a b = (a+b)/2 := by unfold binaryMean; ring
  rw [havg, havg, hratio, Real.log_div hnew.ne' hold.ne']
  ring


theorem adaptiveExactMean_mono (M : ℝ) (L v w : ℕ → ℝ) (k n : ℕ)
    (h : ∀ i, v i ≤ w i) : adaptiveExactMean M L v k n ≤ adaptiveExactMean M L w k n := by
  induction n generalizing k with
  | zero => exact h k
  | succ n ih =>
    simp only [adaptiveExactMean]
    exact binaryMean_mono ⟨(binaryLeftWeight_pos ..).le, (binaryLeftWeight_lt_one ..).le⟩
      (h k) (ih (k+1))

theorem adaptiveExactMean_const (M : ℝ) (L : ℕ → ℝ) (c : ℝ) (k n : ℕ) :
    adaptiveExactMean M L (fun _ => c) k n = c := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => rw [adaptiveExactMean, ih, binaryMean_same]

theorem adaptivePotential_mono {M : ℝ} (hM : 0 < M) (L L' : ℕ → ℝ) (k n : ℕ)
    (h : ∀ i, L i ≤ L' i) : adaptivePotential M L k n ≤ adaptivePotential M L' k n := by
  induction n generalizing k with
  | zero => exact h k
  | succ n ih =>
    simp only [adaptivePotential]
    exact binaryMix_mono (adaptiveEta_pos hM k) (by constructor <;> norm_num) (h k) (ih (k+1))

theorem adaptivePotential_translate {M : ℝ} (hM : 0 < M) (L : ℕ → ℝ) (c : ℝ) (k n : ℕ) :
    adaptivePotential M (fun i => L i + c) k n = adaptivePotential M L k n + c := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    rw [adaptivePotential, adaptivePotential, ih]
    exact binaryMix_translate (adaptiveEta_pos hM k) (by constructor <;> norm_num) _ _ c

theorem adaptivePotential_shift_abs {M b : ℝ} (hM : 0 < M) (L v : ℕ → ℝ) (k n : ℕ)
    (hv : ∀ i, |v i| ≤ b) :
    |adaptivePotential M (fun i => L i + v i) k n - adaptivePotential M L k n| ≤ b := by
  have hlow := adaptivePotential_mono hM (fun i => L i - b) (fun i => L i + v i) k n
    (fun i => by linarith only [(abs_le.mp (hv i)).1])
  have hupp := adaptivePotential_mono hM (fun i => L i + v i) (fun i => L i + b) k n
    (fun i => by linarith only [(abs_le.mp (hv i)).2])
  simp only [sub_eq_add_neg, adaptivePotential_translate hM] at hlow hupp
  exact abs_le.mpr ⟨by linarith only [hlow], by linarith only [hupp]⟩

theorem adaptivePotential_path {M : ℝ} (hM : 0 < M) (L : ℕ → ℝ) (k n i : ℕ) (hi : i ≤ n) :
    adaptivePotential M L k n - L (k+i) ≤
      (Real.log 2) * (2 / adaptiveEta M (k+i) - 1 / adaptiveEta M k) := by
  induction n generalizing k i with
  | zero =>
    have hi' : i = 0 := by omega
    subst i
    simp only [adaptivePotential, add_zero, sub_self, ← sub_div, show (2:ℝ)-1=1 by norm_num]
    exact mul_nonneg (Real.log_nonneg (by norm_num)) (by have := adaptiveEta_pos hM k; positivity)
  | succ n ih =>
    have he := adaptiveEta_pos hM k
    cases i with
    | zero =>
      simp only [adaptivePotential, add_zero, ← sub_div, show (2:ℝ)-1=1 by norm_num]
      have h := binaryMix_left_le he (L k) (adaptivePotential M L (k+1) n)
      simp only [div_eq_mul_inv, one_mul] at h ⊢
      linarith only [h]
    | succ i =>
      have hS := binaryMix_right_le he (L k) (adaptivePotential M L (k+1) n)
      have hI := ih (k+1) i (by omega)
      have hshift : k + (i+1) = (k+1) + i := by omega
      have hsplit : 1 / adaptiveEta M (k+1) = 2 / adaptiveEta M k := by
        unfold adaptiveEta
        rw [adaptiveRate_succ]
        ring
      rw [hsplit, ← hshift] at hI
      simp only [adaptivePotential]
      simp only [div_eq_mul_inv, one_mul] at hS hI ⊢
      linarith only [hS, hI]


theorem adaptivePotential_congr (M : ℝ) (L L' : ℕ → ℝ) (k n : ℕ)
    (h : ∀ i, k ≤ i → i ≤ k+n → L i = L' i) :
    adaptivePotential M L k n = adaptivePotential M L' k n := by
  induction n generalizing k with
  | zero => exact h k (by omega) (by omega)
  | succ n ih =>
    have ht := ih (k+1) (fun i hlo hhi => h i (by omega) (by omega))
    simp only [adaptivePotential, ht, h k le_rfl (by omega)]

theorem adaptiveExactMean_congr (M : ℝ) (L L' v v' : ℕ → ℝ) (k n : ℕ)
    (hL : ∀ i, k ≤ i → i ≤ k+n → L i = L' i)
    (hv : ∀ i, k ≤ i → i ≤ k+n → v i = v' i) :
    adaptiveExactMean M L v k n = adaptiveExactMean M L' v' k n := by
  induction n generalizing k with
  | zero => exact hv k (by omega) (by omega)
  | succ n ih =>
    have hL' i (hlo : k+1 ≤ i) (hhi : i ≤ (k+1)+n) := hL i (by omega) (by omega)
    have hv' i (hlo : k+1 ≤ i) (hhi : i ≤ (k+1)+n) := hv i (by omega) (by omega)
    have ht := ih (k+1) hL' hv'
    simp only [adaptiveExactMean, ht, adaptivePotential_congr M L L' (k+1) n hL',
      hL k le_rfl (by omega), hv k le_rfl (by omega)]

theorem adaptivePotential_extend_zero {M : ℝ} (hM : 0 < M) (L : ℕ → ℝ) (k n : ℕ)
    (h : ∀ i ≥ k+n, L i = 0) (m : ℕ) :
    adaptivePotential M L k (n+m) = adaptivePotential M L k n := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [← ih]
    clear ih
    have h' : ∀ i ≥ k+(n+m), L i = 0 := fun i hi => h i (by omega)
    clear h
    change adaptivePotential M L k ((n+m)+1) = adaptivePotential M L k (n+m)
    generalize hm : n+m = j at h' ⊢
    clear hm n m
    induction j generalizing k with
    | zero =>
      simp only [adaptivePotential]
      rw [h' k (by omega), h' (k+1) (by omega)]
      exact binaryMix_same (adaptiveEta_pos hM k) _ _
    | succ j ih =>
      have ht := ih (k+1) (fun i hi => h' i (by omega))
      change binaryMix (adaptiveEta M k) (1/2) (L k)
          (adaptivePotential M L (k+1) (j+1)) =
        binaryMix (adaptiveEta M k) (1/2) (L k) (adaptivePotential M L (k+1) j)
      rw [ht]


private theorem adaptiveExactMean_add (M : ℝ) (L v w : ℕ → ℝ) (k n : ℕ) :
    adaptiveExactMean M L (fun i => v i + w i) k n =
      adaptiveExactMean M L v k n + adaptiveExactMean M L w k n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [adaptiveExactMean, ih, binaryMean]
    ring

private theorem adaptiveExactMean_mul (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) (c : ℝ) :
    adaptiveExactMean M L (fun i => c * v i) k n =
      c * adaptiveExactMean M L v k n := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [adaptiveExactMean, ih, binaryMean]
    ring

private theorem adaptiveExactMean_sum (M : ℝ) (L : ℕ → ℝ) (k n : ℕ)
    {α : Type*} (s : Finset α) (f : α → ℕ → ℝ) :
    adaptiveExactMean M L (fun i => ∑ a ∈ s, f a i) k n =
      ∑ a ∈ s, adaptiveExactMean M L (f a) k n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [adaptiveExactMean_const]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha, adaptiveExactMean_add, ih]


theorem adaptiveExactMean_weighted_sum (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) :
    adaptiveExactMean M L v k n =
      ∑ j ∈ Finset.Icc k (k+n), adaptiveProbability M L k n j * v j := by
  have hv (i : ℕ) (hlo : k ≤ i) (hhi : i ≤ k+n) :
      v i = ∑ j ∈ Finset.Icc k (k+n), v j * (if i=j then (1:ℝ) else 0) := by
    classical
    simp only [mul_ite, mul_zero, mul_one]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [hji.symm]
    · intro h
      exact (h (Finset.mem_Icc.mpr ⟨hlo,hhi⟩)).elim
  rw [adaptiveExactMean_congr M L L v _ k n (by simp) hv, adaptiveExactMean_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [adaptiveExactMean_mul]
  exact mul_comm _ _


end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

/-- The two-loss exponential mix error is bounded by the weighted variance. -/
theorem binaryMix_gap {η q x y B : ℝ} (hη : 0 < η) (hq : q ∈ Set.Icc 0 1)
    (hx : |x| ≤ B) (hy : |y| ≤ B) (hsmall : 2*η*B ≤ 1) :
    binaryMean q x y - binaryMix η q x y ∈ Set.Icc 0 (η*q*(1-q)*(x-y)^2) := by
  let μ := binaryMean q x y
  let a := -η*(x-μ)
  let b := -η*(y-μ)
  let Z := binaryMean q (Real.exp a) (Real.exp b)
  have hq' : 0 ≤ 1-q := sub_nonneg.mpr hq.2
  have hx' : x-μ = (1-q)*(x-y) := by dsimp [μ, binaryMean]; ring
  have hy' : y-μ = -q*(x-y) := by dsimp [μ, binaryMean]; ring
  have hxy : |x-y| ≤ 2*B := by
    have h := abs_sub x y
    linarith only [h, hx, hy]
  have ha : |a| ≤ 1 := by
    rw [show a = -η * ((1-q)*(x-y)) by dsimp only [a]; rw [hx'], abs_mul, abs_mul, abs_neg,
      abs_of_pos hη, abs_of_nonneg hq']
    have h := mul_le_mul_of_nonneg_right (show 1-q ≤ 1 by linarith only [hq.1]) (abs_nonneg (x-y))
    have hh := mul_le_mul_of_nonneg_left ((by simpa only [one_mul] using h :
      (1-q)*|x-y| ≤ |x-y|).trans hxy) hη.le
    linarith only [hh, hsmall]
  have hb : |b| ≤ 1 := by
    rw [show b = -η * (-q*(x-y)) by dsimp only [b]; rw [hy'], abs_mul, abs_mul, abs_neg, abs_neg,
      abs_of_pos hη, abs_of_nonneg hq.1]
    have h := mul_le_mul_of_nonneg_right hq.2 (abs_nonneg (x-y))
    have hh := mul_le_mul_of_nonneg_left ((by simpa only [one_mul] using h :
      q*|x-y| ≤ |x-y|).trans hxy) hη.le
    linarith only [hh, hsmall]
  have hlin : q*a+(1-q)*b = 0 := by dsimp [a,b,μ,binaryMean]; ring
  have hsq : q*a^2+(1-q)*b^2 = η^2*q*(1-q)*(x-y)^2 := by
    dsimp only [a,b]
    rw [hx', hy']
    ring
  have hlo : 1 ≤ Z := by
    have h := binaryMean_mono hq (Real.add_one_le_exp a) (Real.add_one_le_exp b)
    change binaryMean q (a+1) (b+1) ≤ Z at h
    unfold binaryMean at h
    linarith only [h, hlin]
  have hup : Z ≤ 1 + η^2*q*(1-q)*(x-y)^2 := by
    have h₁ : Real.exp a ≤ a+1+a^2 := by
      linarith only [(le_abs_self (Real.exp a-1-a)).trans (Real.abs_exp_sub_one_sub_id_le ha)]
    have h₂ : Real.exp b ≤ b+1+b^2 := by
      linarith only [(le_abs_self (Real.exp b-1-b)).trans (Real.abs_exp_sub_one_sub_id_le hb)]
    have h := binaryMean_mono hq h₁ h₂
    change Z ≤ binaryMean q _ _ at h
    unfold binaryMean at h
    linarith only [h, hsq, hlin]
  have hcenter : μ - binaryMix η q x y = Real.log Z / η := by
    have ht := binaryMix_translate hη hq x y (-μ)
    simp only [← sub_eq_add_neg] at ht
    change -Real.log Z / η = binaryMix η q x y - μ at ht
    rw [neg_div] at ht
    linarith only [ht]
  change μ - binaryMix η q x y ∈ _
  rw [hcenter]
  constructor
  · exact div_nonneg (Real.log_nonneg hlo) hη.le
  · apply (div_le_iff₀ hη).mpr
    have hlog := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hlo)
    linarith only [hlog, hup]

def adaptiveIncrement (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) : ℝ :=
  adaptivePotential M (fun j => L j + v j) k n - adaptivePotential M L k n

def adaptiveMixError (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) : ℝ :=
  adaptiveExactMean M L v k n - adaptiveIncrement M L v k n

def adaptiveWeightedVariance (M : ℝ) (L v : ℕ → ℝ) (k : ℕ) : ℕ → ℝ
  | 0 => 0
  | n+1 =>
    let p := binaryLeftWeight (adaptiveEta M k) (L k) (adaptivePotential M L (k+1) n)
    let m := adaptiveExactMean M L v (k+1) n
    adaptiveRate k * (p*(1-p)*(v k-m)^2) + (1-p)*adaptiveWeightedVariance M L v (k+1) n

private theorem adaptiveExactMean_abs (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) (B : ℝ)
    (hv : ∀ i, |v i| ≤ B) : |adaptiveExactMean M L v k n| ≤ B := by
  have hl := adaptiveExactMean_mono M L (fun _ => -B) v k n (fun i => (abs_le.mp (hv i)).1)
  have hh := adaptiveExactMean_mono M L v (fun _ => B) k n (fun i => (abs_le.mp (hv i)).2)
  rw [adaptiveExactMean_const] at hl hh
  exact abs_le.mpr ⟨hl, hh⟩

private theorem adaptiveIncrement_succ (M : ℝ) (L v : ℕ → ℝ) (k n : ℕ) :
    let p := binaryLeftWeight (adaptiveEta M k) (L k) (adaptivePotential M L (k+1) n)
    adaptiveIncrement M L v k (n+1) =
      binaryMix (adaptiveEta M k) p (v k) (adaptiveIncrement M L v (k+1) n) := by
  dsimp only [adaptiveIncrement, adaptivePotential]
  rw [← binaryMix_increment]
  simp

theorem adaptiveWeightedVariance_le {M : ℝ} (hM : 0 < M) (L v : ℕ → ℝ)
    (hv : ∀ i, |v i| ≤ 2*M) (k n : ℕ) :
    let m := adaptiveExactMean M L v k n
    let J := adaptiveExactMean M L (fun j => adaptiveRate j * |v j|) k n
    adaptiveWeightedVariance M L v k n ≤
      4*M*J + 2*M*adaptiveRate k*|m| - adaptiveRate k*m^2 := by
  have hsq (y : ℝ) (hy : |y| ≤ 2*M) : y^2 ≤ 2*M*|y| := by
    simpa only [← sq, sq_abs] using mul_le_mul_of_nonneg_right hy (abs_nonneg y)
  induction n generalizing k with
  | zero =>
    change 0 ≤ 4*M*(adaptiveRate k*|v k|) + 2*M*adaptiveRate k*|v k| - adaptiveRate k*(v k)^2
    have he := adaptiveRate_pos k
    have h := mul_le_mul_of_nonneg_left (hsq _ (hv k)) he.le
    have hp : 0 ≤ 4*M*(adaptiveRate k*|v k|) := by positivity
    linarith only [h,hp]
  | succ n ih =>
    let p := binaryLeftWeight (adaptiveEta M k) (L k) (adaptivePotential M L (k+1) n)
    let x := v k
    let m := adaptiveExactMean M L v (k+1) n
    let μ := binaryMean p x m
    let J := adaptiveExactMean M L (fun j => adaptiveRate j * |v j|) (k+1) n
    let S := adaptiveWeightedVariance M L v (k+1) n
    let ε := adaptiveRate k
    have hp : 0 ≤ p := (binaryLeftWeight_pos ..).le
    have hp' : 0 ≤ 1-p := sub_nonneg.mpr (binaryLeftWeight_lt_one ..).le
    have he : 0 ≤ ε := (adaptiveRate_pos k).le
    have hm := adaptiveExactMean_abs M L v (k+1) n (2*M) hv
    have hm' : (1-p)*|m| ≤ |μ|+p*|x| := by
      have heq : (1-p)*m = μ - p*x := by dsimp [μ,binaryMean]; ring
      have h := abs_sub μ (p*x)
      rwa [← heq, abs_mul (1-p), abs_mul p, abs_of_nonneg hp', abs_of_nonneg hp] at h
    have hchild : S ≤ 4*M*J + 2*M*(ε/2)*|m| - (ε/2)*m^2 := by
      simpa only [adaptiveRate_succ k] using ih (k+1)
    have hvar : p*(1-p)*(x-m)^2 = p*x^2 + (1-p)*m^2 - μ^2 := by
      dsimp [μ, binaryMean]
      ring
    change ε * (p*(1-p)*(x-m)^2) + (1-p)*S ≤
      4*M*(p*(ε*|x|)+(1-p)*J) + 2*M*ε*|μ| - ε*μ^2
    rw [hvar]
    have hx := mul_le_mul_of_nonneg_left (hsq x (hv k)) (mul_nonneg he hp)
    have hmSq := mul_le_mul_of_nonneg_left (hsq m hm) (mul_nonneg (show 0 ≤ ε/2 by positivity) hp')
    have htail := mul_le_mul_of_nonneg_left hm' (mul_nonneg (by positivity : 0 ≤ 2*M) he)
    have hI := mul_le_mul_of_nonneg_left hchild hp'
    linarith only [hx,hmSq,htail,hI]

theorem adaptiveMixError_bounds {M : ℝ} (hM : 0 < M) (L v : ℕ → ℝ)
    (hv : ∀ i, |v i| ≤ 2*M) (k n : ℕ) :
    let E := adaptiveMixError M L v k n
    0 ≤ E ∧ E ≤ 2 * adaptiveWeightedVariance M L v k n / (128*M) + 16*M*adaptiveEta M k*E := by
  induction n generalizing k with
  | zero =>
    simp only [adaptiveMixError, adaptiveExactMean, adaptiveIncrement, adaptivePotential,
      adaptiveWeightedVariance, add_sub_cancel_left, sub_self, mul_zero, zero_div, add_zero,
      le_refl, and_self]
  | succ n ih =>
    let p := binaryLeftWeight (adaptiveEta M k) (L k) (adaptivePotential M L (k+1) n)
    let x := v k
    let m := adaptiveExactMean M L v (k+1) n
    let u := adaptiveIncrement M L v (k+1) n
    let E₁ := adaptiveMixError M L v (k+1) n
    let μ := binaryMean p x m
    let E := adaptiveMixError M L v k (n+1)
    let b := binaryMean p x u - binaryMix (adaptiveEta M k) p x u
    let D := p*(1-p)*(x-m)^2
    let S := adaptiveWeightedVariance M L v (k+1) n
    let η := adaptiveEta M k
    have hp : 0 ≤ p := (binaryLeftWeight_pos ..).le
    have hp1 : p ≤ 1 := (binaryLeftWeight_lt_one ..).le
    have hp' : 0 ≤ 1-p := sub_nonneg.mpr hp1
    have hη : 0 < η := adaptiveEta_pos hM k
    have hsmall : 2*η*(2*M) ≤ 1 := by
      have heq : 2*η*(2*M) = adaptiveRate k / 32 := by
        dsimp [η,adaptiveEta]
        field_simp
        ring
      rw [heq]
      linarith only [adaptiveRate_le k]
    have hu := adaptivePotential_shift_abs hM L v (k+1) n hv
    have hm := adaptiveExactMean_abs M L v (k+1) n (2*M) hv
    change |u| ≤ 2*M at hu
    change |m| ≤ 2*M at hm
    have hb : b ∈ Set.Icc 0 (η*p*(1-p)*(x-u)^2) :=
      binaryMix_gap hη ⟨hp,hp1⟩ (hv k) hu hsmall
    obtain ⟨hE₁, hI⟩ := ih (k+1)
    change 0 ≤ E₁ at hE₁
    have hEta : adaptiveEta M (k+1) = η/2 := by simp [η, adaptiveEta, adaptiveRate_succ]; ring
    rw [hEta] at hI
    have hEsq : E₁^2 ≤ 4*M*E₁ := by
      have hE : E₁ ≤ 4*M := by
        change m-u ≤ 4*M
        linarith only [(abs_le.mp hm).2, (abs_le.mp hu).1]
      simpa only [← sq] using mul_le_mul_of_nonneg_right hE hE₁
    have hrec : E = (1-p)*E₁ + b := by
      dsimp only [E, adaptiveMixError]
      rw [adaptiveIncrement_succ]
      change binaryMean p x m - _ = (1-p)*(m-u) + b
      dsimp [b,binaryMean]
      ring
    have hEsub : (1-p)*E₁ ≤ E := by rw [hrec]; exact le_add_of_nonneg_right hb.1
    have hE : 0 ≤ E := (mul_nonneg hp' hE₁).trans hEsub
    have hdiff : (x-u)^2 ≤ 2*(x-m)^2+2*E₁^2 := by
      change (x-u)^2 ≤ 2*(x-m)^2+2*(m-u)^2
      nlinarith only [sq_nonneg ((x-m)-(m-u))]
    have hpη : 0 ≤ η*p*(1-p) := mul_nonneg (mul_nonneg hη.le hp) hp'
    have hbstep : b ≤ 2*η*D + 8*M*η*p*(1-p)*E₁ := by
      have hdiff' := mul_le_mul_of_nonneg_left hdiff hpη
      have hs' := mul_le_mul_of_nonneg_left hEsq (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hpη)
      dsimp only [D]
      linarith only [hb.2,hdiff',hs']
    have hD : 2*η*D = 2*(adaptiveRate k*D)/(128*M) := by dsimp [η,adaptiveEta]; ring
    have hchild := mul_le_mul_of_nonneg_left hI hp'
    have hptop := mul_le_mul_of_nonneg_right hp1
      (show 0 ≤ 8*M*η*((1-p)*E₁) by positivity)
    have hroot := mul_le_mul_of_nonneg_left hEsub (show 0 ≤ 16*M*η by positivity)
    change 0 ≤ E ∧ E ≤ 2 * (adaptiveRate k*D+(1-p)*S)/(128*M) + 16*M*η*E
    refine ⟨hE, ?_⟩
    dsimp only [adaptiveMixError] at hchild
    change (1-p)*E₁ ≤ (1-p)*(2*S/(128*M)+16*M*(η/2)*E₁) at hchild
    rw [hD] at hbstep
    simp only [div_eq_mul_inv] at hbstep hchild ⊢
    linarith only [hrec,hbstep,hchild,hptop,hroot]


theorem abs_adaptiveUpdate_le (i : ℕ) (r : ℝ) : |adaptiveUpdate i r| ≤ 2*|r| := by
  have he := adaptiveRate_pos i
  have h := abs_sub r (adaptiveRate i/2*|r|)
  rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ adaptiveRate i/2), abs_abs] at h
  have hp := mul_le_mul_of_nonneg_right (show adaptiveRate i/2 ≤ 1 by
    linarith only [adaptiveRate_le i]) (abs_nonneg r)
  unfold adaptiveUpdate adaptiveLoss
  rw [abs_neg]
  linarith only [h,hp]

private theorem weightedMean_difference {s : Finset ℕ} {p q x : ℕ → ℝ} {δ B : ℝ}
    (hδ : (∑ i ∈ s, |p i-q i|) ≤ δ) (hB : 0 ≤ B) (hx : ∀ i ∈ s, |x i| ≤ B) :
    |(∑ i ∈ s, p i*x i) - ∑ i ∈ s, q i*x i| ≤ B*δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ s, |p i*x i-q i*x i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, B*|p i-q i| := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← sub_mul, abs_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hx i hi) (abs_nonneg _)
    _ ≤ B*δ := by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hδ hB

private theorem adaptiveMixError_variance_bound {M : ℝ} (hM : 0 < M) (L v : ℕ → ℝ)
    (hv : ∀ i, |v i| ≤ 2*M) (k n : ℕ) :
    let E := adaptiveMixError M L v k n
    let J := adaptiveExactMean M L (fun j => adaptiveRate j*|v j|) k n
    let m := adaptiveExactMean M L v k n
    E ≤ J/16 + adaptiveRate k*|m|/32 + E/64 := by
  let E := adaptiveMixError M L v k n
  let J := adaptiveExactMean M L (fun j => adaptiveRate j*|v j|) k n
  let m := adaptiveExactMean M L v k n
  obtain ⟨hE, he⟩ := adaptiveMixError_bounds hM L v hv k n
  have hV := adaptiveWeightedVariance_le hM L v hv k n
  have hweak : adaptiveWeightedVariance M L v k n ≤ 4*M*J + 2*M*adaptiveRate k*|m| :=
    hV.trans (sub_le_self _ (mul_nonneg (adaptiveRate_pos k).le (sq_nonneg _)))
  have hscale := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hweak (by norm_num : (0:ℝ) ≤ 2)) (by positivity : 0 ≤ 128*M)
  have hcoeff : 16*M*adaptiveEta M k = adaptiveRate k/8 := by
    unfold adaptiveEta
    field_simp
    ring
  rw [hcoeff] at he
  change 0 ≤ E at hE
  have hlast := mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_right (adaptiveRate_le k) (by norm_num : (0:ℝ) ≤ 8)) hE
  norm_num at hlast
  have hclean : 2*(4*M*J+2*M*adaptiveRate k*|m|)/(128*M) =
      J/16+adaptiveRate k*|m|/32 := by
    field_simp
    ring
  rw [hclean] at hscale
  change E ≤ _ at he
  change E ≤ J/16+adaptiveRate k*|m|/32+E/64
  linarith only [hlast, hscale, he]

/-- One round of the recursive mixture with a bounded approximation of the weights. -/
theorem adaptiveOneRoundGap {M δ : ℝ} (hM : 0 < M) (hδ : 0 ≤ δ) (L a approx : ℕ → ℝ)
    (k n : ℕ) (ha : ∀ i, |a i| ≤ M)
    (hp : ∀ i ∈ Finset.Icc k (k+n), 0 ≤ approx i)
    (hdist : (∑ i ∈ Finset.Icc k (k+n), |adaptiveProbability M L k n i - approx i|) ≤ δ)
    (hzero : (∑ i ∈ Finset.Icc k (k+n), approx i * a i) = 0) :
    let v := fun i => adaptiveUpdate i (a i)
    let U := ∑ i ∈ Finset.Icc k (k+n), approx i * (adaptiveRate i/2) * |a i|
    adaptiveMixError M L v k n ≤ (U+M*δ)/3 ∧
      (2/3)*U-(7/3)*M*δ ≤ adaptiveIncrement M L v k n := by
  let s := Finset.Icc k (k+n)
  let v := fun i => adaptiveUpdate i (a i)
  let U := ∑ i ∈ s, approx i * (adaptiveRate i/2) * |a i|
  let m := adaptiveExactMean M L v k n
  let J := adaptiveExactMean M L (fun j => adaptiveRate j*|v j|) k n
  let E := adaptiveMixError M L v k n
  have hv (i : ℕ) : |v i| ≤ 2*M := (abs_adaptiveUpdate_le i (a i)).trans
    (mul_le_mul_of_nonneg_left (ha i) (by norm_num))
  have hU : 0 ≤ U := Finset.sum_nonneg fun i hi =>
    mul_nonneg (mul_nonneg (hp i hi) (by have := adaptiveRate_pos i; positivity)) (abs_nonneg _)
  have hMδ := mul_nonneg hM.le hδ
  have hmean := weightedMean_difference hdist (by positivity : 0 ≤ 2*M) (fun i _ => hv i)
  have hm' : (∑ i ∈ s, approx i*v i) = U := by
    change (∑ i ∈ s, approx i*a i) = 0 at hzero
    simp only [U, v, adaptiveUpdate, adaptiveLoss]
    simp only [neg_sub, mul_sub, Finset.sum_sub_distrib, hzero, sub_zero, mul_assoc]
  rw [hm', ← adaptiveExactMean_weighted_sum] at hmean
  change |m-U| ≤ 2*M*δ at hmean
  have hm : |m| ≤ U+2*M*δ := by
    have h := abs_add_le (m-U) U
    rw [sub_add_cancel, abs_of_nonneg hU] at h
    linarith only [h,hmean]
  have hjexp : (∑ i ∈ s, approx i * (adaptiveRate i*|v i|)) ≤ 4*U := by
    dsimp only [U]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have h := mul_le_mul_of_nonneg_left (abs_adaptiveUpdate_le i (a i))
      (mul_nonneg (hp i hi) (adaptiveRate_pos i).le)
    change (approx i*adaptiveRate i)*|v i| ≤ _ at h
    linarith only [h]
  have hjpt (i : ℕ) : |adaptiveRate i * (|v i|)| ≤ 2*M := by
    rw [abs_of_nonneg (mul_nonneg (adaptiveRate_pos i).le (abs_nonneg _))]
    exact (mul_le_of_le_one_left (abs_nonneg _) ((adaptiveRate_le i).trans (by norm_num))).trans (hv i)
  have hjabs := weightedMean_difference hdist (by positivity : 0 ≤ 2*M) (fun i _ => hjpt i)
  rw [← adaptiveExactMean_weighted_sum] at hjabs
  change |J - ∑ i ∈ s, approx i * (adaptiveRate i*|v i|)| ≤ 2*M*δ at hjabs
  have hj : J ≤ 4*U+2*M*δ := by
    linarith only [hjexp,(abs_le.mp hjabs).2]
  have heabs := adaptiveMixError_variance_bound hM L v hv k n
  have hcoef := mul_le_mul_of_nonneg_right (adaptiveRate_le k) (abs_nonneg m)
  change E ≤ J/16+adaptiveRate k*|m|/32+E/64 at heabs
  have he : E ≤ (U+M*δ)/3 := by
    linarith only [heabs, hm, hj, hcoef, hU, hMδ]
  refine ⟨he, ?_⟩
  change (2/3)*U-(7/3)*M*δ ≤ adaptiveIncrement M L v k n
  have hEq : adaptiveIncrement M L v k n = m-E := by
    dsimp only [m,E,adaptiveMixError]
    ring
  rw [hEq]
  linarith only [(abs_le.mp hmean).1, he]

end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}


theorem adaptiveAwake_iff (i t : ℕ) : i ≤ adaptiveAwake t ↔ adaptiveStart i ≤ t := by
  rw [adaptiveAwake, Nat.le_log_iff_pow_le (by decide) (Nat.succ_ne_zero t)]
  unfold adaptiveStart
  have := Nat.one_le_two_pow (n := i)
  omega

theorem adaptiveAwake_mono : Monotone adaptiveAwake := by
  intro t T ht
  exact (adaptiveAwake_iff _ _).mpr (((adaptiveAwake_iff _ _).mp le_rfl).trans ht)


namespace AdaptiveBase
variable (B : AdaptiveBase K) (hcv : Convex ℝ K) {M : ℝ} (P : AdaptiveWeightRule M)


def adaptiveMixCredit (G : ℝ) (s : AdaptiveRunState d) (t : ℕ) (g : Vec d) : ℝ :=
  ∑ i ∈ Finset.Icc 0 (0+(adaptiveAwake t+1)),
    P.prob s.loss t i * (adaptiveRate i/2) * |B.adaptiveDifference hcv P G s t g i|

theorem adaptiveMixCredit_nonneg (G : ℝ) (s : AdaptiveRunState d) (t : ℕ) (g : Vec d) :
    0 ≤ B.adaptiveMixCredit hcv P G s t g := by
  unfold adaptiveMixCredit
  exact Finset.sum_nonneg fun i _ => mul_nonneg
    (mul_nonneg (P.nonnegative s.loss t i) (by have := adaptiveRate_pos i; positivity)) (abs_nonneg _)


section Run
variable (G : ℝ) (g : ℕ → Vec d)

local notation "s" => B.adaptiveStateAfter hcv P G g
local notation "a" => B.adaptiveDifference hcv P G
local notation "w" => B.adaptiveRoundPlay hcv P G
local notation "b" => B.adaptiveBasePlay G

theorem adaptiveStateAfter_feedback_prefix (i j : ℕ) {t T : ℕ} (ht : t ≤ T) (hj : j < t) :
    (s T).feedback i j = (s t).feedback i j := by
  induction T with
  | zero => omega
  | succ T ih =>
    by_cases h : t=T+1
    · simp [h]
    · have ht' : t ≤ T := by omega
      simp only [adaptiveStateAfter, adaptiveStep, if_neg (show ¬(i ≤ adaptiveAwake T ∧ j=T)
        by omega)]
      exact ih ht'

theorem adaptiveStateAfter_feedback_norm (hG : 0 ≤ G) (hg : ∀ t, norm₂ (g t) ≤ G)
    (i j T : ℕ) : norm₂ ((s T).feedback i j) ≤ 2*G := by
  induction T with
  | zero => simpa [adaptiveStateAfter,norm₂] using (show (0:ℝ) ≤ 2*G by positivity)
  | succ T ih =>
    simp only [adaptiveStateAfter,adaptiveStep]
    split
    · exact adaptiveScaledInput_norm (g T) (hg T) i _
    · exact ih

theorem adaptiveStateAfter_feedback_current (i t T : ℕ) (ht : t < T) (hi : i ≤ adaptiveAwake t) :
    (s T).feedback i t = adaptiveScale (adaptiveRate i/2) (a (s t) t (g t) i) • g t := by
  rw [B.adaptiveStateAfter_feedback_prefix hcv P G g i t (show t+1 ≤ T by omega)
    (Nat.lt_succ_self t)]
  simp [adaptiveStateAfter,adaptiveStep,hi]

theorem adaptiveStateAfter_loss_dormant (i t : ℕ) (ht : t ≤ adaptiveStart i) :
    (s t).loss i = 0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have hi : ¬i ≤ adaptiveAwake t := fun h => by
      have hlo := (adaptiveAwake_iff i t).mp h
      omega
    simp [adaptiveStateAfter,adaptiveStep, adaptiveDifference, hi, adaptiveUpdate, adaptiveLoss,
      ih (by omega)]

theorem adaptiveStateAfter_loss_eq (i T : ℕ) :
    (s T).loss i = ∑ t ∈ Finset.range T, adaptiveUpdate i (a (s t) t (g t) i) := by
  induction T with
  | zero => simp [adaptiveStateAfter]
  | succ T ih => simp only [adaptiveStateAfter,adaptiveStep,Finset.sum_range_succ,ih]

theorem adaptiveBasePlay_terminal (i t T : ℕ) (ht : t ≤ T) :
    b (s t) t i =
      B.play (2*G) (adaptiveRate i)
        (fun j => (s T).feedback i (j+adaptiveStart i)) (t-adaptiveStart i) := by
  apply B.play_prefix
  intro j hj
  exact (B.adaptiveStateAfter_feedback_prefix hcv P G g i _ ht (by omega)).symm

theorem adaptiveDifference_zero_mean (σ : AdaptiveRunState d) (t : ℕ) (input : Vec d) :
    (∑ i ∈ Finset.Icc 0 (0+(adaptiveAwake t+1)),
      P.prob σ.loss t i *
        a σ t input i) = 0 := by
  have hIcc : Finset.Icc 0 (0+(adaptiveAwake t+1)) = Finset.range (adaptiveAwake t+2) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hIcc, show adaptiveAwake t + 2 = (adaptiveAwake t + 1) + 1 by omega,
    Finset.sum_range_succ]
  rw [show a σ t input (adaptiveAwake t+1) = 0 by simp [adaptiveDifference], mul_zero, add_zero]
  let p := P.prob σ.loss t
  let r := adaptiveWeight P σ.loss t
  have hp (i : ℕ) : p i = adaptiveAwakeMass P σ.loss t * r i := by
    have hmass : 0 < adaptiveAwakeMass P σ.loss t := P.awake_positive σ.loss t
    change p i = adaptiveAwakeMass P σ.loss t * (p i / adaptiveAwakeMass P σ.loss t)
    rw [mul_comm, div_mul_cancel₀ _ hmass.ne']
  change (∑ i ∈ Finset.range (adaptiveAwake t+1), p i * a σ t input i) = 0
  simp_rw [hp, mul_assoc]
  rw [← Finset.mul_sum]
  suffices h : (∑ i ∈ Finset.range (adaptiveAwake t+1), r i * a σ t input i) = 0 by rw [h,mul_zero]
  have hcalc : ∀ i ∈ Finset.range (adaptiveAwake t+1), a σ t input i =
      dotProduct input (w σ t).val - dotProduct input (b σ t i).val := by
    intro i hi
    have hi' : i ≤ adaptiveAwake t := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
    simp only [adaptiveDifference, if_pos hi', excess, dotProduct_sub]
  rw [Finset.sum_congr rfl (fun i hi => congrArg (fun y => r i*y) (hcalc i hi))]
  have hweights : (∑ i ∈ Finset.range (adaptiveAwake t+1), r i) = 1 :=
    adaptiveWeight_sum P σ.loss t
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hweights, one_mul]
  change dotProduct input (w σ t).val -
    (∑ i ∈ Finset.range (adaptiveAwake t+1), r i * dotProduct input (b σ t i).val) = 0
  have hsum : (∑ i ∈ Finset.range (adaptiveAwake t+1), r i * dotProduct input (b σ t i).val) =
      dotProduct input (w σ t).val := by
    change _ = dotProduct input (∑ i ∈ Finset.range (adaptiveAwake t+1), r i • (b σ t i).val)
    rw [dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
  rw [hsum, sub_self]

end Run
end AdaptiveBase
end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}

private theorem adaptiveExcess_abs (g x y : Vec d) :
    |excess g x y| ≤ norm₂ g * norm₂ (x-y) := by
  have hn : norm₂ (-g) = norm₂ g := by simp [norm₂, neg_dotProduct, dotProduct_neg]
  refine abs_le.mpr ⟨?_, dotProduct_le_norm₂_mul g (x-y)⟩
  have h := dotProduct_le_norm₂_mul (-g) (x-y)
  rw [neg_dotProduct, hn] at h
  change - (norm₂ g*norm₂ (x-y)) ≤ dotProduct g (x-y)
  linarith only [h]

private theorem adaptivePotential_zero {M : ℝ} (hM : 0 < M) (k n : ℕ) :
    adaptivePotential M (fun _ => 0) k n = 0 := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [adaptivePotential, ih, binaryMix_same (adaptiveEta_pos hM k)]

private theorem adaptiveTolerance_sum_le (T : ℕ) :
    (∑ t ∈ Finset.range T, adaptiveMixTolerance t) ≤ 1 := by
  have h : ∀ n : ℕ, (∑ t ∈ Finset.range n, adaptiveMixTolerance t) ≤
      1 - 1 / ((n : ℝ)+1) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      have hp : adaptiveMixTolerance n ≤ 1 / ((n : ℝ)+1) - 1 / ((n : ℝ)+2) := by
        unfold adaptiveMixTolerance
        calc
          _ ≤ 1 / (((n : ℝ)+1)*((n : ℝ)+2)) := by
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            rw [pow_two]
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = _ := by field_simp; ring
      rw [Finset.sum_range_succ, Nat.cast_succ, show (n : ℝ)+1+1=(n:ℝ)+2 by ring]
      linarith only [ih, hp]
  exact (h T).trans (sub_le_self _ (by positivity))

namespace AdaptiveBase

variable (B : AdaptiveBase K) (hcv : Convex ℝ K) {M G : ℝ}
  (P : AdaptiveWeightRule M) (g : ℕ → Vec d)

local notation "s" => B.adaptiveStateAfter hcv P G g
local notation "a" => B.adaptiveDifference hcv P G
local notation "w" => B.adaptiveRoundPlay hcv P G
local notation "b" => B.adaptiveBasePlay G

private theorem adaptiveExcess_bound (hg : ∀ t, norm₂ (g t) ≤ G)
    (hspread : ∀ u v : K, G * norm₂ (u.val-v.val) ≤ M) (t : ℕ) (u v : K) :
    |excess (g t) u.val v.val| ≤ M :=
  (adaptiveExcess_abs ..).trans ((mul_le_mul_of_nonneg_right (hg t) (norm₂_nonneg _)).trans
    (hspread u v))

theorem adaptiveRoot_bound (hM : 0 < M) (hg : ∀ t, norm₂ (g t) ≤ G)
    (hspread : ∀ u v : K, G * norm₂ (u.val-v.val) ≤ M) (T n : ℕ)
    (hdepth : ∀ t < T, adaptiveAwake t+1 ≤ n) :
    (2/3)*(∑ t ∈ Finset.range T, B.adaptiveMixCredit hcv P G (s t) t (g t)) -
      (7/3)*M*(∑ t ∈ Finset.range T, adaptiveMixTolerance t) ≤
      adaptivePotential M (s T).loss 0 n := by
  induction T with
  | zero =>
    change _ ≤ adaptivePotential M (fun _ => 0) 0 n
    simp [adaptivePotential_zero hM]
  | succ T ih =>
    have hprev := ih fun t ht => hdepth t (by omega)
    let localDepth := adaptiveAwake T+1
    let L := (s T).loss
    let L' := (s (T+1)).loss
    let Δ := fun i => adaptiveUpdate i (a (s T) T (g T) i)
    let p := P.prob L T
    have hdiff (j i : ℕ) : |a (s j) j (g j) i| ≤ M := by
      unfold adaptiveDifference
      split
      · exact adaptiveExcess_bound g hg hspread j _ _
      · simpa only [abs_zero] using hM.le
    have hLrange (i : ℕ) : |L i| ≤ 2*M*T := by
      change |(s T).loss i| ≤ _
      rw [B.adaptiveStateAfter_loss_eq hcv P G g i T]
      calc
        _ ≤ ∑ j ∈ Finset.range T, |adaptiveUpdate i (a (s j) j (g j) i)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _ ∈ Finset.range T, 2*M := Finset.sum_le_sum fun j _ =>
          (abs_adaptiveUpdate_le i _).trans (mul_le_mul_of_nonneg_left (hdiff j i) (by norm_num))
        _ = _ := by simp [mul_comm]
    have hdormant (i : ℕ) (hi : i ≥ localDepth) : T+1 ≤ adaptiveStart i := by
      have hi' : ¬i ≤ adaptiveAwake T := by dsimp [localDepth] at hi; omega
      have : ¬adaptiveStart i ≤ T := fun h => hi' ((adaptiveAwake_iff i T).mpr h)
      omega
    have hL (i : ℕ) (hi : i ≥ 0+localDepth) : L i = 0 :=
      B.adaptiveStateAfter_loss_dormant hcv P G g i T (by
        have := hdormant i (by omega)
        omega)
    have hround := adaptiveOneRoundGap hM (show 0 ≤ adaptiveMixTolerance T by
      unfold adaptiveMixTolerance; positivity) L (a (s T) T (g T)) p
      0 localDepth (hdiff T) (fun i _ => P.nonnegative L T i)
      (P.approximation L T hLrange (hL localDepth (by omega))) (B.adaptiveDifference_zero_mean hcv P G (s T) T (g T))
    have hstep : (2/3)*B.adaptiveMixCredit hcv P G (s T) T (g T) -
        (7/3)*M*adaptiveMixTolerance T ≤ adaptiveIncrement M L Δ 0 localDepth :=
      hround.2
    have hL' (i : ℕ) (hi : i ≥ 0+localDepth) : L' i = 0 :=
      B.adaptiveStateAfter_loss_dormant hcv P G g i (T+1) (hdormant i (by omega))
    have hn : localDepth + (n-localDepth) = n :=
      Nat.add_sub_of_le (hdepth T (by omega))
    have hb := adaptivePotential_extend_zero hM L 0 localDepth hL (n-localDepth)
    have ha := adaptivePotential_extend_zero hM L' 0 localDepth hL' (n-localDepth)
    rw [hn] at ha hb
    change _ ≤ adaptivePotential M L' 0 n
    change _ ≤ adaptivePotential M L 0 n at hprev
    change _ ≤ adaptivePotential M L' 0 localDepth - adaptivePotential M L 0 localDepth at hstep
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith only [ha,hb,hprev,hstep]

theorem adaptiveAwake_mix_comparison (hM : 0 < M) (hg : ∀ t, norm₂ (g t) ≤ G)
    (hspread : ∀ u v : K, G * norm₂ (u.val-v.val) ≤ M) (T i : ℕ) (hT : 2^i ≤ T) :
    (∑ t ∈ Finset.Ico (adaptiveStart i) T, adaptiveLoss (adaptiveRate i/2) (a (s t) t (g t) i)) ≤
      256*M*Real.log 2 / adaptiveRate i +(7/3)*M := by
  have hstart := (adaptiveStart_lt_iff i T).mpr hT
  let n := adaptiveAwake (T-1)+1
  have hn : i ≤ n := by
    have hi : adaptiveStart i ≤ T-1 := by omega
    exact ((adaptiveAwake_iff i (T-1)).mpr hi).trans (Nat.le_succ _)
  have hroot := B.adaptiveRoot_bound hcv P g hM hg hspread T n
    (fun t ht => Nat.succ_le_succ (adaptiveAwake_mono (by omega)))
  have hbudget := adaptiveTolerance_sum_le T
  have hU : 0 ≤ (2/3) * (∑ t ∈ Finset.range T, B.adaptiveMixCredit hcv P G (s t) t (g t)) :=
    mul_nonneg (by norm_num) (Finset.sum_nonneg fun t _ =>
      B.adaptiveMixCredit_nonneg hcv P G (s t) t (g t))
  have hneg := mul_le_of_le_one_right (show 0 ≤ (7/3:ℝ)*M by positivity) hbudget
  have hpath := adaptivePotential_path hM (s T).loss 0 n i hn
  rw [Nat.zero_add] at hpath
  have hpenalty :
      Real.log 2 * (2/adaptiveEta M i - 1/adaptiveEta M 0) ≤
        256*M*Real.log 2 / adaptiveRate i := calc
    _ ≤ Real.log 2 * (2/adaptiveEta M i) :=
      mul_le_mul_of_nonneg_left
        (sub_le_self _ (div_nonneg (by norm_num) (adaptiveEta_pos hM 0).le))
        (Real.log_nonneg (by norm_num))
    _ = _ := by
      unfold adaptiveEta
      field_simp
      ring
  have hbefore : (∑ t ∈ Finset.range (adaptiveStart i),
      adaptiveLoss (adaptiveRate i/2) (a (s t) t (g t) i)) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have hi : ¬i ≤ adaptiveAwake t := fun h =>
      (Nat.not_le_of_gt (Finset.mem_range.mp ht)) ((adaptiveAwake_iff i t).mp h)
    simp [adaptiveDifference, hi, adaptiveLoss]
  have hsum := B.adaptiveStateAfter_loss_eq hcv P G g i T
  simp only [adaptiveUpdate, Finset.sum_neg_distrib] at hsum
  rw [Finset.sum_Ico_eq_sub _ hstart.le, hbefore, sub_zero]
  linarith only [hpath,hpenalty,hroot,hneg,hsum,hU]

theorem adaptiveAwake_base_comparison (hG : 0 < G) (hg : ∀ t, norm₂ (g t) ≤ G)
    (T i : ℕ) (u : K) :
    let r := fun t => excess (g t) (w (s t) t).val u.val
    (∑ t ∈ Finset.Ico (adaptiveStart i) T,
      adaptiveLoss (adaptiveRate i/2)
        (adaptiveScale (adaptiveRate i/2) (a (s t) t (g t) i) * (r t-a (s t) t (g t) i))) ≤
          G * B.cost / adaptiveRate i := by
  let input := fun j => (s T).feedback i (j+adaptiveStart i)
  have hinput : ∀ j, norm₂ (input j) ≤ 2*G :=
    fun j => B.adaptiveStateAfter_feedback_norm hcv P G g hG.le hg i _ _
  have hlearner := B.playedRegret (show 0 < 2*G by positivity)
    (adaptiveRate_pos i) ((adaptiveRate_le i).trans (by norm_num)) input hinput u (T-adaptiveStart i)
  let r := fun t => excess (g t) (w (s t) t).val u.val
  let rbase := fun j => excess (input j) (B.play (2*G) (adaptiveRate i) input j).val u.val
  have hconvert : ∀ t ∈ Finset.Ico (adaptiveStart i) T,
      adaptiveScale (adaptiveRate i/2) (a (s t) t (g t) i) * (r t-a (s t) t (g t) i) =
        rbase (t-adaptiveStart i) := by
    intro t ht
    obtain ⟨hlo, hupp⟩ := Finset.mem_Ico.mp ht
    have hawake := (adaptiveAwake_iff i t).mpr hlo
    have hf := B.adaptiveStateAfter_feedback_current hcv P G g i t T hupp hawake
    have hbase := B.adaptiveBasePlay_terminal hcv P G g i t T hupp.le
    have hinput' : input (t-adaptiveStart i) =
        adaptiveScale (adaptiveRate i/2) (a (s t) t (g t) i) • g t := by
      simpa only [input, Nat.sub_add_cancel hlo] using hf
    have hdiff : r t-a (s t) t (g t) i = excess (g t) (b (s t) t i).val u.val := by
      simp only [r,adaptiveDifference,if_pos hawake,excess,dotProduct_sub]
      ring
    dsimp only [rbase]
    rw [hinput', ← hbase, hdiff, excess, excess, smul_dotProduct, smul_eq_mul]
  change (∑ t ∈ Finset.Ico (adaptiveStart i) T, adaptiveLoss (adaptiveRate i/2) _) ≤ _
  calc
    _ = ∑ t ∈ Finset.Ico (adaptiveStart i) T, adaptiveLoss (adaptiveRate i/2) (rbase (t-adaptiveStart i)) :=
      Finset.sum_congr rfl fun t ht => congrArg (adaptiveLoss (adaptiveRate i/2)) (hconvert t ht)
    _ = ∑ j ∈ Finset.range (T-adaptiveStart i), adaptiveLoss (adaptiveRate i/2) (rbase j) := by
      rw [Finset.sum_Ico_eq_sum_range]
      simp
    _ ≤ _ := by
      change 2*(∑ j ∈ Finset.range (T-adaptiveStart i), rbase j) -
        adaptiveRate i*(∑ j ∈ Finset.range (T-adaptiveStart i), |rbase j|) ≤ _ at hlearner
      simp only [adaptiveLoss, Finset.sum_sub_distrib, ← Finset.mul_sum, div_eq_mul_inv] at hlearner ⊢
      linarith only [hlearner]

/-- Linearized regret for the recursive mixture with the specified weight tolerance. -/
theorem adaptiveMixture (hM : 0 < M) (hG : 0 < G) (hg : ∀ t, norm₂ (g t) ≤ G)
    (hspread : ∀ u v : K, G * norm₂ (u.val-v.val) ≤ M) (T : ℕ) (hT : 0 < T) (u : K) :
    let r := fun t => excess (g t) (B.adaptivePlay hcv P G g t).val u.val
    let C := G*B.cost + 257*M
    (∑ t ∈ Finset.range T, r t) ≤ 24*(C+Real.sqrt (C * adaptiveNegative T r)) := by
  let r := fun t => excess (g t) (w (s t) t).val u.val
  let C₀ := G*B.cost+M
  let C := G*B.cost+257*M
  have hGC := mul_nonneg hG.le B.cost_nonneg
  have hC : 0 < C := by dsimp only [C]; positivity
  have hMC : M ≤ C := by dsimp only [C]; linarith only [hGC,hM]
  have hr (t : ℕ) : |r t| ≤ M :=
    adaptiveExcess_bound g hg hspread t _ u
  change (∑ t ∈ Finset.range T, r t) ≤ 24*(C+Real.sqrt (C*adaptiveNegative T r))
  apply adaptiveRegret_of_masterRatewise hC hMC hT (adaptiveNegative_nonneg T r)
    (adaptiveNegative_le M hM.le T r fun t _ => hr t)
  intro i hi
  apply masterRatewise_of_signed hC.le
  have hmix := B.adaptiveAwake_mix_comparison hcv P g hM hg hspread T i hi
  have hbase := B.adaptiveAwake_base_comparison hcv P g hG hg T i u
  have hbase' := hbase.trans (show G*B.cost / adaptiveRate i ≤
      2*C₀ / adaptiveRate i from div_le_div_of_nonneg_right
      (by dsimp only [C₀]; linarith only [hGC,hM]) (adaptiveRate_pos i).le)
  have h := adaptiveMasterSigned_of_awake T i hi M C₀ hM.le r
    (fun t => a (s t) t (g t) i) (fun t _ => (le_abs_self _).trans (hr t)) hmix hbase'
  exact h.trans_eq (by dsimp [C,C₀]; ring)

end AdaptiveBase
end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature

variable {d : ℕ} {K : Set (Vec d)}


theorem adaptiveWidthConstant_pos : 0 < adaptiveWidthConstant := by
  unfold adaptiveWidthConstant adaptiveBaseWidthFactor
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- The known-width linearized regret bound for any certified initialization. -/
theorem adaptiveWidth_givenBase (B : AdaptiveBase K) (hc : IsCompact K) (hcv : Convex ℝ K)
    (hcost : B.cost ≤ adaptiveBaseWidthFactor*coordinateWidth K) {G W : ℝ} (hG : 0 < G) (hW : 0 < W)
    (hwidth : coordinateWidth K ≤ W) (P : AdaptiveWeightRule (adaptiveWidthScale G W))
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G) (T : ℕ) (hT : 0 < T) (u : K) :
    let r := fun t => excess (g t) (B.adaptivePlay hcv P G g t).val u.val
    (∑ t ∈ Finset.range T, r t) ≤
      adaptiveWidthConstant * (G*W + Real.sqrt (G*W*adaptiveNegative T r)) := by
  let M := adaptiveWidthScale G W
  let r := fun t => excess (g t) (B.adaptivePlay hcv P G g t).val u.val
  let C := G*B.cost+257*M
  let n := adaptiveNegative T r
  let κ := adaptiveBaseWidthFactor + 514 / Real.log 2
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hM : 0 < M := by dsimp [M,adaptiveWidthScale]; positivity
  have hspread (x y : K) : G*norm₂ (x.val-y.val) ≤ M := calc
    _ ≤ G*(2*coordinateWidth K / Real.log 2) :=
      mul_le_mul_of_nonneg_left (coordinateWidth_pair hc x y) hG.le
    _ ≤ G*(2*W / Real.log 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hwidth (by norm_num)) hlog.le) hG.le
    _ = _ := by dsimp [M,adaptiveWidthScale]; ring
  have hm := B.adaptiveMixture hcv P g hM hG hg hspread T hT u
  change (∑ t ∈ Finset.range T, r t) ≤ 24*(C+Real.sqrt (C*n)) at hm
  have hC : C ≤ κ*(G*W) := calc
    _ ≤ G*(adaptiveBaseWidthFactor*W)+257*M := add_le_add
      (mul_le_mul_of_nonneg_left (hcost.trans
        (mul_le_mul_of_nonneg_left hwidth (by norm_num [adaptiveBaseWidthFactor]))) hG.le) le_rfl
    _ = _ := by dsimp [M,adaptiveWidthScale,κ]; ring
  have hn := adaptiveNegative_nonneg T r
  have hκ : 1 ≤ κ := by
    dsimp [κ,adaptiveBaseWidthFactor]
    have h := div_nonneg (by norm_num : (0:ℝ) ≤ 514) hlog.le
    linarith only [h]
  have hκ' : Real.sqrt κ ≤ κ := by
    apply (Real.sqrt_le_left (zero_le_one.trans hκ)).mpr
    simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hκ (zero_le_one.trans hκ)
  have hroot : Real.sqrt (C*n) ≤ κ*Real.sqrt (G*W*n) := calc
    _ ≤ Real.sqrt ((κ*(G*W))*n) := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hC hn)
    _ = Real.sqrt κ * Real.sqrt (G*W*n) := by
      rw [mul_assoc, Real.sqrt_mul (zero_le_one.trans hκ), mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_right hκ' (Real.sqrt_nonneg _)
  change (∑ t ∈ Finset.range T, r t) ≤ (24*κ)*(G*W+Real.sqrt (G*W*n))
  linarith only [hm,hC,hroot]

theorem adaptiveWidth_convex_givenBase (B : AdaptiveBase K) (hc : IsCompact K) (hcv : Convex ℝ K)
    (hcost : B.cost ≤ adaptiveBaseWidthFactor*coordinateWidth K) {G W : ℝ} (hG : 0 < G) (hW : 0 < W)
    (hwidth : coordinateWidth K ≤ W) (P : AdaptiveWeightRule (adaptiveWidthScale G W))
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G) (T : ℕ) (hT : 0 < T) (u : K)
    (f : ℕ → Vec d → ℝ) (hcont : ∀ t < T, ContinuousOn (f t) K)
    (hsub : ∀ t < T, ∀ v ∈ K, f t (B.adaptivePlay hcv P G g t).val - f t v ≤
      excess (g t) (B.adaptivePlay hcv P G g t).val v) :
    let w := fun t => (B.adaptivePlay hcv P G g t).val
    let r := fun t => excess (g t) (w t) u.val
    let n := adaptiveNegative T r
    let Δ := ∑ t ∈ Finset.range T, (f t u.val - sInf (f t '' K))
    (∑ t ∈ Finset.range T, (f t (w t) - f t u.val)) ≤ (∑ t ∈ Finset.range T, r t) ∧
      (∑ t ∈ Finset.range T, r t) ≤ adaptiveWidthConstant*(G*W+Real.sqrt (G*W*n)) ∧
      adaptiveWidthConstant*(G*W+Real.sqrt (G*W*n)) ≤
        adaptiveWidthConstant*(G*W+Real.sqrt (G*W*Δ)) := by
  let w := fun t => (B.adaptivePlay hcv P G g t).val
  have htransfer := adaptiveConvexTransfer hc T w g f u.val u.prop
    (fun t _ => (B.adaptivePlay hcv P G g t).prop) hcont hsub
  refine ⟨htransfer.1, adaptiveWidth_givenBase B hc hcv hcost hG hW hwidth P g hg T hT u, ?_⟩
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left htransfer.2 (mul_nonneg hG.le hW.le))))
    adaptiveWidthConstant_pos.le


end Curvature
end
end

section
set_option autoImplicit false
noncomputable section
namespace Curvature
variable {d : ℕ} {K : Set (Vec d)}


namespace DomainInitialization


theorem adaptiveBase_cost (I : DomainInitialization K) (hne : K.Nonempty) (hc : IsCompact K)
    (hcv : Convex ℝ K) : (I.adaptiveBase hne hc hcv).cost ≤ 393216*coordinateWidth K := by
  cases I with
  | dyadic D h => change 192*D.representationCost ≤ _; linarith
  | fixed center A ha hq hq' hgram hbody mode =>
    change 164*coordinateWidth K ≤ _
    have h := (AdaptiveBase.fixedAxes hne hc hcv center A ha hq hq' hgram hbody mode).cost_nonneg
    change 0 ≤ 164*coordinateWidth K at h
    linarith

end DomainInitialization


end Curvature
end
end

set_option autoImplicit false
noncomputable section
open Curvature
variable {d : ℕ} {K : Set (Vec d)}

theorem solution (init : DomainInitialization K) (hc : IsCompact K)
    (hcv : Convex ℝ K) (hne : K.Nonempty) {G W : ℝ} (hG : 0 < G) (hW : 0 < W)
    (hwidth : coordinateWidth K ≤ W) (P : AdaptiveWeightRule (adaptiveWidthScale G W))
    (g : ℕ → Vec d) (hg : ∀ t, norm₂ (g t) ≤ G) (T : ℕ) (hT : 0 < T) (u : K) :
    let w := (init.adaptiveBase hne hc hcv).adaptivePlay hcv P G g
    let r := fun t => excess (g t) (w t).val u.val
    let n := adaptiveNegative T r
    let rhs := adaptiveWidthConstant*(G*W+Real.sqrt (G*W*n))
    (∑ t ∈ Finset.range T, r t) ≤ rhs ∧
      ∀ (f : ℕ → Vec d → ℝ), (∀ t < T, ContinuousOn (f t) K) →
        (∀ t < T, ∀ v ∈ K, f t (w t).val - f t v ≤ excess (g t) (w t).val v) →
        let Δ := ∑ t ∈ Finset.range T, (f t u.val - sInf (f t '' K))
        (∑ t ∈ Finset.range T, (f t (w t).val - f t u.val)) ≤ (∑ t ∈ Finset.range T, r t) ∧
          rhs ≤ adaptiveWidthConstant*(G*W+Real.sqrt (G*W*Δ)) := by
  let B := init.adaptiveBase hne hc hcv
  have hcost : B.cost ≤ _ := init.adaptiveBase_cost hne hc hcv
  refine ⟨adaptiveWidth_givenBase B hc hcv hcost hG hW hwidth P g hg T hT u, ?_⟩
  intro f hcont hsub
  obtain ⟨hreg, _, hshift⟩ := adaptiveWidth_convex_givenBase B hc hcv hcost hG hW hwidth P g hg
    T hT u f hcont hsub
  exact ⟨hreg, hshift⟩
