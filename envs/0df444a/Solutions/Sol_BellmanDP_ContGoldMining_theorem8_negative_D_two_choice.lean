-- Prove2me | solution 1 for BellmanDP.ContGoldMining.theorem8_negative_D_two_choice
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:05:14.868147+00:00
-- url     : https://prove2.me/submissions/62a51e83-32e2-4431-b91c-b5ba47a6f830

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process
import Definitions.Def_BellmanDP_ContGoldMining_Switching



namespace BellmanDP.ContGoldMining

open MeasureTheory Set Filter Topology

noncomputable def cgmΦ (φ₁ : ℝ → ℝ) (t : ℝ) : ℝ := ∫ s in (0:ℝ)..t, φ₁ s

lemma cgm_ii {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) (a b : ℝ) :
    IntervalIntegrable φ₁ volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (1:ℝ)) intervalIntegrable_const
    h.1.aestronglyMeasurable (ae_of_all _ (fun t => ?_))
  have := h.2 t
  show ‖φ₁ t‖ ≤ 1
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [this.1], this.2⟩

lemma cgm_cum0 (φ₁ : ℝ → ℝ) (t : ℝ) : cumTime (twoChoice φ₁) 0 t = cgmΦ φ₁ t := by
  simp [cumTime, twoChoice, cgmΦ]

lemma cgm_cum1 {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) (t : ℝ) :
    cumTime (twoChoice φ₁) 1 t = t - cgmΦ φ₁ t := by
  simp only [cumTime, twoChoice, cgmΦ, Matrix.cons_val_one, Matrix.cons_val_zero]
  rw [intervalIntegral.integral_sub intervalIntegrable_const (cgm_ii h 0 t)]
  simp

lemma cgm_cum2 (φ₁ : ℝ → ℝ) (t : ℝ) : cumTime (twoChoice φ₁) 2 t = 0 := by
  simp [cumTime, twoChoice]

lemma cgm_stateX {q₁ q₂ r₁ r₂ x₀ : ℝ} {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) (t : ℝ) :
    stateX (Params.two q₁ q₂ r₁ r₂) x₀ (twoChoice φ₁) t =
      x₀ * Real.exp (-(r₁ * cgmΦ φ₁ t)) := by
  simp only [stateX, Fin.sum_univ_three, cgm_cum0, cgm_cum1 h, cgm_cum2, Params.a, Params.two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring_nf

lemma cgm_stateY {q₁ q₂ r₁ r₂ y₀ : ℝ} {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) (t : ℝ) :
    stateY (Params.two q₁ q₂ r₁ r₂) y₀ (twoChoice φ₁) t =
      y₀ * Real.exp (-(r₂ * (t - cgmΦ φ₁ t))) := by
  simp only [stateY, Fin.sum_univ_three, cgm_cum0, cgm_cum1 h, cgm_cum2, Params.b, Params.two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring_nf

lemma cgm_rate {q₁ q₂ r₁ r₂ x₀ y₀ : ℝ} {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) (t : ℝ) :
    goldRate (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ₁) t =
      Real.exp (-(q₁ * cgmΦ φ₁ t + q₂ * (t - cgmΦ φ₁ t))) *
        (φ₁ t * (r₁ * (x₀ * Real.exp (-(r₁ * cgmΦ φ₁ t)))) +
          (1 - φ₁ t) * (r₂ * (y₀ * Real.exp (-(r₂ * (t - cgmΦ φ₁ t)))))) := by
  rw [goldRate, cgm_stateX h, cgm_stateY h]
  simp only [survival, Fin.sum_univ_three, cgm_cum0, cgm_cum1 h, cgm_cum2, Params.q, Params.a,
    Params.b, Params.two, twoChoice,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring_nf

lemma cgm_Φ_zero (φ₁ : ℝ → ℝ) : cgmΦ φ₁ 0 = 0 := by simp [cgmΦ]

lemma cgm_Φ_sub {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) (s t : ℝ) :
    cgmΦ φ₁ t - cgmΦ φ₁ s = ∫ x in s..t, φ₁ x :=
  intervalIntegral.integral_interval_sub_left (cgm_ii h 0 t) (cgm_ii h 0 s)

lemma cgm_Φ_bounds {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) {s t : ℝ} (hst : s ≤ t) :
    0 ≤ cgmΦ φ₁ t - cgmΦ φ₁ s ∧ cgmΦ φ₁ t - cgmΦ φ₁ s ≤ t - s := by
  rw [cgm_Φ_sub h]
  constructor
  · exact intervalIntegral.integral_nonneg hst (fun x _ => (h.2 x).1)
  · have := intervalIntegral.integral_mono_on hst (cgm_ii h s t)
      (intervalIntegrable_const (c := (1:ℝ))) (fun x _ => (h.2 x).2)
    simpa using this

lemma cgm_Φ_abs {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) (s t : ℝ) :
    |cgmΦ φ₁ t - cgmΦ φ₁ s| ≤ |t - s| := by
  rcases le_total s t with hst | hst
  · have := cgm_Φ_bounds h hst
    rw [abs_of_nonneg this.1, abs_of_nonneg (by linarith)]; exact this.2
  · have := cgm_Φ_bounds h hst
    rw [abs_sub_comm, abs_of_nonneg this.1, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact this.2

lemma cgm_Φ_lip {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) : LipschitzWith 1 (cgmΦ φ₁) :=
  LipschitzWith.of_dist_le_mul fun s t => by
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]; exact cgm_Φ_abs h t s

lemma cgm_Φ_nonneg {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ cgmΦ φ₁ t ∧ cgmΦ φ₁ t ≤ t := by
  have := cgm_Φ_bounds h ht
  rw [cgm_Φ_zero] at this; constructor <;> linarith [this.1, this.2]

noncomputable def cgmQ (q₁ q₂ : ℝ) (φ₁ : ℝ → ℝ) (t : ℝ) : ℝ :=
  q₁ * cgmΦ φ₁ t + q₂ * (t - cgmΦ φ₁ t)

lemma cgm_Q_mono {q₁ q₂ : ℝ} (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁)
    {s t : ℝ} (hst : s ≤ t) : min q₁ q₂ * (t - s) ≤ cgmQ q₁ q₂ φ₁ t - cgmQ q₁ q₂ φ₁ s := by
  have hb := cgm_Φ_bounds h hst
  have h1 := min_le_left q₁ q₂
  have h2 := min_le_right q₁ q₂
  unfold cgmQ
  nlinarith [mul_le_mul_of_nonneg_right h1 hb.1,
    mul_le_mul_of_nonneg_right h2 (show 0 ≤ (t - s) - (cgmΦ φ₁ t - cgmΦ φ₁ s) by linarith)]

lemma cgm_Q_abs {q₁ q₂ : ℝ} (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁)
    (s t : ℝ) : |cgmQ q₁ q₂ φ₁ t - cgmQ q₁ q₂ φ₁ s| ≤ (q₁ + 2 * q₂) * |t - s| := by
  have hb := cgm_Φ_abs h s t
  have : cgmQ q₁ q₂ φ₁ t - cgmQ q₁ q₂ φ₁ s =
      q₁ * (cgmΦ φ₁ t - cgmΦ φ₁ s) + q₂ * ((t - s) - (cgmΦ φ₁ t - cgmΦ φ₁ s)) := by
    unfold cgmQ; ring
  rw [this]
  calc _ ≤ |q₁ * (cgmΦ φ₁ t - cgmΦ φ₁ s)| + |q₂ * ((t - s) - (cgmΦ φ₁ t - cgmΦ φ₁ s))| :=
        abs_add_le _ _
    _ ≤ q₁ * |t - s| + q₂ * (|t - s| + |t - s|) := by
        rw [abs_mul, abs_mul, abs_of_nonneg hq₁, abs_of_nonneg hq₂]
        gcongr
        exact (abs_sub _ _).trans (by gcongr)
    _ = _ := by ring

noncomputable def cgmH (r₁ r₂ x₀ y₀ u v : ℝ) : ℝ :=
  x₀ * (1 - Real.exp (-(r₁ * u))) + y₀ * (1 - Real.exp (-(r₂ * v)))

noncomputable def cgmΨ (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (φ₁ m : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(q₁ * cgmΦ φ₁ t + q₂ * (t - cgmΦ φ₁ t))) *
      cgmH r₁ r₂ x₀ y₀ (cgmΦ φ₁ t) (t - cgmΦ φ₁ t)
    + ∫ σ in (0:ℝ)..(q₁ * cgmΦ φ₁ t + q₂ * (t - cgmΦ φ₁ t)), m σ

lemma cgm_Ψ_zero (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (φ₁ m : ℝ → ℝ) :
    cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m 0 = 0 := by
  simp [cgmΨ, cgm_Φ_zero, cgmH]

lemma cgm_potential (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) {φ₁ m : ℝ → ℝ}
    (h : TwoAdmissible φ₁) (hm : Continuous m) (B : ℝ) (hB : ∀ s, |m s| ≤ B) (T : ℝ)
    (hT : 0 ≤ T) :
    IntervalIntegrable (deriv (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m)) volume 0 T ∧
    ∫ t in (0:ℝ)..T, deriv (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) t = cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m T ∧
    ∀ᵐ t, t ∈ Ioo 0 T → deriv (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) t =
      goldRate (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ₁) t +
        (q₁ * φ₁ t + q₂ * (1 - φ₁ t)) *
          (m (cgmQ q₁ q₂ φ₁ t) - Real.exp (-(cgmQ q₁ q₂ φ₁ t)) *
            cgmH r₁ r₂ x₀ y₀ (cgmΦ φ₁ t) (t - cgmΦ φ₁ t)) := by
  -- absolute continuity
  set G : ℝ × ℝ → ℝ := fun p => Real.exp (-(q₁ * p.1 + q₂ * (p.2 - p.1))) *
      (x₀ * (1 - Real.exp (-(r₁ * p.1))) + y₀ * (1 - Real.exp (-(r₂ * (p.2 - p.1))))) with hGdef
  have hG : ContDiff ℝ 1 G := by rw [hGdef]; fun_prop
  obtain ⟨K₁, hK₁⟩ := (hG.contDiffOn (s := Icc ((0:ℝ), (0:ℝ)) (T, T))).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  have hp : LipschitzWith (max 1 1) (fun t => (cgmΦ φ₁ t, t)) :=
    (cgm_Φ_lip h).prodMk LipschitzWith.id
  have hmaps : MapsTo (fun t => (cgmΦ φ₁ t, t)) (uIcc 0 T) (Icc ((0:ℝ), (0:ℝ)) (T, T)) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    have := cgm_Φ_nonneg h ht.1
    exact ⟨Prod.mk_le_mk.2 ⟨this.1, ht.1⟩, Prod.mk_le_mk.2 ⟨by linarith [this.2, ht.2], ht.2⟩⟩
  have hL1 := hK₁.comp hp.lipschitzOnWith hmaps
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hL2 : LipschitzWith (Real.toNNReal (B * (q₁ + 2 * q₂)))
      (fun t => ∫ σ in (0:ℝ)..(cgmQ q₁ q₂ φ₁ t), m σ) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq, Real.dist_eq,
      intervalIntegral.integral_interval_sub_left (hm.intervalIntegrable _ _)
        (hm.intervalIntegrable _ _)]
    calc ‖∫ σ in cgmQ q₁ q₂ φ₁ t..cgmQ q₁ q₂ φ₁ s, m σ‖
        ≤ B * |cgmQ q₁ q₂ φ₁ s - cgmQ q₁ q₂ φ₁ t| :=
          intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hB x)
      _ ≤ B * ((q₁ + 2 * q₂) * |s - t|) := by gcongr; exact cgm_Q_abs hq₁ hq₂ h t s
      _ = _ := by ring
  have hAC : AbsolutelyContinuousOnInterval (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) 0 T :=
    hL1.absolutelyContinuousOnInterval.add hL2.lipschitzOnWith.absolutelyContinuousOnInterval
  refine ⟨hAC.intervalIntegrable_deriv, ?_, ?_⟩
  · rw [hAC.integral_deriv_eq_sub, cgm_Ψ_zero, sub_zero]
  · filter_upwards [(cgm_ii h 0 T).ae_hasDerivAt_integral] with t ht htI
    have htI' : t ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact Ioo_subset_Icc_self htI
    have hΦ : HasDerivAt (cgmΦ φ₁) (φ₁ t) t := ht htI' 0 left_mem_uIcc
    have hQ := (hΦ.const_mul q₁).add (((hasDerivAt_id' t).sub hΦ).const_mul q₂)
    have hE := hQ.neg.exp
    have hH := ((((hΦ.const_mul r₁).neg.exp).const_sub 1).const_mul x₀).add
      (((((hasDerivAt_id' t).sub hΦ).const_mul r₂).neg.exp.const_sub 1).const_mul y₀)
    have hF := (hm.integral_hasStrictDerivAt 0 (q₁ * cgmΦ φ₁ t + q₂ * (t - cgmΦ φ₁ t))).hasDerivAt
    have hT' := (hE.mul hH).add (hF.comp t hQ)
    rw [(show HasDerivAt (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) _ t from hT').deriv, cgm_rate h]
    simp only [cgmQ, cgmH, Function.comp, Pi.add_apply, Pi.neg_apply, Pi.sub_apply, Pi.mul_apply]
    ring

lemma cgm_kkt_ineq {q₁ q₂ r₁ r₂ x₀ y₀ u v u' v' : ℝ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hs : q₁ * u + q₂ * v = q₁ * u' + q₂ * v')
    (hk : q₂ * r₁ * (x₀ * Real.exp (-(r₁ * u'))) - q₁ * r₂ * (y₀ * Real.exp (-(r₂ * v'))) = 0 ∨
      (v' = 0 ∧ 0 ≤ q₂ * r₁ * (x₀ * Real.exp (-(r₁ * u'))) -
        q₁ * r₂ * (y₀ * Real.exp (-(r₂ * v'))))  ∨
      (u' = 0 ∧ q₂ * r₁ * (x₀ * Real.exp (-(r₁ * u'))) -
        q₁ * r₂ * (y₀ * Real.exp (-(r₂ * v'))) ≤ 0)) :
    cgmH r₁ r₂ x₀ y₀ u v ≤ cgmH r₁ r₂ x₀ y₀ u' v' := by
  set a := Real.exp (-(r₁ * u')) with ha
  set b := Real.exp (-(r₂ * v')) with hb
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := Real.exp_pos _
  have e1 : a * (1 - r₁ * (u - u')) ≤ Real.exp (-(r₁ * u)) := by
    have : Real.exp (-(r₁ * u)) = a * Real.exp (-(r₁ * (u - u'))) := by
      rw [ha, ← Real.exp_add]; ring_nf
    rw [this]
    have := Real.add_one_le_exp (-(r₁ * (u - u')))
    nlinarith
  have e2 : b * (1 - r₂ * (v - v')) ≤ Real.exp (-(r₂ * v)) := by
    have : Real.exp (-(r₂ * v)) = b * Real.exp (-(r₂ * (v - v'))) := by
      rw [hb, ← Real.exp_add]; ring_nf
    rw [this]
    have := Real.add_one_le_exp (-(r₂ * (v - v')))
    nlinarith
  have key : r₁ * x₀ * a * (u - u') + r₂ * y₀ * b * (v - v') ≤ 0 := by
    have hdu : q₁ * (u - u') = -(q₂ * (v - v')) := by linarith
    have iden : q₁ * q₂ * (r₁ * x₀ * a * (u - u') + r₂ * y₀ * b * (v - v')) =
        -(q₂ * (v - v')) * (q₂ * r₁ * (x₀ * a) - q₁ * r₂ * (y₀ * b)) := by
      have : q₁ * q₂ * (r₁ * x₀ * a * (u - u')) = q₂ * r₁ * x₀ * a * (q₁ * (u - u')) := by ring
      rw [mul_add, this, hdu]; ring
    have : q₁ * q₂ * (r₁ * x₀ * a * (u - u') + r₂ * y₀ * b * (v - v')) ≤ 0 := by
      rw [iden]
      rcases hk with hk | ⟨hv', hk⟩ | ⟨hu', hk⟩
      · rw [hk]; simp
      · rw [hv', sub_zero]; exact mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hk
      · have : -(q₂ * (v - v')) = q₁ * u := by rw [← hdu, hu', sub_zero]
        rw [this]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hk
    by_contra hc
    push_neg at hc
    have := mul_pos (mul_pos hq₁ hq₂) hc
    linarith
  unfold cgmH
  nlinarith [mul_le_mul_of_nonneg_left e1 hx₀, mul_le_mul_of_nonneg_left e2 hy₀]

noncomputable def cgmE (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (φ₁ : ℝ → ℝ) (s : ℝ) : ℝ :=
  q₂ * r₁ * (x₀ * Real.exp (-(r₁ * cgmΦ φ₁ s))) -
    q₁ * r₂ * (y₀ * Real.exp (-(r₂ * (s - cgmΦ φ₁ s))))

lemma cgm_E_cont (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) :
    Continuous (cgmE q₁ q₂ r₁ r₂ x₀ y₀ φ₁) := by
  have := (cgm_Φ_lip h).continuous
  unfold cgmE; fun_prop

lemma cgm_rule_ae {q₁ q₂ r₁ r₂ x₀ y₀ : ℝ} {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁)
    (hf : FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ₁) :
    ∀ᵐ s, 0 ≤ s → (0 < cgmE q₁ q₂ r₁ r₂ x₀ y₀ φ₁ s → φ₁ s = 1) ∧
      (cgmE q₁ q₂ r₁ r₂ x₀ y₀ φ₁ s < 0 → φ₁ s = 0) ∧
      (cgmE q₁ q₂ r₁ r₂ x₀ y₀ φ₁ s = 0 → φ₁ s = r₂ / (r₁ + r₂)) := by
  unfold FollowsIndexRule at hf
  rw [ae_restrict_iff' measurableSet_Ici] at hf
  filter_upwards [hf] with s hs hs0
  have := hs hs0
  simp only [cgm_stateX h, cgm_stateY h] at this
  unfold cgmE
  refine ⟨fun hE => this.1 (by linarith), fun hE => this.2.1 (by linarith),
    fun hE => this.2.2 (by linarith)⟩

lemma cgm_ae_const_interval {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) {a b c : ℝ} (hab : a ≤ b)
    (hc : ∀ᵐ s, s ∈ Ioo a b → φ₁ s = c) : cgmΦ φ₁ b - cgmΦ φ₁ a = c * (b - a) := by
  rw [cgm_Φ_sub h, show c * (b - a) = ∫ x in a..b, c by simp; ring]
  apply intervalIntegral.integral_congr_ae
  have hb : ∀ᵐ s : ℝ, s ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [hc, hb] with s hs hsb hs'
  rw [uIoc_of_le hab] at hs'
  exact hs ⟨hs'.1, lt_of_le_of_ne hs'.2 hsb⟩

lemma cgm_index_kkt {q₁ q₂ r₁ r₂ x₀ y₀ : ℝ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁)
    (hf : FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ₁) (t : ℝ) (ht : 0 ≤ t) :
    cgmE q₁ q₂ r₁ r₂ x₀ y₀ φ₁ t = 0 ∨
      (t - cgmΦ φ₁ t = 0 ∧ 0 ≤ cgmE q₁ q₂ r₁ r₂ x₀ y₀ φ₁ t) ∨
      (cgmΦ φ₁ t = 0 ∧ cgmE q₁ q₂ r₁ r₂ x₀ y₀ φ₁ t ≤ 0) := by
  set E := cgmE q₁ q₂ r₁ r₂ x₀ y₀ φ₁ with hEdef
  have hEc : Continuous E := cgm_E_cont q₁ q₂ r₁ r₂ x₀ y₀ h
  have hrule := cgm_rule_ae (h := h) hf
  -- positive case
  have pos_case : 0 < E t → t - cgmΦ φ₁ t = 0 := by
    intro hEt
    -- on an interval (a, t] where E > 0, φ₁ = 1
    have step : ∀ a, 0 ≤ a → a ≤ t → (∀ s ∈ Ioo a t, 0 < E s) →
        cgmΦ φ₁ t - cgmΦ φ₁ a = t - a := by
      intro a ha hat hpos
      have := cgm_ae_const_interval h hat (c := 1) (by
        filter_upwards [hrule] with s hs hsI
        exact (hs (by linarith [hsI.1])).1 (hpos s hsI))
      linarith
    set S := {s | s ∈ Icc 0 t ∧ E s ≤ 0} with hS
    by_cases hne : S.Nonempty
    · have hSc : IsClosed S := by
        have : S = Icc 0 t ∩ E ⁻¹' (Iic 0) := rfl
        rw [this]; exact isClosed_Icc.inter (isClosed_Iic.preimage hEc)
      have hbdd : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
      have hmem := hSc.csSup_mem hne hbdd
      set s₀ := sSup S
      have hpos : ∀ s ∈ Ioo s₀ t, 0 < E s := by
        intro s hs
        by_contra hc; push_neg at hc
        have : s ≤ s₀ := le_csSup hbdd ⟨⟨by linarith [hmem.1.1, hs.1], hs.2.le⟩, hc⟩
        linarith [hs.1]
      have hd := step s₀ hmem.1.1 hmem.1.2 hpos
      exfalso
      have hEle : E t ≤ E s₀ := by
        simp only [hEdef, cgmE]
        have h1 : t - cgmΦ φ₁ t = s₀ - cgmΦ φ₁ s₀ := by linarith
        rw [h1]
        have : Real.exp (-(r₁ * cgmΦ φ₁ t)) ≤ Real.exp (-(r₁ * cgmΦ φ₁ s₀)) := by
          apply Real.exp_le_exp.2; nlinarith [hmem.1.2]
        nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ q₂ * r₁ * x₀ by positivity)]
      linarith [hmem.2]
    · have hpos : ∀ s ∈ Ioo 0 t, 0 < E s := by
        intro s hs; by_contra hc; push_neg at hc
        exact hne ⟨s, ⟨hs.1.le, hs.2.le⟩, hc⟩
      have := step 0 le_rfl ht hpos
      rw [cgm_Φ_zero] at this; linarith
  have neg_case : E t < 0 → cgmΦ φ₁ t = 0 := by
    intro hEt
    have step : ∀ a, 0 ≤ a → a ≤ t → (∀ s ∈ Ioo a t, E s < 0) →
        cgmΦ φ₁ t - cgmΦ φ₁ a = 0 := by
      intro a ha hat hneg
      have := cgm_ae_const_interval h hat (c := 0) (by
        filter_upwards [hrule] with s hs hsI
        exact (hs (by linarith [hsI.1])).2.1 (hneg s hsI))
      linarith
    set S := {s | s ∈ Icc 0 t ∧ 0 ≤ E s} with hS
    by_cases hne : S.Nonempty
    · have hSc : IsClosed S := by
        have : S = Icc 0 t ∩ E ⁻¹' (Ici 0) := rfl
        rw [this]; exact isClosed_Icc.inter (isClosed_Ici.preimage hEc)
      have hbdd : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
      have hmem := hSc.csSup_mem hne hbdd
      set s₀ := sSup S
      have hneg : ∀ s ∈ Ioo s₀ t, E s < 0 := by
        intro s hs
        by_contra hc; push_neg at hc
        have : s ≤ s₀ := le_csSup hbdd ⟨⟨by linarith [hmem.1.1, hs.1], hs.2.le⟩, hc⟩
        linarith [hs.1]
      have hd := step s₀ hmem.1.1 hmem.1.2 hneg
      exfalso
      have hEle : E s₀ ≤ E t := by
        simp only [hEdef, cgmE]
        have h1 : cgmΦ φ₁ t = cgmΦ φ₁ s₀ := by linarith
        rw [h1]
        have : Real.exp (-(r₂ * (t - cgmΦ φ₁ s₀))) ≤ Real.exp (-(r₂ * (s₀ - cgmΦ φ₁ s₀))) := by
          apply Real.exp_le_exp.2; nlinarith [hmem.1.2]
        nlinarith [mul_le_mul_of_nonneg_left this (show 0 ≤ q₁ * r₂ * y₀ by positivity)]
      linarith [hmem.2]
    · have hneg : ∀ s ∈ Ioo 0 t, E s < 0 := by
        intro s hs; by_contra hc; push_neg at hc
        exact hne ⟨s, ⟨hs.1.le, hs.2.le⟩, hc⟩
      have := step 0 le_rfl ht hneg
      rw [cgm_Φ_zero] at this; linarith
  rcases lt_trichotomy (E t) 0 with hlt | heq | hgt
  · exact Or.inr (Or.inr ⟨neg_case hlt, hlt.le⟩)
  · exact Or.inl heq
  · exact Or.inr (Or.inl ⟨pos_case hgt, hgt.le⟩)


lemma cgm_H_bounds {r₁ r₂ x₀ y₀ u v : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    0 ≤ cgmH r₁ r₂ x₀ y₀ u v ∧ cgmH r₁ r₂ x₀ y₀ u v ≤ x₀ + y₀ := by
  have h1 : Real.exp (-(r₁ * u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h2 : Real.exp (-(r₂ * v)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h3 := Real.exp_pos (-(r₁ * u))
  have h4 := Real.exp_pos (-(r₂ * v))
  unfold cgmH
  constructor <;> nlinarith [mul_nonneg hx₀ h3.le, mul_nonneg hy₀ h4.le,
    mul_nonneg hx₀ (sub_nonneg.2 h1), mul_nonneg hy₀ (sub_nonneg.2 h2)]

lemma cgm_rate_nonneg {q₁ q₂ r₁ r₂ x₀ y₀ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) (t : ℝ) :
    0 ≤ goldRate (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ₁) t := by
  rw [cgm_rate h]
  have := h.2 t
  have : 0 ≤ 1 - φ₁ t := by linarith [this.2]
  have := (h.2 t).1
  positivity

lemma cgm_Ψ_eq (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (φ₁ m : ℝ → ℝ) (t : ℝ) :
    cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m t = Real.exp (-(cgmQ q₁ q₂ φ₁ t)) *
      cgmH r₁ r₂ x₀ y₀ (cgmΦ φ₁ t) (t - cgmΦ φ₁ t) + ∫ σ in (0:ℝ)..(cgmQ q₁ q₂ φ₁ t), m σ :=
  rfl

lemma cgm_lint_le {q₁ q₂ r₁ r₂ x₀ y₀ : ℝ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) {φ₁ m : ℝ → ℝ} (h : TwoAdmissible φ₁)
    (hm : Continuous m) (B : ℝ) (hB : ∀ s, |m s| ≤ B)
    (hmge : ∀ t, 0 ≤ t → Real.exp (-(cgmQ q₁ q₂ φ₁ t)) *
      cgmH r₁ r₂ x₀ y₀ (cgmΦ φ₁ t) (t - cgmΦ φ₁ t) ≤ m (cgmQ q₁ q₂ φ₁ t))
    (T : ℝ) (hT : 0 ≤ T) :
    ∫⁻ t in Ioc 0 T, ENNReal.ofReal (goldRate (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ₁) t)
      ≤ ENNReal.ofReal (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m T) := by
  obtain ⟨hint, hval, hderiv⟩ := cgm_potential q₁ q₂ r₁ r₂ x₀ y₀ hq₁.le hq₂.le h hm B hB T hT
  have hT' : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc 0 T)),
      goldRate (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ₁) t ≤
        deriv (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) t := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hderiv, hT'] with t hd hne hmem
    rw [hd ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩]
    have h1 := h.2 t
    have hQ' : 0 ≤ q₁ * φ₁ t + q₂ * (1 - φ₁ t) := by
      have : 0 ≤ 1 - φ₁ t := by linarith [h1.2]
      have := h1.1; positivity
    have := hmge t hmem.1.le
    exact le_add_of_nonneg_right (mul_nonneg hQ' (by linarith))
  have hint' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hint
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] deriv (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) := by
    filter_upwards [hae] with t ht
    exact (cgm_rate_nonneg hr₁ hr₂ hx₀ hy₀ h t).trans ht
  calc _ ≤ ∫⁻ t in Ioc 0 T, ENNReal.ofReal (deriv (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) t) :=
        lintegral_mono_ae (hae.mono fun t ht => ENNReal.ofReal_le_ofReal ht)
    _ = ENNReal.ofReal (∫ t in Ioc 0 T, deriv (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) t) :=
        (ofReal_integral_eq_lintegral_ofReal hint' hnn).symm
    _ = _ := by rw [← intervalIntegral.integral_of_le hT, hval]

lemma cgm_lint_eq {q₁ q₂ r₁ r₂ x₀ y₀ : ℝ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) {φ₁ m : ℝ → ℝ} (h : TwoAdmissible φ₁)
    (hm : Continuous m) (B : ℝ) (hB : ∀ s, |m s| ≤ B)
    (hmeq : ∀ t, 0 ≤ t → m (cgmQ q₁ q₂ φ₁ t) = Real.exp (-(cgmQ q₁ q₂ φ₁ t)) *
      cgmH r₁ r₂ x₀ y₀ (cgmΦ φ₁ t) (t - cgmΦ φ₁ t))
    (T : ℝ) (hT : 0 ≤ T) :
    ∫⁻ t in Ioc 0 T, ENNReal.ofReal (goldRate (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ₁) t)
      = ENNReal.ofReal (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m T) := by
  obtain ⟨hint, hval, hderiv⟩ := cgm_potential q₁ q₂ r₁ r₂ x₀ y₀ hq₁.le hq₂.le h hm B hB T hT
  have hT' : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc 0 T)),
      goldRate (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ₁) t =
        deriv (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) t := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hderiv, hT'] with t hd hne hmem
    rw [hd ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩, hmeq t hmem.1.le]
    ring
  have hint' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 hint
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 T)] deriv (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) := by
    filter_upwards [hae] with t ht
    rw [← ht]; exact cgm_rate_nonneg hr₁ hr₂ hx₀ hy₀ h t
  calc _ = ∫⁻ t in Ioc 0 T, ENNReal.ofReal (deriv (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) t) :=
        lintegral_congr_ae (hae.mono fun t ht => by rw [ht])
    _ = ENNReal.ofReal (∫ t in Ioc 0 T, deriv (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ₁ m) t) :=
        (ofReal_integral_eq_lintegral_ofReal hint' hnn).symm
    _ = _ := by rw [← intervalIntegral.integral_of_le hT, hval]

lemma cgm_Q_zero (q₁ q₂ : ℝ) (φ₁ : ℝ → ℝ) : cgmQ q₁ q₂ φ₁ 0 = 0 := by
  simp [cgmQ, cgm_Φ_zero]

theorem cgm_opt {q₁ q₂ r₁ r₂ x₀ y₀ : ℝ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) {φ ψ : ℝ → ℝ} (hφ : TwoAdmissible φ)
    (hrule : FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ) (hψ : TwoAdmissible ψ) :
    goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice ψ) ≤
      goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ) := by
  set c := min q₁ q₂ with hc
  have hc0 : 0 < c := lt_min hq₁ hq₂
  set Q := cgmQ q₁ q₂ φ with hQdef
  have hΦc := (cgm_Φ_lip hφ).continuous
  have hmono : StrictMono Q := by
    intro s t hst
    have := cgm_Q_mono hq₁.le hq₂.le hφ hst.le
    nlinarith [mul_pos hc0 (sub_pos.2 hst)]
  have hQc : Continuous Q := by rw [hQdef]; unfold cgmQ; fun_prop
  have hQ0 : Q 0 = 0 := cgm_Q_zero q₁ q₂ φ
  have hsurj : Function.Surjective Q := by
    intro s
    set R := |s| / c
    have hR : 0 ≤ R := by positivity
    have hcR : c * R = |s| := by simp only [R]; field_simp
    have hm1 : c * (R - 0) ≤ Q R - Q 0 := cgm_Q_mono hq₁.le hq₂.le hφ hR
    have hm2 : c * (0 - -R) ≤ Q 0 - Q (-R) := cgm_Q_mono hq₁.le hq₂.le hφ (by linarith)
    have h1 : |s| ≤ Q R := by rw [hQ0] at hm1; linarith
    have h2 : Q (-R) ≤ -|s| := by rw [hQ0] at hm2; linarith
    have hs : s ∈ Icc (Q (-R)) (Q R) := ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (by linarith) hQc.continuousOn hs
    exact ⟨t, ht⟩
  set e := hmono.orderIsoOfSurjective Q hsurj
  set τ : ℝ → ℝ := fun s => e.symm s
  have hτQ : ∀ t, τ (Q t) = t := fun t => e.symm_apply_apply t
  have hQτ : ∀ s, Q (τ s) = s := fun s => e.apply_symm_apply s
  have hτc : Continuous τ := e.symm.continuous
  have hτnn : ∀ s, 0 ≤ s → 0 ≤ τ s := by
    intro s hs
    rw [← hmono.le_iff_le, hQτ, hQ0]; exact hs
  set m : ℝ → ℝ := fun s => cgmH r₁ r₂ x₀ y₀ (cgmΦ φ (τ (max s 0)))
      (τ (max s 0) - cgmΦ φ (τ (max s 0))) * Real.exp (-(max s 0)) with hmdef
  have hm : Continuous m := by rw [hmdef]; unfold cgmH; fun_prop
  have hB : ∀ s, |m s| ≤ x₀ + y₀ := by
    intro s
    have ht := hτnn (max s 0) (le_max_right _ _)
    have hb := cgm_Φ_nonneg hφ ht
    have hH := cgm_H_bounds hr₁ hr₂ hx₀ hy₀ hb.1 (show 0 ≤ τ (max s 0) - cgmΦ φ (τ (max s 0))
      by linarith [hb.2])
    have he1 : Real.exp (-(max s 0)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [le_max_right s 0])
    have he0 := Real.exp_pos (-(max s 0))
    rw [abs_le]
    constructor <;> simp only [hmdef] <;> nlinarith [mul_le_mul_of_nonneg_left he1 hH.1]
  have hmφ : ∀ t, 0 ≤ t → m (cgmQ q₁ q₂ φ t) = Real.exp (-(cgmQ q₁ q₂ φ t)) *
      cgmH r₁ r₂ x₀ y₀ (cgmΦ φ t) (t - cgmΦ φ t) := by
    intro t ht
    have hQt : 0 ≤ Q t := by rw [← hQ0]; exact hmono.monotone ht
    simp only [hmdef, ← hQdef, max_eq_left hQt, hτQ]
    ring
  have hmψ : ∀ t, 0 ≤ t → Real.exp (-(cgmQ q₁ q₂ ψ t)) *
      cgmH r₁ r₂ x₀ y₀ (cgmΦ ψ t) (t - cgmΦ ψ t) ≤ m (cgmQ q₁ q₂ ψ t) := by
    intro t ht
    have hQt : 0 ≤ cgmQ q₁ q₂ ψ t := by
      have := cgm_Q_mono hq₁.le hq₂.le hψ ht
      rw [cgm_Q_zero] at this; nlinarith
    simp only [hmdef, max_eq_left hQt]
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    set t' := τ (cgmQ q₁ q₂ ψ t)
    have ht' : 0 ≤ t' := hτnn _ hQt
    have hb := cgm_Φ_nonneg hψ ht
    apply cgm_kkt_ineq hq₁ hq₂ hr₁ hr₂ hx₀ hy₀ hb.1 (by linarith [hb.2])
    · have h' : Q t' = cgmQ q₁ q₂ ψ t := hQτ _
      simp only [hQdef, cgmQ] at h' ⊢
      linarith
    · have := cgm_index_kkt hq₁ hq₂ hr₁ hr₂ hx₀ hy₀ hφ hrule t' ht'
      simp only [cgmE] at this
      exact this
  -- the value of the index policy dominates F
  set S := goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ)
  have hFS : ∀ s, 0 ≤ s → ENNReal.ofReal (∫ σ in (0:ℝ)..s, m σ) ≤ S := by
    intro s hs
    have ht' := hτnn s hs
    have heq := cgm_lint_eq hq₁ hq₂ hr₁ hr₂ hx₀ hy₀ hφ hm (x₀ + y₀) hB hmφ (τ s) ht'
    have hb := cgm_Φ_nonneg hφ ht'
    have hH := cgm_H_bounds hr₁ hr₂ hx₀ hy₀ hb.1 (show 0 ≤ τ s - cgmΦ φ (τ s) by linarith [hb.2])
    calc ENNReal.ofReal (∫ σ in (0:ℝ)..s, m σ)
        ≤ ENNReal.ofReal (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ m (τ s)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [cgm_Ψ_eq, ← hQdef, hQτ]
          have := mul_nonneg (Real.exp_pos (-s)).le hH.1
          linarith
      _ = _ := heq.symm
      _ ≤ S := lintegral_mono_set Ioc_subset_Ioi_self
  -- bound for ψ
  have hbound : ∀ T, 0 ≤ T → ∫⁻ t in Ioc 0 T,
      ENNReal.ofReal (goldRate (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice ψ) t) ≤
        ENNReal.ofReal ((x₀ + y₀) * Real.exp (-(c * T))) + S := by
    intro T hT
    refine (cgm_lint_le hq₁ hq₂ hr₁ hr₂ hx₀ hy₀ hψ hm (x₀ + y₀) hB hmψ T hT).trans ?_
    have hQT : c * T ≤ cgmQ q₁ q₂ ψ T := by
      have := cgm_Q_mono hq₁.le hq₂.le hψ hT
      rw [cgm_Q_zero] at this; linarith
    have hb := cgm_Φ_nonneg hψ hT
    have hH := cgm_H_bounds hr₁ hr₂ hx₀ hy₀ hb.1 (show 0 ≤ T - cgmΦ ψ T by linarith [hb.2])
    rw [cgm_Ψ_eq]
    refine (ENNReal.ofReal_add_le).trans (add_le_add ?_ (hFS _ (by nlinarith)))
    apply ENNReal.ofReal_le_ofReal
    have : Real.exp (-cgmQ q₁ q₂ ψ T) ≤ Real.exp (-(c * T)) := Real.exp_le_exp.2 (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right this hH.1, Real.exp_pos (-(c * T))]
  -- conclude
  unfold goldInfty
  have hU : Ioi (0:ℝ) = ⋃ n : ℕ, Ioc 0 (n : ℝ) := by
    ext t
    simp only [mem_Ioi, mem_iUnion, mem_Ioc]
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact ⟨n, ht, hn⟩
    · rintro ⟨n, ht, _⟩; exact ht
  rw [hU, setLIntegral_iUnion_of_directed]
  · refine iSup_le fun n => ?_
    have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal ((x₀ + y₀) * Real.exp (-(c * N))) + S)
        atTop (𝓝 (0 + S)) := by
      refine Tendsto.add ?_ tendsto_const_nhds
      rw [← ENNReal.ofReal_zero]
      apply ENNReal.tendsto_ofReal
      have h1 : Tendsto (fun N : ℕ => c * (N : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.const_mul_atTop hc0
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul (x₀ + y₀)
      simpa using h2
    rw [zero_add] at hlim
    refine ge_of_tendsto hlim (eventually_atTop.2 ⟨n, fun N hN => ?_⟩)
    refine (lintegral_mono_set (Ioc_subset_Ioc_right (Nat.cast_le.2 hN))).trans ?_
    exact hbound N (Nat.cast_nonneg N)
  · exact Monotone.directed_le fun a b hab => Ioc_subset_Ioc_right (Nat.cast_le.2 hab)


lemma cgm_rule_of {q₁ q₂ r₁ r₂ x₀ y₀ : ℝ} {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁)
    (H : ∀ s, 0 ≤ s → (0 < cgmE q₁ q₂ r₁ r₂ x₀ y₀ φ₁ s → φ₁ s = 1) ∧
      (cgmE q₁ q₂ r₁ r₂ x₀ y₀ φ₁ s < 0 → φ₁ s = 0) ∧
      (cgmE q₁ q₂ r₁ r₂ x₀ y₀ φ₁ s = 0 → φ₁ s = r₂ / (r₁ + r₂))) :
    FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ₁ := by
  unfold FollowsIndexRule
  rw [ae_restrict_iff' measurableSet_Ici]
  refine ae_of_all _ (fun s hs => ?_)
  have := H s hs
  simp only [cgm_stateX h, cgm_stateY h]
  unfold cgmE at this
  exact ⟨fun h1 => this.1 (by linarith), fun h2 => this.2.1 (by linarith),
    fun h3 => this.2.2 (by linarith)⟩

lemma cgm_pw_adm {a c τ : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hc : c ∈ Icc (0:ℝ) 1) :
    TwoAdmissible (fun s => if s < τ then a else c) := by
  refine ⟨Measurable.ite measurableSet_Iio measurable_const measurable_const, fun s => ?_⟩
  dsimp only
  split_ifs
  · exact ha
  · exact hc

lemma cgm_pw_Φ {a c τ : ℝ} (hτ : 0 ≤ τ) (ha : a ∈ Icc (0:ℝ) 1) (hc : c ∈ Icc (0:ℝ) 1) :
    (∀ s, 0 ≤ s → s ≤ τ → cgmΦ (fun s => if s < τ then a else c) s = a * s) ∧
    (∀ s, τ ≤ s → cgmΦ (fun s => if s < τ then a else c) s = a * τ + c * (s - τ)) := by
  have h := cgm_pw_adm (τ := τ) ha hc
  have first : ∀ s, 0 ≤ s → s ≤ τ → cgmΦ (fun s => if s < τ then a else c) s = a * s := by
    intro s hs hsτ
    have := cgm_ae_const_interval h hs (c := a) (ae_of_all _ (fun x hx => by
      simp only [if_pos (lt_of_lt_of_le hx.2 hsτ)]))
    rw [cgm_Φ_zero] at this; linarith
  refine ⟨first, fun s hs => ?_⟩
  have := cgm_ae_const_interval h hs (c := c) (ae_of_all _ (fun x hx => by
    simp only [if_neg (not_lt.2 hx.1.le)]))
  rw [first τ hτ le_rfl] at this; linarith

lemma cgm_const_Φ {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (s : ℝ) (hs : 0 ≤ s) :
    cgmΦ (fun _ => a) s = a * s := by
  have h : TwoAdmissible (fun _ : ℝ => a) := ⟨measurable_const, fun _ => ha⟩
  have := cgm_ae_const_interval h hs (c := a) (ae_of_all _ (fun x _ => rfl))
  rw [cgm_Φ_zero] at this; linarith

theorem cgm_exists {q₁ q₂ r₁ r₂ x₀ y₀ : ℝ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    ∃ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ ∧ FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ₁ := by
  set c := r₂ / (r₁ + r₂) with hcdef
  have hc : c ∈ Icc (0:ℝ) 1 :=
    ⟨by positivity, (div_le_one (by linarith)).2 (by linarith)⟩
  have h01 : (1:ℝ) ∈ Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have h00 : (0:ℝ) ∈ Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hkey : r₂ * (1 - c) = r₁ * c := by rw [hcdef]; field_simp; ring
  rcases hx₀.lt_or_eq with hx | hx <;> rcases hy₀.lt_or_eq with hy | hy
  · -- both positive
    set L := Real.log (q₂ * r₁ * x₀ / (q₁ * r₂ * y₀)) with hL
    have hpos : 0 < q₂ * r₁ * x₀ / (q₁ * r₂ * y₀) := by positivity
    have heL : Real.exp L = q₂ * r₁ * x₀ / (q₁ * r₂ * y₀) := Real.exp_log hpos
    rcases le_or_gt 0 L with hL0 | hL0
    · set τ := L / r₁ with hτ
      have hτ0 : 0 ≤ τ := by positivity
      have hrτ : r₁ * τ = L := by rw [hτ]; field_simp
      clear_value τ
      have hadm := cgm_pw_adm (τ := τ) h01 hc
      obtain ⟨hΦ1, hΦ2⟩ := cgm_pw_Φ hτ0 h01 hc
      refine ⟨_, hadm, cgm_rule_of hadm (fun s hs => ?_)⟩
      by_cases hsτ : s < τ
      · have hE : 0 < cgmE q₁ q₂ r₁ r₂ x₀ y₀ (fun s => if s < τ then 1 else c) s := by
          simp only [cgmE, hΦ1 s hs hsτ.le, one_mul, sub_self, mul_zero, neg_zero,
            Real.exp_zero, mul_one]
          have h1 : Real.exp (-L) < Real.exp (-(r₁ * s)) := Real.exp_lt_exp.2 (by nlinarith)
          rw [Real.exp_neg, heL, inv_div] at h1
          have h2 := mul_lt_mul_of_pos_left h1 (show 0 < q₂ * r₁ * x₀ by positivity)
          rw [mul_div_assoc', mul_div_cancel_left₀ _ (show q₂ * r₁ * x₀ ≠ 0 by positivity)] at h2
          linarith
        refine ⟨fun _ => by simp [hsτ], fun h => absurd h (not_lt.2 hE.le), fun h => ?_⟩
        rw [h] at hE; exact absurd hE (lt_irrefl _)
      · have hE : cgmE q₁ q₂ r₁ r₂ x₀ y₀ (fun s => if s < τ then 1 else c) s = 0 := by
          simp only [cgmE, hΦ2 s (not_lt.1 hsτ), one_mul]
          have e1 : -(r₁ * (τ + c * (s - τ))) = -L + -(r₁ * c * (s - τ)) := by
            rw [← hrτ]; ring
          have e2 : -(r₂ * (s - (τ + c * (s - τ)))) = -(r₁ * c * (s - τ)) := by
            rw [← hkey]; ring
          rw [e1, e2, Real.exp_add, Real.exp_neg L, heL, inv_div]
          field_simp
          ring
        refine ⟨fun h => by rw [hE] at h; exact absurd h (lt_irrefl _),
          fun h => by rw [hE] at h; exact absurd h (lt_irrefl _), fun _ => by simpa [hsτ] using hcdef⟩
    · set τ := -L / r₂ with hτ
      have hτ0 : 0 ≤ τ := div_nonneg (by linarith) hr₂.le
      have hrτ : r₂ * τ = -L := by rw [hτ]; field_simp
      clear_value τ
      have hadm := cgm_pw_adm (τ := τ) h00 hc
      obtain ⟨hΦ1, hΦ2⟩ := cgm_pw_Φ hτ0 h00 hc
      refine ⟨_, hadm, cgm_rule_of hadm (fun s hs => ?_)⟩
      by_cases hsτ : s < τ
      · have hE : cgmE q₁ q₂ r₁ r₂ x₀ y₀ (fun s => if s < τ then 0 else c) s < 0 := by
          simp only [cgmE, hΦ1 s hs hsτ.le, zero_mul, sub_zero, mul_zero, neg_zero,
            Real.exp_zero, mul_one]
          have h1 : Real.exp L < Real.exp (-(r₂ * s)) := Real.exp_lt_exp.2 (by nlinarith)
          rw [heL] at h1
          have h2 := mul_lt_mul_of_pos_left h1 (show 0 < q₁ * r₂ * y₀ by positivity)
          rw [mul_div_assoc', mul_div_cancel_left₀ _ (show q₁ * r₂ * y₀ ≠ 0 by positivity)] at h2
          linarith
        refine ⟨fun h => absurd h (not_lt.2 hE.le), fun _ => by simp [hsτ], fun h => ?_⟩
        rw [h] at hE; exact absurd hE (lt_irrefl _)
      · have hE : cgmE q₁ q₂ r₁ r₂ x₀ y₀ (fun s => if s < τ then 0 else c) s = 0 := by
          simp only [cgmE, hΦ2 s (not_lt.1 hsτ), zero_mul, zero_add]
          have e1 : -(r₂ * (s - c * (s - τ))) = L + -(r₁ * c * (s - τ)) := by
            rw [← hkey]; linear_combination (-1 : ℝ) * hrτ
          rw [e1, Real.exp_add, heL]
          field_simp
          ring
        refine ⟨fun h => by rw [hE] at h; exact absurd h (lt_irrefl _),
          fun h => by rw [hE] at h; exact absurd h (lt_irrefl _), fun _ => by simpa [hsτ] using hcdef⟩
  · -- x₀ > 0, y₀ = 0
    have hadm : TwoAdmissible (fun _ : ℝ => (1:ℝ)) := ⟨measurable_const, fun _ => h01⟩
    refine ⟨_, hadm, cgm_rule_of hadm (fun s hs => ?_)⟩
    have hE : 0 < cgmE q₁ q₂ r₁ r₂ x₀ y₀ (fun _ => 1) s := by
      simp only [cgmE, ← hy, mul_zero, zero_mul, sub_zero]
      positivity
    exact ⟨fun _ => rfl, fun h => absurd h (not_lt.2 hE.le),
      fun h => by rw [h] at hE; exact absurd hE (lt_irrefl _)⟩
  · -- x₀ = 0, y₀ > 0
    have hadm : TwoAdmissible (fun _ : ℝ => (0:ℝ)) := ⟨measurable_const, fun _ => h00⟩
    refine ⟨_, hadm, cgm_rule_of hadm (fun s hs => ?_)⟩
    have hE : cgmE q₁ q₂ r₁ r₂ x₀ y₀ (fun _ => 0) s < 0 := by
      simp only [cgmE, ← hx, mul_zero, zero_mul, zero_sub]
      have : 0 < q₁ * r₂ * (y₀ * Real.exp (-(r₂ * (s - cgmΦ (fun _ => 0) s)))) := by positivity
      linarith
    exact ⟨fun h => absurd h (not_lt.2 hE.le), fun _ => rfl,
      fun h => by rw [h] at hE; exact absurd hE (lt_irrefl _)⟩
  · -- both zero
    have hadm : TwoAdmissible (fun _ : ℝ => c) := ⟨measurable_const, fun _ => hc⟩
    refine ⟨_, hadm, cgm_rule_of hadm (fun s hs => ?_)⟩
    have hE : cgmE q₁ q₂ r₁ r₂ x₀ y₀ (fun _ => c) s = 0 := by
      simp only [cgmE, ← hx, ← hy, mul_zero, zero_mul, sub_zero]
    exact ⟨fun h => by rw [hE] at h; exact absurd h (lt_irrefl _),
      fun h => by rw [hE] at h; exact absurd h (lt_irrefl _), fun _ => rfl⟩

theorem index_policy_optimal_core (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    (∃ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ ∧ FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ₁) ∧
    ∀ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ → FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ₁ →
      ∀ ψ₁ : ℝ → ℝ, TwoAdmissible ψ₁ →
        goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice ψ₁) ≤
          goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ₁) :=
  ⟨cgm_exists hq₁ hq₂ hr₁ hr₂ hx₀ hy₀, fun _ hφ hrule _ hψ =>
    cgm_opt hq₁ hq₂ hr₁ hr₂ hx₀ hy₀ hφ hrule hψ⟩


/-! ## Three-choice controls -/

lemma cgm3_bnd {φ : Control} (h : Admissible φ) (i : Fin 3) (t : ℝ) : 0 ≤ φ i t ∧ φ i t ≤ 1 := by
  refine ⟨h.2.1 i t, ?_⟩
  have := Finset.single_le_sum (f := fun j => φ j t) (fun j _ => h.2.1 j t) (Finset.mem_univ i)
  rw [h.2.2 t] at this; exact this

lemma cgm3_ii {φ : Control} (h : Admissible φ) (i : Fin 3) (a b : ℝ) :
    IntervalIntegrable (φ i) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (1:ℝ)) intervalIntegrable_const
    (h.1 i).aestronglyMeasurable (ae_of_all _ (fun t => ?_))
  have := cgm3_bnd h i t
  show ‖φ i t‖ ≤ 1
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨by linarith [this.1], this.2⟩

lemma cgm3_cum_zero (φ : Control) (i : Fin 3) : cumTime φ i 0 = 0 := by simp [cumTime]

lemma cgm3_cum_bounds {φ : Control} (h : Admissible φ) (i : Fin 3) {s t : ℝ} (hst : s ≤ t) :
    0 ≤ cumTime φ i t - cumTime φ i s ∧ cumTime φ i t - cumTime φ i s ≤ t - s := by
  rw [show cumTime φ i t - cumTime φ i s = ∫ x in s..t, φ i x from
    intervalIntegral.integral_interval_sub_left (cgm3_ii h i 0 t) (cgm3_ii h i 0 s)]
  constructor
  · exact intervalIntegral.integral_nonneg hst (fun x _ => (cgm3_bnd h i x).1)
  · have := intervalIntegral.integral_mono_on hst (cgm3_ii h i s t)
      (intervalIntegrable_const (c := (1:ℝ))) (fun x _ => (cgm3_bnd h i x).2)
    simpa using this

lemma cgm3_cum_abs {φ : Control} (h : Admissible φ) (i : Fin 3) (s t : ℝ) :
    |cumTime φ i t - cumTime φ i s| ≤ |t - s| := by
  rcases le_total s t with hst | hst
  · have := cgm3_cum_bounds h i hst
    rw [abs_of_nonneg this.1, abs_of_nonneg (by linarith)]; exact this.2
  · have := cgm3_cum_bounds h i hst
    rw [abs_sub_comm, abs_of_nonneg this.1, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact this.2

lemma cgm3_cum_sum {φ : Control} (h : Admissible φ) (t : ℝ) : ∑ i, cumTime φ i t = t := by
  unfold cumTime
  rw [← intervalIntegral.integral_finset_sum (fun i _ => cgm3_ii h i 0 t)]
  simp [h.2.2]

lemma cgm3_lin_abs {φ : Control} (h : Admissible φ) (c : Fin 3 → ℝ) (s t : ℝ) :
    |∑ i, c i * cumTime φ i t - ∑ i, c i * cumTime φ i s| ≤ (∑ i, |c i|) * |t - s| := by
  rw [← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (cgm3_cum_abs h i s t) (abs_nonneg _)

lemma cgm3_lin_lip {φ : Control} (h : Admissible φ) (c : Fin 3 → ℝ) :
    LipschitzWith (Real.toNNReal (∑ i, |c i|)) (fun t => ∑ i, c i * cumTime φ i t) :=
  LipschitzWith.of_dist_le_mul fun s t => by
    rw [Real.coe_toNNReal _ (Finset.sum_nonneg fun i _ => abs_nonneg _), Real.dist_eq,
      Real.dist_eq]
    exact cgm3_lin_abs h c t s

noncomputable def cgmL (c : Fin 3 → ℝ) (φ : Control) (t : ℝ) : ℝ := ∑ i, c i * cumTime φ i t

noncomputable def cgm3Ψ (P : Params) (x₀ y₀ : ℝ) (φ : Control) (m : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-(cgmL P.q φ t)) *
      (x₀ * (1 - Real.exp (-(cgmL P.a φ t))) + y₀ * (1 - Real.exp (-(cgmL P.b φ t))))
    + ∫ σ in (0:ℝ)..(cgmL P.q φ t), m σ

lemma cgmL_zero (c : Fin 3 → ℝ) (φ : Control) : cgmL c φ 0 = 0 := by
  simp [cgmL, cgm3_cum_zero]

lemma cgm3_potential (P : Params) (x₀ y₀ : ℝ) {φ : Control} {m : ℝ → ℝ}
    (h : Admissible φ) (hm : Continuous m) (B : ℝ) (hB : ∀ s, |m s| ≤ B) (T : ℝ)
    (hT : 0 ≤ T) :
    IntervalIntegrable (deriv (cgm3Ψ P x₀ y₀ φ m)) volume 0 T ∧
    ∫ t in (0:ℝ)..T, deriv (cgm3Ψ P x₀ y₀ φ m) t = cgm3Ψ P x₀ y₀ φ m T ∧
    ∀ᵐ t, t ∈ Ioo 0 T → deriv (cgm3Ψ P x₀ y₀ φ m) t =
      goldRate P x₀ y₀ φ t + (∑ i, P.q i * φ i t) *
          (m (cgmL P.q φ t) - Real.exp (-(cgmL P.q φ t)) *
            (x₀ * (1 - Real.exp (-(cgmL P.a φ t))) + y₀ * (1 - Real.exp (-(cgmL P.b φ t))))) := by
  set G : ℝ × ℝ × ℝ → ℝ := fun p => Real.exp (-p.2.2) *
      (x₀ * (1 - Real.exp (-p.1)) + y₀ * (1 - Real.exp (-p.2.1))) with hGdef
  have hG : ContDiff ℝ 1 G := by rw [hGdef]; fun_prop
  set p : ℝ → ℝ × ℝ × ℝ := fun t => (cgmL P.a φ t, cgmL P.b φ t, cgmL P.q φ t) with hpdef
  have hp : LipschitzWith _ p :=
    (cgm3_lin_lip h P.a).prodMk ((cgm3_lin_lip h P.b).prodMk (cgm3_lin_lip h P.q))
  set Kp := max (Real.toNNReal (∑ i, |P.a i|))
    (max (Real.toNNReal (∑ i, |P.b i|)) (Real.toNNReal (∑ i, |P.q i|)))
  obtain ⟨K₁, hK₁⟩ := (hG.contDiffOn (s := Metric.closedBall (p 0) (Kp * T))).exists_lipschitzOnWith
    (by simp) (convex_closedBall _ _) (isCompact_closedBall _ _)
  have hmaps : MapsTo p (uIcc 0 T) (Metric.closedBall (p 0) (Kp * T)) := by
    intro t ht
    rw [uIcc_of_le hT] at ht
    rw [Metric.mem_closedBall]
    refine (hp.dist_le_mul t 0).trans ?_
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact mul_le_mul_of_nonneg_left ht.2 (by positivity)
  have hL1 := hK₁.comp hp.lipschitzOnWith hmaps
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hFl : LipschitzWith (Real.toNNReal B) (fun s => ∫ σ in (0:ℝ)..s, m σ) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    rw [Real.coe_toNNReal _ hB0, Real.dist_eq, Real.dist_eq,
      intervalIntegral.integral_interval_sub_left (hm.intervalIntegrable _ _)
        (hm.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := t) (b := s) (f := m)
      (C := B) (fun x _ => hB x)
    rwa [Real.norm_eq_abs] at this
  have hL2 := hFl.comp (cgm3_lin_lip h P.q)
  have hAC : AbsolutelyContinuousOnInterval (cgm3Ψ P x₀ y₀ φ m) 0 T :=
    hL1.absolutelyContinuousOnInterval.add hL2.lipschitzOnWith.absolutelyContinuousOnInterval
  refine ⟨hAC.intervalIntegrable_deriv, ?_, ?_⟩
  · rw [hAC.integral_deriv_eq_sub]
    simp [cgm3Ψ, cgmL_zero]
  · have hall : ∀ᵐ t, ∀ i : Fin 3, t ∈ uIcc 0 T → ∀ c ∈ uIcc 0 T,
        HasDerivAt (fun x => ∫ s in c..x, φ i s) (φ i t) t := by
      rw [ae_all_iff]; intro i; exact (cgm3_ii h i 0 T).ae_hasDerivAt_integral
    filter_upwards [hall] with t ht htI
    have htI' : t ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact Ioo_subset_Icc_self htI
    have hΦ : ∀ i, HasDerivAt (fun x => cumTime φ i x) (φ i t) t :=
      fun i => ht i htI' 0 left_mem_uIcc
    have hlin : ∀ c : Fin 3 → ℝ, HasDerivAt (cgmL c φ) (∑ i, c i * φ i t) t := by
      intro c
      have := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hΦ i).const_mul (c i))
      exact this
    have hQ := hlin P.q
    have hE := hQ.neg.exp
    have hH := ((((hlin P.a).neg.exp).const_sub 1).const_mul x₀).add
      ((((hlin P.b).neg.exp).const_sub 1).const_mul y₀)
    have hF := (hm.integral_hasStrictDerivAt 0 (cgmL P.q φ t)).hasDerivAt
    have hT' := (hE.mul hH).add (hF.comp t hQ)
    rw [(show HasDerivAt (cgm3Ψ P x₀ y₀ φ m) _ t from hT').deriv]
    simp only [goldRate, survival, stateX, stateY, cgmL, Function.comp, Pi.add_apply,
      Pi.neg_apply, Pi.sub_apply, Pi.mul_apply, Fin.sum_univ_three]
    ring

lemma cgm3_rate_nonneg (P : Params) (hP : P.Positive) {x₀ y₀ : ℝ} (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) {φ : Control} (h : Admissible φ) (t : ℝ) : 0 ≤ goldRate P x₀ y₀ φ t := by
  obtain ⟨hq1, hq2, hq3, hr1, hr2, hr3, hr4⟩ := hP
  unfold goldRate survival stateX stateY
  apply mul_nonneg (Real.exp_pos _).le
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (h.2.1 i t)
  have ha : 0 ≤ P.a i := by fin_cases i <;> simp [Params.a] <;> linarith
  have hb : 0 ≤ P.b i := by fin_cases i <;> simp [Params.b] <;> linarith
  positivity

noncomputable def cgm3gap (P : Params) (x₀ y₀ : ℝ) (φ : Control) (m : ℝ → ℝ) (t : ℝ) : ℝ :=
  m (cgmL P.q φ t) - Real.exp (-(cgmL P.q φ t)) *
    (x₀ * (1 - Real.exp (-(cgmL P.a φ t))) + y₀ * (1 - Real.exp (-(cgmL P.b φ t))))

lemma cgm3_lint_gap (P : Params) (hP : P.Positive) {x₀ y₀ : ℝ} (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    {φ : Control} {m : ℝ → ℝ} (h : Admissible φ) (hm : Continuous m) (B : ℝ)
    (hB : ∀ s, |m s| ≤ B) (T : ℝ) (hT : 0 ≤ T) :
    ∫⁻ t in Ioc 0 T, ENNReal.ofReal (goldRate P x₀ y₀ φ t) =
      ENNReal.ofReal (cgm3Ψ P x₀ y₀ φ m T -
        ∫ t in (0:ℝ)..T, (∑ i, P.q i * φ i t) * cgm3gap P x₀ y₀ φ m t) := by
  obtain ⟨hint, hval, hderiv⟩ := cgm3_potential P x₀ y₀ h hm B hB T hT
  have hT' : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
  have hcont : Continuous (cgm3gap P x₀ y₀ φ m) := by
    have h1 : Continuous (cgmL P.q φ) := (cgm3_lin_lip h P.q).continuous
    have h2 : Continuous (cgmL P.a φ) := (cgm3_lin_lip h P.a).continuous
    have h3 : Continuous (cgmL P.b φ) := (cgm3_lin_lip h P.b).continuous
    unfold cgm3gap
    exact (hm.comp h1).sub (by fun_prop)
  have hQ'int : IntervalIntegrable (fun t => ∑ i, P.q i * φ i t) volume 0 T := by
    have : (fun t => ∑ i, P.q i * φ i t) =
        fun t => P.q 0 * φ 0 t + P.q 1 * φ 1 t + P.q 2 * φ 2 t :=
      funext fun t => Fin.sum_univ_three _
    rw [this]
    exact (((cgm3_ii h 0 0 T).const_mul _).add ((cgm3_ii h 1 0 T).const_mul _)).add
      ((cgm3_ii h 2 0 T).const_mul _)
  have hgint : IntervalIntegrable
      (fun t => (∑ i, P.q i * φ i t) * cgm3gap P x₀ y₀ φ m t) volume 0 T :=
    hQ'int.mul_continuousOn hcont.continuousOn
  have hae : ∀ᵐ t ∂(volume.restrict (Ioc 0 T)), goldRate P x₀ y₀ φ t =
      deriv (cgm3Ψ P x₀ y₀ φ m) t - (∑ i, P.q i * φ i t) * cgm3gap P x₀ y₀ φ m t := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hderiv, hT'] with t hd hne hmem
    rw [hd ⟨hmem.1, lt_of_le_of_ne hmem.2 hne⟩, cgm3gap]
    ring
  have hint' := (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 (hint.sub hgint)
  have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 T)]
      fun t => deriv (cgm3Ψ P x₀ y₀ φ m) t - (∑ i, P.q i * φ i t) * cgm3gap P x₀ y₀ φ m t := by
    filter_upwards [hae] with t ht
    rw [← ht]; exact cgm3_rate_nonneg P hP hx₀ hy₀ h t
  calc _ = ∫⁻ t in Ioc 0 T, ENNReal.ofReal (deriv (cgm3Ψ P x₀ y₀ φ m) t -
        (∑ i, P.q i * φ i t) * cgm3gap P x₀ y₀ φ m t) :=
        lintegral_congr_ae (hae.mono fun t ht => by rw [ht])
    _ = ENNReal.ofReal (∫ t in Ioc 0 T, (deriv (cgm3Ψ P x₀ y₀ φ m) t -
        (∑ i, P.q i * φ i t) * cgm3gap P x₀ y₀ φ m t)) :=
        (ofReal_integral_eq_lintegral_ofReal hint' hnn).symm
    _ = _ := by
        rw [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_sub hint hgint, hval]

lemma cgm_kkt3 {q₁ q₂ q₃ r₁ r₂ r₃ r₄ x₀ y₀ u v w u' v' : ℝ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hr₃ : 0 < r₃) (hr₄ : 0 < r₄) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hD : q₁ * r₂ * r₃ + q₂ * r₁ * r₄ - q₃ * r₁ * r₂ < 0)
    (hs : q₁ * u + q₂ * v + q₃ * w = q₁ * u' + q₂ * v')
    (hk : q₂ * r₁ * (x₀ * Real.exp (-(r₁ * u'))) - q₁ * r₂ * (y₀ * Real.exp (-(r₂ * v'))) = 0 ∨
      (v' = 0 ∧ 0 ≤ q₂ * r₁ * (x₀ * Real.exp (-(r₁ * u'))) -
        q₁ * r₂ * (y₀ * Real.exp (-(r₂ * v'))))  ∨
      (u' = 0 ∧ q₂ * r₁ * (x₀ * Real.exp (-(r₁ * u'))) -
        q₁ * r₂ * (y₀ * Real.exp (-(r₂ * v'))) ≤ 0)) :
    x₀ * (1 - Real.exp (-(r₁ * u + r₃ * w))) + y₀ * (1 - Real.exp (-(r₂ * v + r₄ * w))) ≤
      cgmH r₁ r₂ x₀ y₀ u' v' ∧
    (0 < w → x₀ * (1 - Real.exp (-(r₁ * u + r₃ * w))) +
      y₀ * (1 - Real.exp (-(r₂ * v + r₄ * w))) < cgmH r₁ r₂ x₀ y₀ u' v') := by
  set a := Real.exp (-(r₁ * u')) with ha
  set b := Real.exp (-(r₂ * v')) with hb
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := Real.exp_pos _
  have e1 : a * (1 - (r₁ * u + r₃ * w - r₁ * u')) ≤ Real.exp (-(r₁ * u + r₃ * w)) := by
    have : Real.exp (-(r₁ * u + r₃ * w)) = a * Real.exp (-(r₁ * u + r₃ * w - r₁ * u')) := by
      rw [ha, ← Real.exp_add]; ring_nf
    rw [this]
    have := Real.add_one_le_exp (-(r₁ * u + r₃ * w - r₁ * u'))
    nlinarith
  have e2 : b * (1 - (r₂ * v + r₄ * w - r₂ * v')) ≤ Real.exp (-(r₂ * v + r₄ * w)) := by
    have : Real.exp (-(r₂ * v + r₄ * w)) = b * Real.exp (-(r₂ * v + r₄ * w - r₂ * v')) := by
      rw [hb, ← Real.exp_add]; ring_nf
    rw [this]
    have := Real.add_one_le_exp (-(r₂ * v + r₄ * w - r₂ * v'))
    nlinarith
  set G := x₀ * a * (r₁ * (u - u') + r₃ * w) + y₀ * b * (r₂ * (v - v') + r₄ * w) with hG
  have hle : x₀ * (1 - Real.exp (-(r₁ * u + r₃ * w))) + y₀ * (1 - Real.exp (-(r₂ * v + r₄ * w)))
      - cgmH r₁ r₂ x₀ y₀ u' v' ≤ G := by
    unfold cgmH
    nlinarith [mul_le_mul_of_nonneg_left e1 hx₀.le, mul_le_mul_of_nonneg_left e2 hy₀.le]
  set E := q₂ * r₁ * (x₀ * a) - q₁ * r₂ * (y₀ * b) with hE
  set Dv := q₁ * r₂ * r₃ + q₂ * r₁ * r₄ - q₃ * r₁ * r₂ with hDv
  have id1 : q₁ * r₁ * r₂ * G = -(r₁ * E * (r₂ * (v - v') + r₄ * w)) + w * Dv * (r₁ * x₀ * a) := by
    rw [hG, hE, hDv]; linear_combination (r₁ * r₂ * (r₁ * x₀ * a)) * hs
  have id2 : q₂ * r₁ * r₂ * G = r₂ * E * (r₁ * (u - u') + r₃ * w) + w * Dv * (r₂ * y₀ * b) := by
    rw [hG, hE, hDv]; linear_combination (r₁ * r₂ * (r₂ * y₀ * b)) * hs
  have hα : 0 < r₁ * x₀ * a := by positivity
  have hβ : 0 < r₂ * y₀ * b := by positivity
  have hDn : Dv < 0 := hD
  have fin : ∀ K R : ℝ, 0 < K → K * G = R → (R ≤ 0 → G ≤ 0) ∧ (R < 0 → G < 0) := by
    intro K R hK hKG
    constructor
    · intro hR; by_contra hc; push_neg at hc; have := mul_pos hK hc; linarith
    · intro hR; by_contra hc; push_neg at hc; have := mul_nonneg hK.le hc; linarith
  have hGle : G ≤ 0 ∧ (0 < w → G < 0) := by
    rcases hk with hk | ⟨hv', hk⟩ | ⟨hu', hk⟩
    · have h1 : q₁ * r₁ * r₂ * G = w * Dv * (r₁ * x₀ * a) := by rw [id1, hk]; ring
      have f := fin _ _ (by positivity) h1
      refine ⟨f.1 ?_, fun hw' => f.2 ?_⟩
      · have := mul_nonpos_of_nonpos_of_nonneg hDn.le (mul_nonneg hw hα.le); linarith
      · have := mul_neg_of_neg_of_pos hDn (mul_pos hw' hα); linarith
    · have h1 : q₁ * r₁ * r₂ * G = -(r₁ * E * (r₂ * v + r₄ * w)) + w * Dv * (r₁ * x₀ * a) := by
        rw [id1, hv', sub_zero]
      have h2 : 0 ≤ r₁ * E * (r₂ * v + r₄ * w) := by positivity
      have f := fin _ _ (by positivity) h1
      refine ⟨f.1 ?_, fun hw' => f.2 ?_⟩
      · have := mul_nonpos_of_nonpos_of_nonneg hDn.le (mul_nonneg hw hα.le); linarith
      · have := mul_neg_of_neg_of_pos hDn (mul_pos hw' hα); linarith
    · have h1 : q₂ * r₁ * r₂ * G = r₂ * E * (r₁ * u + r₃ * w) + w * Dv * (r₂ * y₀ * b) := by
        rw [id2, hu', sub_zero]
      have h2 : r₂ * E * (r₁ * u + r₃ * w) ≤ 0 := by
        have h3 : 0 ≤ r₁ * u + r₃ * w := by positivity
        have := mul_nonpos_of_nonpos_of_nonneg hk h3
        have := mul_nonpos_of_nonneg_of_nonpos hr₂.le this
        linarith
      have f := fin _ _ (by positivity) h1
      refine ⟨f.1 ?_, fun hw' => f.2 ?_⟩
      · have := mul_nonpos_of_nonpos_of_nonneg hDn.le (mul_nonneg hw hβ.le); linarith
      · have := mul_neg_of_neg_of_pos hDn (mul_pos hw' hβ); linarith
  exact ⟨by linarith [hGle.1], fun hw' => by linarith [hGle.2 hw']⟩

lemma cgm_Ioi_eq : Ioi (0:ℝ) = ⋃ n : ℕ, Ioc 0 (n : ℝ) := by
  ext t
  simp only [mem_Ioi, mem_iUnion, mem_Ioc]
  constructor
  · intro ht
    obtain ⟨n, hn⟩ := exists_nat_ge t
    exact ⟨n, ht, hn⟩
  · rintro ⟨n, ht, _⟩; exact ht

lemma cgm_dir : Directed (· ⊆ ·) (fun n : ℕ => Ioc (0:ℝ) (n : ℝ)) :=
  Monotone.directed_le fun a b hab => Ioc_subset_Ioc_right (Nat.cast_le.2 hab)

lemma cgm_lim {g : ℝ → ℝ} {K : ENNReal} {C c : ℝ} (hc : 0 < c) (N₀ : ℕ)
    (hb : ∀ n N : ℕ, n ≤ N → N₀ ≤ N → ∫⁻ t in Ioc 0 (n:ℝ), ENNReal.ofReal (g t) ≤
      ENNReal.ofReal (C * Real.exp (-(c * N))) + K) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (g t) ≤ K := by
  rw [cgm_Ioi_eq, setLIntegral_iUnion_of_directed _ cgm_dir]
  refine iSup_le fun n => ?_
  have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal (C * Real.exp (-(c * N))) + K)
      atTop (𝓝 (0 + K)) := by
    refine Tendsto.add ?_ tendsto_const_nhds
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    have h1 : Tendsto (fun N : ℕ => c * (N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hc
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
    simpa using h2
  rw [zero_add] at hlim
  exact ge_of_tendsto hlim (eventually_atTop.2 ⟨max n N₀, fun N hN =>
    hb n N (le_of_max_le_left hN) (le_of_max_le_right hN)⟩)

lemma cgm_M {q₁ q₂ r₁ r₂ x₀ y₀ : ℝ} (hq₁ : 0 < q₁) (hq₂ : 0 < q₂) (hr₁ : 0 < r₁)
    (hr₂ : 0 < r₂) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) {φ : ℝ → ℝ} (hφ : TwoAdmissible φ)
    (hrule : FollowsIndexRule q₁ q₂ r₁ r₂ x₀ y₀ φ) :
    ∃ m : ℝ → ℝ, Continuous m ∧ (∀ s, |m s| ≤ x₀ + y₀) ∧
      (∀ s, 0 ≤ s → ENNReal.ofReal (∫ σ in (0:ℝ)..s, m σ) ≤
        goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ)) ∧
      (∀ s, 0 ≤ s → ∃ t', 0 ≤ t' ∧ cgmQ q₁ q₂ φ t' = s ∧
        m s = Real.exp (-s) * cgmH r₁ r₂ x₀ y₀ (cgmΦ φ t') (t' - cgmΦ φ t')) ∧
      goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ) ≤ ENNReal.ofReal (2 * (x₀ + y₀)) ∧
      (∀ s, 0 < s → 0 < m s) := by
  set c := min q₁ q₂ with hc
  have hc0 : 0 < c := lt_min hq₁ hq₂
  set Q := cgmQ q₁ q₂ φ with hQdef
  have hΦc := (cgm_Φ_lip hφ).continuous
  have hmono : StrictMono Q := by
    intro s t hst
    have := cgm_Q_mono hq₁.le hq₂.le hφ hst.le
    nlinarith [mul_pos hc0 (sub_pos.2 hst)]
  have hQc : Continuous Q := by rw [hQdef]; unfold cgmQ; fun_prop
  have hQ0 : Q 0 = 0 := cgm_Q_zero q₁ q₂ φ
  have hsurj : Function.Surjective Q := by
    intro s
    set R := |s| / c
    have hR : 0 ≤ R := by positivity
    have hcR : c * R = |s| := by simp only [R]; field_simp
    have hm1 : c * (R - 0) ≤ Q R - Q 0 := cgm_Q_mono hq₁.le hq₂.le hφ hR
    have hm2 : c * (0 - -R) ≤ Q 0 - Q (-R) := cgm_Q_mono hq₁.le hq₂.le hφ (by linarith)
    have h1 : |s| ≤ Q R := by rw [hQ0] at hm1; linarith
    have h2 : Q (-R) ≤ -|s| := by rw [hQ0] at hm2; linarith
    have hs : s ∈ Icc (Q (-R)) (Q R) := ⟨by linarith [neg_abs_le s], by linarith [le_abs_self s]⟩
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (by linarith) hQc.continuousOn hs
    exact ⟨t, ht⟩
  set e := hmono.orderIsoOfSurjective Q hsurj
  set τ : ℝ → ℝ := fun s => e.symm s
  have hτQ : ∀ t, τ (Q t) = t := fun t => e.symm_apply_apply t
  have hQτ : ∀ s, Q (τ s) = s := fun s => e.apply_symm_apply s
  have hτc : Continuous τ := e.symm.continuous
  have hτnn : ∀ s, 0 ≤ s → 0 ≤ τ s := by
    intro s hs
    rw [← hmono.le_iff_le, hQτ, hQ0]; exact hs
  set m : ℝ → ℝ := fun s => cgmH r₁ r₂ x₀ y₀ (cgmΦ φ (τ (max s 0)))
      (τ (max s 0) - cgmΦ φ (τ (max s 0))) * Real.exp (-(max s 0)) with hmdef
  have hm : Continuous m := by rw [hmdef]; unfold cgmH; fun_prop
  have hHb : ∀ s, 0 ≤ cgmH r₁ r₂ x₀ y₀ (cgmΦ φ (τ (max s 0)))
      (τ (max s 0) - cgmΦ φ (τ (max s 0))) ∧ cgmH r₁ r₂ x₀ y₀ (cgmΦ φ (τ (max s 0)))
      (τ (max s 0) - cgmΦ φ (τ (max s 0))) ≤ x₀ + y₀ := by
    intro s
    have ht := hτnn (max s 0) (le_max_right _ _)
    have hb := cgm_Φ_nonneg hφ ht
    exact cgm_H_bounds hr₁ hr₂ hx₀.le hy₀.le hb.1 (show 0 ≤ τ (max s 0) - cgmΦ φ (τ (max s 0))
      by linarith [hb.2])
  have hB : ∀ s, |m s| ≤ x₀ + y₀ := by
    intro s
    have hH := hHb s
    have he1 : Real.exp (-(max s 0)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [le_max_right s 0])
    have he0 := Real.exp_pos (-(max s 0))
    rw [abs_le]
    constructor <;> simp only [hmdef] <;> nlinarith [mul_le_mul_of_nonneg_left he1 hH.1]
  have hmφ : ∀ t, 0 ≤ t → m (cgmQ q₁ q₂ φ t) = Real.exp (-(cgmQ q₁ q₂ φ t)) *
      cgmH r₁ r₂ x₀ y₀ (cgmΦ φ t) (t - cgmΦ φ t) := by
    intro t ht
    have hQt : 0 ≤ Q t := by rw [← hQ0]; exact hmono.monotone ht
    simp only [hmdef, ← hQdef, max_eq_left hQt, hτQ]
    ring
  set S := goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice φ)
  have hFS : ∀ s, 0 ≤ s → ENNReal.ofReal (∫ σ in (0:ℝ)..s, m σ) ≤ S := by
    intro s hs
    have ht' := hτnn s hs
    have heq := cgm_lint_eq hq₁ hq₂ hr₁ hr₂ hx₀.le hy₀.le hφ hm (x₀ + y₀) hB hmφ (τ s) ht'
    have hb := cgm_Φ_nonneg hφ ht'
    have hH := cgm_H_bounds hr₁ hr₂ hx₀.le hy₀.le hb.1
      (show 0 ≤ τ s - cgmΦ φ (τ s) by linarith [hb.2])
    calc ENNReal.ofReal (∫ σ in (0:ℝ)..s, m σ)
        ≤ ENNReal.ofReal (cgmΨ q₁ q₂ r₁ r₂ x₀ y₀ φ m (τ s)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [cgm_Ψ_eq, ← hQdef, hQτ]
          have := mul_nonneg (Real.exp_pos (-s)).le hH.1
          linarith
      _ = _ := heq.symm
      _ ≤ S := lintegral_mono_set Ioc_subset_Ioi_self
  have hcmp : ∀ s, 0 ≤ s → ∃ t', 0 ≤ t' ∧ cgmQ q₁ q₂ φ t' = s ∧
      m s = Real.exp (-s) * cgmH r₁ r₂ x₀ y₀ (cgmΦ φ t') (t' - cgmΦ φ t') := by
    intro s hs
    refine ⟨τ s, hτnn s hs, hQτ s, ?_⟩
    simp only [hmdef, max_eq_left hs]
    ring
  have hFle : ∀ s, 0 ≤ s → ∫ σ in (0:ℝ)..s, m σ ≤ x₀ + y₀ := by
    intro s hs
    have h1 : ∫ σ in (0:ℝ)..s, m σ ≤ ∫ σ in (0:ℝ)..s, (x₀ + y₀) * Real.exp (-σ) := by
      apply intervalIntegral.integral_mono_on hs (hm.intervalIntegrable _ _)
        ((by fun_prop : Continuous fun σ : ℝ => (x₀ + y₀) * Real.exp (-σ)).intervalIntegrable _ _)
      intro σ hσ
      simp only [hmdef, max_eq_left hσ.1]
      have := (hHb σ).2
      simp only [max_eq_left hσ.1] at this
      exact mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
    have h2 : ∫ σ in (0:ℝ)..s, (x₀ + y₀) * Real.exp (-σ) = (x₀ + y₀) * (1 - Real.exp (-s)) := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_comp_neg (fun x => Real.exp x)]
      simp [integral_exp]
    have h3 := Real.exp_pos (-s)
    nlinarith
  have hSfin : S ≤ ENNReal.ofReal (2 * (x₀ + y₀)) := by
    show ∫⁻ t in Ioi (0:ℝ), _ ≤ _
    rw [cgm_Ioi_eq, setLIntegral_iUnion_of_directed _ cgm_dir]
    refine iSup_le fun n => ?_
    rw [cgm_lint_eq hq₁ hq₂ hr₁ hr₂ hx₀.le hy₀.le hφ hm (x₀ + y₀) hB hmφ n (Nat.cast_nonneg n)]
    apply ENNReal.ofReal_le_ofReal
    rw [cgm_Ψ_eq]
    have hb := cgm_Φ_nonneg hφ (Nat.cast_nonneg n)
    have hH := cgm_H_bounds hr₁ hr₂ hx₀.le hy₀.le hb.1
      (show 0 ≤ (n:ℝ) - cgmΦ φ n by linarith [hb.2])
    have hQn : 0 ≤ cgmQ q₁ q₂ φ n := by
      rw [← hQ0]; exact hmono.monotone (Nat.cast_nonneg n)
    have he : Real.exp (-cgmQ q₁ q₂ φ n) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have := hFle _ hQn
    nlinarith [mul_le_mul_of_nonneg_right he hH.1, Real.exp_pos (-cgmQ q₁ q₂ φ n)]
  have hmpos : ∀ s, 0 < s → 0 < m s := by
    intro s hs
    obtain ⟨t', ht', hQt', hms⟩ := hcmp s hs.le
    rw [hms]
    apply mul_pos (Real.exp_pos _)
    have ht'pos : 0 < t' := by
      rcases ht'.lt_or_eq with h | h
      · exact h
      · rw [← h, ← hQdef, hQ0] at hQt'; linarith
    have hb := cgm_Φ_nonneg hφ ht'
    unfold cgmH
    rcases (lt_or_ge 0 (cgmΦ φ t')) with hu | hu
    · have h1 : Real.exp (-(r₁ * cgmΦ φ t')) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
      have h2 : Real.exp (-(r₂ * (t' - cgmΦ φ t'))) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [hb.2])
      nlinarith [mul_pos hx₀ (sub_pos.2 h1), mul_nonneg hy₀.le (sub_nonneg.2 h2)]
    · have hv : 0 < t' - cgmΦ φ t' := by linarith
      have h1 : Real.exp (-(r₂ * (t' - cgmΦ φ t'))) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
      have h2 : Real.exp (-(r₁ * cgmΦ φ t')) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hb.1])
      nlinarith [mul_pos hy₀ (sub_pos.2 h1), mul_nonneg hx₀.le (sub_nonneg.2 h2)]
  exact ⟨m, hm, hB, hFS, hcmp, hSfin, hmpos⟩

lemma cgm_rate_P (P : Params) {x₀ y₀ : ℝ} {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) (t : ℝ) :
    goldRate P x₀ y₀ (twoChoice φ₁) t =
      goldRate (Params.two P.q₁ P.q₂ P.r₁ P.r₂) x₀ y₀ (twoChoice φ₁) t := by
  rw [cgm_rate h]
  simp only [goldRate, survival, stateX, stateY, Fin.sum_univ_three, cgm_cum0, cgm_cum1 h,
    cgm_cum2, Params.q, Params.a, Params.b, twoChoice,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring_nf

lemma cgm_gold_P (P : Params) {x₀ y₀ : ℝ} {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) :
    goldInfty P x₀ y₀ (twoChoice φ₁) =
      goldInfty (Params.two P.q₁ P.q₂ P.r₁ P.r₂) x₀ y₀ (twoChoice φ₁) := by
  unfold goldInfty
  congr 1; funext t; rw [cgm_rate_P P h]

lemma cgm_adm_two {φ₁ : ℝ → ℝ} (h : TwoAdmissible φ₁) : Admissible (twoChoice φ₁) := by
  refine ⟨fun i => ?_, fun i t => ?_, fun t => ?_⟩
  · fin_cases i
    · exact h.1
    · exact measurable_const.sub h.1
    · exact measurable_const
  · have := h.2 t
    fin_cases i <;> simp [twoChoice] <;> linarith [this.1, this.2]
  · simp [twoChoice, Fin.sum_univ_three]

lemma cgm3_Lq_ge (P : Params) (hP : P.Positive) {φ : Control} (h : Admissible φ) {t : ℝ}
    (ht : 0 ≤ t) : min P.q₁ (min P.q₂ P.q₃) * t ≤ cgmL P.q φ t := by
  obtain ⟨hq1, hq2, hq3, -, -, -, -⟩ := hP
  have hs := cgm3_cum_sum h t
  have b0 := (cgm3_cum_bounds h 0 ht); have b1 := (cgm3_cum_bounds h 1 ht)
  have b2 := (cgm3_cum_bounds h 2 ht)
  simp only [cgm3_cum_zero, sub_zero] at b0 b1 b2
  simp only [Fin.sum_univ_three] at hs
  simp only [cgmL, Fin.sum_univ_three, Params.q, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have m1 := min_le_left P.q₁ (min P.q₂ P.q₃)
  have m2 := (min_le_right P.q₁ (min P.q₂ P.q₃)).trans (min_le_left P.q₂ P.q₃)
  have m3 := (min_le_right P.q₁ (min P.q₂ P.q₃)).trans (min_le_right P.q₂ P.q₃)
  nlinarith [mul_le_mul_of_nonneg_right m1 b0.1, mul_le_mul_of_nonneg_right m2 b1.1,
    mul_le_mul_of_nonneg_right m3 b2.1]

lemma cgm3_key (P : Params) (hP : P.Positive) (hD : D P < 0) {x₀ y₀ : ℝ} (hx₀ : 0 < x₀)
    (hy₀ : 0 < y₀) {φ₁ : ℝ → ℝ} (h1 : TwoAdmissible φ₁)
    (hr1 : FollowsIndexRule P.q₁ P.q₂ P.r₁ P.r₂ x₀ y₀ φ₁) {ψ : Control} (hψ : Admissible ψ) :
    goldInfty P x₀ y₀ ψ ≤ goldInfty P x₀ y₀ (twoChoice φ₁) ∧
    ((∃ t₀, 0 ≤ t₀ ∧ 0 < cumTime ψ 2 t₀) →
      goldInfty P x₀ y₀ ψ < goldInfty P x₀ y₀ (twoChoice φ₁)) := by
  have hP' := hP
  obtain ⟨hq1, hq2, hq3, hr1', hr2, hr3, hr4⟩ := hP'
  obtain ⟨m, hm, hB, hFS, hcmp, hSfin, hmpos⟩ :=
    cgm_M hq1 hq2 hr1' hr2 hx₀ hy₀ h1 hr1
  rw [cgm_gold_P P h1]
  set S := goldInfty (Params.two P.q₁ P.q₂ P.r₁ P.r₂) x₀ y₀ (twoChoice φ₁)
  set c := min P.q₁ (min P.q₂ P.q₃) with hc
  have hc0 : 0 < c := lt_min hq1 (lt_min hq2 hq3)
  -- the gap and its strict positivity
  have hgap : ∀ t, 0 ≤ t → 0 ≤ cgm3gap P x₀ y₀ ψ m t ∧
      (0 < cumTime ψ 2 t → 0 < cgm3gap P x₀ y₀ ψ m t) := by
    intro t ht
    have hs0 : 0 ≤ cgmL P.q ψ t := le_trans (by positivity) (cgm3_Lq_ge P hP hψ ht)
    obtain ⟨t', ht', hQt', hms⟩ := hcmp _ hs0
    have b0 := (cgm3_cum_bounds hψ 0 ht); have b1 := (cgm3_cum_bounds hψ 1 ht)
    have b2 := (cgm3_cum_bounds hψ 2 ht)
    simp only [cgm3_cum_zero, sub_zero] at b0 b1 b2
    have hb := cgm_Φ_nonneg h1 ht'
    have hkk := cgm_index_kkt hq1 hq2 hr1' hr2 hx₀.le hy₀.le h1 hr1 t' ht'
    simp only [cgmE] at hkk
    have hDv : P.q₁ * P.r₂ * P.r₃ + P.q₂ * P.r₁ * P.r₄ - P.q₃ * P.r₁ * P.r₂ < 0 := hD
    have hsum : P.q₁ * cumTime ψ 0 t + P.q₂ * cumTime ψ 1 t + P.q₃ * cumTime ψ 2 t =
        P.q₁ * cgmΦ φ₁ t' + P.q₂ * (t' - cgmΦ φ₁ t') := by
      have := hQt'
      simp only [cgmQ] at this
      rw [this]
      simp [cgmL, Fin.sum_univ_three, Params.q]
    have K := cgm_kkt3 hq1 hq2 hr1' hr2 hr3 hr4 hx₀ hy₀ b0.1 b1.1 b2.1 hDv hsum hkk
    have hA : cgmL P.a ψ t = P.r₁ * cumTime ψ 0 t + P.r₃ * cumTime ψ 2 t := by
      simp [cgmL, Fin.sum_univ_three, Params.a]
    have hBb : cgmL P.b ψ t = P.r₂ * cumTime ψ 1 t + P.r₄ * cumTime ψ 2 t := by
      simp [cgmL, Fin.sum_univ_three, Params.b]
    unfold cgm3gap
    rw [hms, hA, hBb]
    have he := Real.exp_pos (-cgmL P.q ψ t)
    constructor
    · have := mul_le_mul_of_nonneg_left K.1 he.le; linarith
    · intro hw
      have := mul_lt_mul_of_pos_left (K.2 hw) he; linarith
  have hgapc : Continuous (cgm3gap P x₀ y₀ ψ m) := by
    have h1 : Continuous (cgmL P.q ψ) := (cgm3_lin_lip hψ P.q).continuous
    have h2 : Continuous (cgmL P.a ψ) := (cgm3_lin_lip hψ P.a).continuous
    have h3 : Continuous (cgmL P.b ψ) := (cgm3_lin_lip hψ P.b).continuous
    unfold cgm3gap
    exact (hm.comp h1).sub (by fun_prop)
  have hQ'nn : ∀ t, 0 ≤ ∑ i, P.q i * ψ i t := by
    intro t
    apply Finset.sum_nonneg; intro i _
    have : 0 ≤ P.q i := by fin_cases i <;> simp [Params.q] <;> linarith
    exact mul_nonneg this (hψ.2.1 i t)
  have hQ'ge : ∀ t, c ≤ ∑ i, P.q i * ψ i t := by
    intro t
    have hs := hψ.2.2 t
    simp only [Fin.sum_univ_three] at hs ⊢
    simp only [Params.q, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    have m1 := min_le_left P.q₁ (min P.q₂ P.q₃)
    have m2 := (min_le_right P.q₁ (min P.q₂ P.q₃)).trans (min_le_left P.q₂ P.q₃)
    have m3 := (min_le_right P.q₁ (min P.q₂ P.q₃)).trans (min_le_right P.q₂ P.q₃)
    nlinarith [mul_le_mul_of_nonneg_right m1 (hψ.2.1 0 t), mul_le_mul_of_nonneg_right m2
      (hψ.2.1 1 t), mul_le_mul_of_nonneg_right m3 (hψ.2.1 2 t)]
  have hgint : ∀ T, IntervalIntegrable
      (fun t => (∑ i, P.q i * ψ i t) * cgm3gap P x₀ y₀ ψ m t) volume 0 T := by
    intro T
    have : (fun t => ∑ i, P.q i * ψ i t) =
        fun t => P.q 0 * ψ 0 t + P.q 1 * ψ 1 t + P.q 2 * ψ 2 t :=
      funext fun t => Fin.sum_univ_three _
    have hQi : IntervalIntegrable (fun t => ∑ i, P.q i * ψ i t) volume 0 T := by
      rw [this]
      exact (((cgm3_ii hψ 0 0 T).const_mul _).add ((cgm3_ii hψ 1 0 T).const_mul _)).add
        ((cgm3_ii hψ 2 0 T).const_mul _)
    exact hQi.mul_continuousOn hgapc.continuousOn
  -- basic bound
  have hbase : ∀ T, 0 ≤ T → ∫⁻ t in Ioc 0 T, ENNReal.ofReal (goldRate P x₀ y₀ ψ t) ≤
      ENNReal.ofReal ((x₀ + y₀) * Real.exp (-(c * T)) + (∫ σ in (0:ℝ)..(cgmL P.q ψ T), m σ) -
        ∫ t in (0:ℝ)..T, (∑ i, P.q i * ψ i t) * cgm3gap P x₀ y₀ ψ m t) := by
    intro T hT
    rw [cgm3_lint_gap P hP hx₀.le hy₀.le hψ hm (x₀ + y₀) hB T hT]
    apply ENNReal.ofReal_le_ofReal
    unfold cgm3Ψ
    have hQT := cgm3_Lq_ge P hP hψ hT
    have he : Real.exp (-cgmL P.q ψ T) ≤ Real.exp (-(c * T)) := Real.exp_le_exp.2 (by linarith)
    have b0 := (cgm3_cum_bounds hψ 0 hT); have b1 := (cgm3_cum_bounds hψ 1 hT)
    have b2 := (cgm3_cum_bounds hψ 2 hT)
    simp only [cgm3_cum_zero, sub_zero] at b0 b1 b2
    have hA : 0 ≤ cgmL P.a ψ T := by
      simp only [cgmL, Fin.sum_univ_three, Params.a, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_mul, add_zero]
      have := mul_nonneg hr1'.le b0.1; have := mul_nonneg hr3.le b2.1
      linarith
    have hBb : 0 ≤ cgmL P.b ψ T := by
      simp only [cgmL, Fin.sum_univ_three, Params.b, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, zero_mul, zero_add]
      have := mul_nonneg hr2.le b1.1; have := mul_nonneg hr4.le b2.1
      linarith
    have hH := cgm_H_bounds (r₁ := 1) (r₂ := 1) one_pos one_pos hx₀.le hy₀.le hA hBb
    simp only [cgmH, one_mul] at hH
    have key := mul_le_mul he hH.2 hH.1 (Real.exp_pos _).le
    rw [mul_comm (Real.exp (-(c * T)))] at key
    exact sub_le_sub_right (add_le_add key le_rfl) _
  have hFS' : ∀ s, 0 ≤ s → ∫ σ in (0:ℝ)..s, m σ ≤ S.toReal := by
    intro s hs
    exact (ENNReal.ofReal_le_iff_le_toReal (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSfin)).1
      (hFS s hs)
  have hSne : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hSfin
  have hQnn : ∀ T, 0 ≤ T → 0 ≤ cgmL P.q ψ T := fun T hT =>
    le_trans (by positivity) (cgm3_Lq_ge P hP hψ hT)
  constructor
  · apply cgm_lim hc0 0
    intro n N hnN _
    refine (lintegral_mono_set (Ioc_subset_Ioc_right (Nat.cast_le.2 hnN))).trans ?_
    refine (hbase N (Nat.cast_nonneg N)).trans ?_
    have hint0 : 0 ≤ ∫ t in (0:ℝ)..N, (∑ i, P.q i * ψ i t) * cgm3gap P x₀ y₀ ψ m t :=
      intervalIntegral.integral_nonneg (Nat.cast_nonneg N)
        (fun t ht => mul_nonneg (hQ'nn t) (hgap t ht.1).1)
    refine le_trans (ENNReal.ofReal_le_ofReal (?_ : _ ≤ (x₀ + y₀) * Real.exp (-(c * N)) +
        ∫ σ in (0:ℝ)..(cgmL P.q ψ N), m σ)) ?_
    · apply sub_le_self
      exact intervalIntegral.integral_nonneg (Nat.cast_nonneg N)
        (fun t ht => mul_nonneg (hQ'nn t) (hgap t ht.1).1)
    · exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl
          (hFS _ (hQnn _ (Nat.cast_nonneg N))))
  · rintro ⟨t₀, ht₀, hw₀⟩
    have hwpos : ∀ t ∈ Icc t₀ (t₀ + 1), 0 < cgm3gap P x₀ y₀ ψ m t := by
      intro t ht
      have := cgm3_cum_bounds hψ 2 ht.1
      exact (hgap t (by linarith [ht.1])).2 (by linarith [this.1])
    obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn
      (nonempty_Icc.2 (by linarith : t₀ ≤ t₀ + 1)) hgapc.continuousOn
    set δ := cgm3gap P x₀ y₀ ψ m t₁
    have hδ : 0 < δ := hwpos t₁ ht₁
    have hlow : ∀ T, t₀ + 1 ≤ T →
        c * δ ≤ ∫ t in (0:ℝ)..T, (∑ i, P.q i * ψ i t) * cgm3gap P x₀ y₀ ψ m t := by
      intro T hT
      have hnn : 0 ≤ᵐ[volume.restrict (Ioc 0 T)]
          fun t => (∑ i, P.q i * ψ i t) * cgm3gap P x₀ y₀ ψ m t := by
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        exact ae_of_all _ fun t ht => mul_nonneg (hQ'nn t) (hgap t ht.1.le).1
      have h1 := intervalIntegral.integral_mono_interval ht₀ (by linarith : t₀ ≤ t₀ + 1) hT
        hnn (hgint T)
      have hsub : IntervalIntegrable (fun t => (∑ i, P.q i * ψ i t) * cgm3gap P x₀ y₀ ψ m t)
          volume t₀ (t₀ + 1) :=
        (hgint T).mono_set (by
          rw [uIcc_of_le (by linarith), uIcc_of_le (by linarith)]
          exact Icc_subset_Icc ht₀ hT)
      have h2 := intervalIntegral.integral_mono_on (by linarith : t₀ ≤ t₀ + 1)
        (intervalIntegrable_const (c := c * δ)) hsub (fun t ht =>
          mul_le_mul (hQ'ge t) (hmin ht) hδ.le (hQ'nn t))
      simp only [intervalIntegral.integral_const, smul_eq_mul] at h2
      linarith
    have hSpos : 0 < S.toReal := by
      have := hFS' 1 zero_le_one
      have hpos : 0 < ∫ σ in (0:ℝ)..1, m σ :=
        intervalIntegral.intervalIntegral_pos_of_pos_on (hm.intervalIntegrable _ _)
          (fun x hx => hmpos x hx.1) zero_lt_one
      linarith
    have hle : ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (goldRate P x₀ y₀ ψ t) ≤
        ENNReal.ofReal (S.toReal - c * δ) := by
      apply cgm_lim hc0 (⌈t₀ + 1⌉₊)
      intro n N hnN hN
      have hN' : t₀ + 1 ≤ (N : ℝ) := (Nat.le_ceil _).trans (Nat.cast_le.2 hN)
      refine (lintegral_mono_set (Ioc_subset_Ioc_right (Nat.cast_le.2 hnN))).trans ?_
      refine (hbase N (Nat.cast_nonneg N)).trans ?_
      have := hlow N hN'
      have := hFS' _ (hQnn _ (Nat.cast_nonneg N))
      refine le_trans (ENNReal.ofReal_le_ofReal (?_ : _ ≤ (x₀ + y₀) * Real.exp (-(c * N)) +
        (S.toReal - c * δ))) ENNReal.ofReal_add_le
      linarith
    refine lt_of_le_of_lt hle ?_
    rw [← ENNReal.ofReal_toReal hSne, ENNReal.ofReal_lt_ofReal_iff hSpos]
    have := mul_pos hc0 hδ
    rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    linarith

theorem theorem8_core (P : Params) (hP : P.Positive) (hr : P.r₄ < P.r₃)
    (hD : D P < 0) (x₀ y₀ : ℝ) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    (∃ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ ∧ FollowsIndexRule P.q₁ P.q₂ P.r₁ P.r₂ x₀ y₀ φ₁) ∧
    (∀ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ → FollowsIndexRule P.q₁ P.q₂ P.r₁ P.r₂ x₀ y₀ φ₁ →
      IsOptimalInfty P x₀ y₀ (twoChoice φ₁)) ∧
    ∀ φ : Control, IsOptimalInfty P x₀ y₀ φ →
      ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))), φ 2 t = 0 := by
  have hP' := hP
  obtain ⟨hq1, hq2, hq3, hr1', hr2, hr3, hr4⟩ := hP'
  have hex := cgm_exists hq1 hq2 hr1' hr2 hx₀.le hy₀.le (x₀ := x₀) (y₀ := y₀)
  refine ⟨hex, fun φ₁ h1 hrl => ⟨cgm_adm_two h1, fun ψ hψ =>
    (cgm3_key P hP hD hx₀ hy₀ h1 hrl hψ).1⟩, fun φ hopt => ?_⟩
  obtain ⟨φ₁, h1, hrl⟩ := hex
  have hz : ∀ t, 0 ≤ t → cumTime φ 2 t = 0 := by
    intro t ht
    by_contra hne
    have hb := cgm3_cum_bounds hopt.1 2 ht
    rw [cgm3_cum_zero, sub_zero] at hb
    have hpos : 0 < cumTime φ 2 t := lt_of_le_of_ne hb.1 (Ne.symm hne)
    have h2 := (cgm3_key P hP hD hx₀ hy₀ h1 hrl hopt.1).2 ⟨t, ht, hpos⟩
    have h3 := hopt.2 _ (cgm_adm_two h1)
    exact absurd h3 (not_le.2 h2)
  have hn : ∀ n : ℕ, ∀ᵐ t, t ∈ Ioc 0 (n : ℝ) → φ 2 t = 0 := by
    intro n
    have hint : IntegrableOn (φ 2) (Ioc 0 (n:ℝ)) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg n)).1
        (cgm3_ii hopt.1 2 0 n)
    have h0 : ∫ t in Ioc 0 (n:ℝ), φ 2 t = 0 := by
      rw [← intervalIntegral.integral_of_le (Nat.cast_nonneg n)]
      exact hz n (Nat.cast_nonneg n)
    have := (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ (fun t => hopt.1.2.1 2 t)) hint).1 h0
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at this
    exact this
  rw [← ae_all_iff] at hn
  have h0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
  rw [ae_restrict_iff' measurableSet_Ici]
  filter_upwards [hn, h0] with t ht ht0 htI
  obtain ⟨n, hn⟩ := exists_nat_ge t
  exact ht n ⟨lt_of_le_of_ne htI (Ne.symm ht0), hn⟩
end BellmanDP.ContGoldMining

open BellmanDP.ContGoldMining
open MeasureTheory

theorem solution (P : Params) (hP : P.Positive) (hr : P.r₄ < P.r₃)
    (hD : D P < 0) (x₀ y₀ : ℝ) (hx₀ : 0 < x₀) (hy₀ : 0 < y₀) :
    (∃ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ ∧ FollowsIndexRule P.q₁ P.q₂ P.r₁ P.r₂ x₀ y₀ φ₁) ∧
    (∀ φ₁ : ℝ → ℝ, TwoAdmissible φ₁ → FollowsIndexRule P.q₁ P.q₂ P.r₁ P.r₂ x₀ y₀ φ₁ →
      IsOptimalInfty P x₀ y₀ (twoChoice φ₁)) ∧
    ∀ φ : Control, IsOptimalInfty P x₀ y₀ φ →
      ∀ᵐ t ∂(volume.restrict (Set.Ici (0 : ℝ))), φ 2 t = 0 := by
  exact theorem8_core P hP hr hD x₀ y₀ hx₀ hy₀
