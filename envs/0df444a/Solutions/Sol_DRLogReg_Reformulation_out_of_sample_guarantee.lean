-- Prove2me | solution 1 for DRLogReg.Reformulation.out_of_sample_guarantee
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T05:50:39.013617+00:00
-- url     : https://prove2.me/submissions/ef195a97-96fe-46eb-8d18-56fc63ab572b

import Mathlib
import Definitions.Def_DRLogReg_Reformulation_Core
import Definitions.Def_DRLogReg_Reformulation_Program

set_option autoImplicit false

open DRLogReg.Reformulation in
theorem c80dr_sgn_sq (y : Bool) : sgn y * sgn y = 1 := by cases y <;> simp [sgn]

open DRLogReg.Reformulation in
theorem c80dr_abs_sgn (y : Bool) : |sgn y| = 1 := by cases y <;> simp [sgn]

theorem c80dr_softplus_le (a b : ℝ) :
    Real.log (1 + Real.exp a) ≤ Real.log (1 + Real.exp b) + max 0 (a - b) := by
  have h1 : 0 < 1 + Real.exp a := by positivity
  have h2 : 0 < 1 + Real.exp b := by positivity
  rw [← Real.log_exp (max 0 (a - b)), ← Real.log_mul h2.ne' (Real.exp_pos _).ne']
  apply Real.log_le_log h1
  have hm0 : 1 ≤ Real.exp (max 0 (a - b)) := Real.one_le_exp (le_max_left _ _)
  have hm1 : Real.exp a ≤ Real.exp b * Real.exp (max 0 (a - b)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [le_max_right 0 (a - b)]
  nlinarith

theorem c80dr_softplus_ge (a : ℝ) : a ≤ Real.log (1 + Real.exp a) := by
  have := Real.log_le_log (Real.exp_pos a) (show Real.exp a ≤ 1 + Real.exp a by linarith)
  rwa [Real.log_exp] at this

open DRLogReg.Reformulation in
theorem c80dr_logloss_pos {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] ℝ) (x : V) (y : Bool) : 0 < logloss β x y := by
  unfold logloss
  apply Real.log_pos
  linarith [Real.exp_pos (-(sgn y * β x))]

open DRLogReg.Reformulation in
theorem c80dr_dist_same {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (κ : ℝ)
    (x x' : V) (y : Bool) : featureLabelDist κ (x, y) (x', y) = ‖x - x'‖ := by
  simp [featureLabelDist]

open DRLogReg.Reformulation in
theorem c80dr_dist_flip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (κ : ℝ)
    (x x' : V) (y : Bool) : featureLabelDist κ (x, !y) (x', y) = ‖x - x'‖ + κ := by
  cases y <;> norm_num [featureLabelDist, sgn]

open DRLogReg.Reformulation in
theorem c80dr_dist_nonneg {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ : ℝ}
    (hκ : 0 ≤ κ) (ξ ξ' : V × Bool) : 0 ≤ featureLabelDist κ ξ ξ' := by
  unfold featureLabelDist
  positivity

open DRLogReg.Reformulation in
theorem c80dr_lip {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (β : V →L[ℝ] ℝ) (x x' : V) (y : Bool) :
    logloss β x y ≤ logloss β x' y + ‖β‖ * ‖x - x'‖ := by
  unfold logloss
  refine (c80dr_softplus_le (-(sgn y * β x)) (-(sgn y * β x'))).trans ?_
  gcongr
  apply max_le (by positivity)
  have h := β.le_opNorm (x - x')
  rw [Real.norm_eq_abs, map_sub] at h
  have e : -(sgn y * β x) - -(sgn y * β x') = -(sgn y * (β x - β x')) := by ring
  rw [e]
  calc -(sgn y * (β x - β x')) ≤ |sgn y * (β x - β x')| := neg_le_abs _
    _ = |β x - β x'| := by rw [abs_mul, c80dr_abs_sgn, one_mul]
    _ ≤ ‖β‖ * ‖x - x'‖ := h

open DRLogReg.Reformulation in
theorem c80dr_pt {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {κ : ℝ} {N : ℕ}
    {xhat : Fin N → V} {yhat : Fin N → Bool}
    {p : (V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ)} (hp : p ∈ feasible7 κ xhat yhat)
    (i : Fin N) (ξ : V × Bool) :
    logloss p.1 ξ.1 ξ.2 ≤ p.2.2 i + p.2.1 * featureLabelDist κ ξ (xhat i, yhat i) := by
  obtain ⟨h1, h2, h3⟩ := hp
  obtain ⟨x, y⟩ := ξ
  dsimp only
  have hn : 0 ≤ ‖x - xhat i‖ := norm_nonneg _
  have hk : ‖p.1‖ * ‖x - xhat i‖ ≤ p.2.1 * ‖x - xhat i‖ := mul_le_mul_of_nonneg_right h3 hn
  by_cases hy : y = yhat i
  · subst hy
    rw [c80dr_dist_same]
    have e1 := c80dr_lip p.1 x (xhat i) (yhat i)
    have e2 := h1 i
    linarith
  · have hy' : y = !yhat i := by
      cases y <;> cases h : yhat i <;> simp_all
    subst hy'
    rw [c80dr_dist_flip]
    have e1 := c80dr_lip p.1 x (xhat i) (!yhat i)
    have e2 := h2 i
    linarith

open DRLogReg.Reformulation in
theorem c80dr_meas {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] (β : V →L[ℝ] ℝ) : Measurable (fun ξ : V × Bool => logloss β ξ.1 ξ.2) := by
  have h1 : Measurable fun ξ : V × Bool => sgn ξ.2 :=
    (measurable_of_countable sgn).comp measurable_snd
  have h2 : Measurable fun ξ : V × Bool => β ξ.1 := β.continuous.measurable.comp measurable_fst
  unfold logloss
  exact Real.measurable_log.comp (measurable_const.add (Real.measurable_exp.comp (h1.mul h2).neg))

open MeasureTheory DRLogReg.Reformulation in
theorem c80dr_weak {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V]
    [BorelSpace V] {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N) {xhat : Fin N → V}
    {yhat : Fin N → Bool} {p : (V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ)}
    (hp : p ∈ feasible7 κ xhat yhat)
    {Q : Measure (V × Bool)} (hQ : Q ∈ wassersteinBall κ ε (empirical xhat yhat)) :
    ∫⁻ ξ, ENNReal.ofReal (logloss p.1 ξ.1 ξ.2) ∂Q ≤ ENNReal.ofReal (objective7 ε p) := by
  classical
  have hs : ∀ i, 0 ≤ p.2.2 i := fun i => (c80dr_logloss_pos _ _ _).le.trans (hp.1 i)
  have hlam : 0 ≤ p.2.1 := (norm_nonneg _).trans hp.2.2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set C : ℝ := (N : ℝ)⁻¹ * ∑ i, p.2.2 i with hCdef
  have hC : 0 ≤ C := mul_nonneg (inv_nonneg.mpr hNpos.le) (Finset.sum_nonneg fun i _ => hs i)
  have hfm : Measurable (fun ξ : V × Bool => ENNReal.ofReal (logloss p.1 ξ.1 ξ.2)) :=
    (c80dr_meas p.1).ennreal_ofReal
  let g : V × Bool → ENNReal := fun ξ' =>
    ⨅ i, if ξ' = (xhat i, yhat i) then ENNReal.ofReal (p.2.2 i) else ⊤
  have hg : Measurable g :=
    Measurable.iInf fun i => Measurable.ite measurableSet_eq measurable_const measurable_const
  have hgle : ∀ i, g (xhat i, yhat i) ≤ ENNReal.ofReal (p.2.2 i) := fun i =>
    (iInf_le _ i).trans (by simp)
  have hpt : ∀ q : (V × Bool) × (V × Bool), ENNReal.ofReal (logloss p.1 q.1.1 q.1.2) ≤
      g q.2 + ENNReal.ofReal p.2.1 * ENNReal.ofReal (featureLabelDist κ q.1 q.2) := by
    intro q
    simp only [g]
    rw [ENNReal.iInf_add]
    refine le_iInf fun i => ?_
    split_ifs with h
    · rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_add (hs i)
        (mul_nonneg hlam (c80dr_dist_nonneg hκ _ _))]
      apply ENNReal.ofReal_le_ofReal
      rw [h]
      exact c80dr_pt hp i q.1
    · simp
  have hcoup : ∀ π : Measure ((V × Bool) × (V × Bool)), π.map Prod.fst = Q →
      π.map Prod.snd = empirical xhat yhat →
      ∫⁻ ξ, ENNReal.ofReal (logloss p.1 ξ.1 ξ.2) ∂Q ≤ ENNReal.ofReal C + ENNReal.ofReal p.2.1 *
        ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
    intro π h1 h2
    calc ∫⁻ ξ, ENNReal.ofReal (logloss p.1 ξ.1 ξ.2) ∂Q
        = ∫⁻ q, ENNReal.ofReal (logloss p.1 q.1.1 q.1.2) ∂π := by
          rw [← h1, lintegral_map hfm measurable_fst]
      _ ≤ ∫⁻ q, (g q.2 + ENNReal.ofReal p.2.1 *
            ENNReal.ofReal (featureLabelDist κ q.1 q.2)) ∂π :=
          lintegral_mono hpt
      _ = ∫⁻ q, g q.2 ∂π + ENNReal.ofReal p.2.1 *
            ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
          rw [lintegral_add_left (f := fun q : (V × Bool) × (V × Bool) => g q.2)
            (hg.comp measurable_snd), lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal C + ENNReal.ofReal p.2.1 *
            ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := by
          gcongr
          rw [← lintegral_map hg measurable_snd, h2]
          simp only [empirical, lintegral_smul_measure, lintegral_finsetSum_measure,
            lintegral_dirac, smul_eq_mul]
          calc (N : ENNReal)⁻¹ * ∑ i, g (xhat i, yhat i)
              ≤ (N : ENNReal)⁻¹ * ∑ i, ENNReal.ofReal (p.2.2 i) := by
                gcongr with i
                exact hgle i
            _ = ENNReal.ofReal C := by
                rw [hCdef, ENNReal.ofReal_mul (inv_nonneg.mpr hNpos.le),
                  ENNReal.ofReal_sum_of_nonneg (fun i _ => hs i),
                  ENNReal.ofReal_inv_of_pos hNpos, ENNReal.ofReal_natCast]
  have hW := hQ.2
  have hobj : objective7 ε p = p.2.1 * ε + C := rfl
  rw [hobj]
  apply ENNReal.le_of_forall_pos_le_add
  intro δ hδ _
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  set η : ℝ := (δ : ℝ) / (p.2.1 + 1) with hηdef
  have hη : 0 < η := div_pos hδr (by linarith)
  have hlt : wasserstein κ Q (empirical xhat yhat) < ENNReal.ofReal (ε + η) := by
    calc _ ≤ ENNReal.ofReal ε := hW
      _ < ENNReal.ofReal (ε + η) := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  simp only [wasserstein, iInf_lt_iff] at hlt
  obtain ⟨π, _, h1, h2, hcost⟩ := hlt
  have hle : p.2.1 * η ≤ δ := by
    rw [hηdef, mul_div_assoc']
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc ∫⁻ ξ, ENNReal.ofReal (logloss p.1 ξ.1 ξ.2) ∂Q ≤ ENNReal.ofReal C + ENNReal.ofReal p.2.1 *
        ∫⁻ q, ENNReal.ofReal (featureLabelDist κ q.1 q.2) ∂π := hcoup π h1 h2
    _ ≤ ENNReal.ofReal C + ENNReal.ofReal p.2.1 * ENNReal.ofReal (ε + η) := by gcongr
    _ = ENNReal.ofReal (p.2.1 * ε + C + p.2.1 * η) := by
        rw [← ENNReal.ofReal_mul hlam, ← ENNReal.ofReal_add hC (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (p.2.1 * ε + C) + δ := by
        rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_add
          (add_nonneg (mul_nonneg hlam hε) hC) δ.coe_nonneg]
        apply ENNReal.ofReal_le_ofReal
        linarith

open MeasureTheory DRLogReg.Reformulation in
theorem solution
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V]
    {κ ε : ℝ} (hκ : 0 < κ) (hε : 0 ≤ ε) {N : ℕ} (hN : 0 < N)
    (P : Measure (V × Bool)) [IsProbabilityMeasure P]
    (sol : (Fin N → V × Bool) → (V →L[ℝ] ℝ) × ℝ × (Fin N → ℝ))
    (hsol : ∀ ω : Fin N → V × Bool,
      sol ω ∈ feasible7 κ (fun i => (ω i).1) (fun i => (ω i).2) ∧
        ∀ q ∈ feasible7 κ (fun i => (ω i).1) (fun i => (ω i).2),
          objective7 ε (sol ω) ≤ objective7 ε q)
    {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hconf : ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ω | P ∈ wassersteinBall κ ε (empirical (fun i => (ω i).1) (fun i => (ω i).2))}) :
    ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P)
      {ω | ∫⁻ ξ, ENNReal.ofReal (logloss (sol ω).1 ξ.1 ξ.2) ∂P ≤
        ENNReal.ofReal (objective7 ε (sol ω))} := by
  refine hconf.trans (measure_mono ?_)
  intro ω hω
  exact c80dr_weak hκ.le hε hN (hsol ω).1 hω
