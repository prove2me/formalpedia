-- Prove2me | solution 1 for EarlyInspect.Align.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-22T20:19:57.639097+00:00
-- url     : https://prove2.me/submissions/fae35675-f159-4ead-98c7-b1fb59381031

import Mathlib
import Definitions.Def_InventoryControl_newsboy
import Definitions.Def_EarlyInspect_Align_Model

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace EIA2

/-- The Gaussian distribution function written as an integral of its density. -/
noncomputable def Fi (m : ℝ) (v : NNReal) (S : ℝ) : ℝ := ∫ x in Iic S, gaussianPDFReal m v x

lemma pdf_hasDeriv (m : ℝ) (v : NNReal) (x : ℝ) :
    HasDerivAt (gaussianPDFReal m v) (-(x - m) / v * gaussianPDFReal m v x) x := by
  have hb : HasDerivAt (fun y : ℝ => (y - m)) 1 x := by
    simpa using (hasDerivAt_id x).sub_const m
  have hq : HasDerivAt (fun y : ℝ => (y - m) * (y - m)) (1 * (x - m) + (x - m) * 1) x := hb.mul hb
  have hq2 : HasDerivAt (fun y : ℝ => -((y - m) * (y - m)) / (2 * (v : ℝ)))
      (-(1 * (x - m) + (x - m) * 1) / (2 * (v : ℝ))) x := hq.neg.div_const _
  have h2 := hq2.exp.const_mul (√(2 * Real.pi * v))⁻¹
  have hfun : gaussianPDFReal m v = fun y => (√(2 * Real.pi * v))⁻¹ *
      Real.exp (-((y - m) * (y - m)) / (2 * (v : ℝ))) := by
    funext y; simp only [gaussianPDFReal, sq]
  rw [hfun]
  refine h2.congr_deriv ?_
  dsimp only
  by_cases hv : (v : ℝ) = 0
  · simp [hv]
  · field_simp
    ring

lemma pdf_cont (m : ℝ) (v : NNReal) : Continuous (gaussianPDFReal m v) := by
  rw [gaussianPDFReal_def]; fun_prop

lemma Fi_hasDeriv (m : ℝ) (v : NNReal) (S : ℝ) :
    HasDerivAt (Fi m v) (gaussianPDFReal m v S) S := by
  have hint : ∀ a, IntegrableOn (gaussianPDFReal m v) (Iic a) :=
    fun a => (integrable_gaussianPDFReal m v).integrableOn
  have hcont := pdf_cont m v
  have heq : Fi m v = fun u => Fi m v 0 + ∫ x in (0:ℝ)..u, gaussianPDFReal m v x := by
    funext u
    unfold Fi
    rw [← intervalIntegral.integral_Iic_sub_Iic (hint 0) (hint u)]
    ring
  rw [heq]
  exact (intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    (hcont.stronglyMeasurableAtFilter _ _) hcont.continuousAt).const_add _

lemma Fi_nonneg (m : ℝ) (v : NNReal) (S : ℝ) : 0 ≤ Fi m v S :=
  integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _)

lemma real_Iic (m : ℝ) {v : NNReal} (hv : v ≠ 0) (S : ℝ) :
    (gaussianReal m v).real (Iic S) = Fi m v S := by
  rw [Measure.real, gaussianReal_apply_eq_integral m hv, ENNReal.toReal_ofReal
    (integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _))]
  rfl

lemma real_Ici (m : ℝ) {v : NNReal} (hv : v ≠ 0) (S : ℝ) :
    (gaussianReal m v).real (Ici S) = 1 - Fi m v S := by
  rw [Measure.real, gaussianReal_apply_eq_integral m hv, ENNReal.toReal_ofReal
    (integral_nonneg (fun x => gaussianPDFReal_nonneg _ _ _))]
  have h := integral_add_compl (measurableSet_Iio (a := S)) (integrable_gaussianPDFReal m v)
  rw [compl_Iio, integral_gaussianPDFReal_eq_one m hv] at h
  unfold Fi
  rw [integral_Iic_eq_integral_Iio]
  linarith

lemma pdf_tendsto_atBot (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Tendsto (gaussianPDFReal m v) atBot (𝓝 0) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h1 : Tendsto (fun x : ℝ => m + -x) atBot atTop :=
    tendsto_atTop_add_const_left _ m tendsto_neg_atBot_atTop
  have h2 : Tendsto (fun x : ℝ => (m + -x) ^ 2 / (2 * (v : ℝ))) atBot atTop :=
    ((tendsto_pow_atTop (two_ne_zero)).comp h1).atTop_div_const (by positivity)
  have h3 : Tendsto (fun x : ℝ => (√(2 * Real.pi * v))⁻¹ *
      Real.exp (-((m + -x) ^ 2 / (2 * (v : ℝ))))) atBot (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h2)).const_mul
      (√(2 * Real.pi * v))⁻¹
    simpa using this
  refine h3.congr (fun x => ?_)
  rw [gaussianPDFReal_def]
  congr 2
  ring

lemma integrable_lin_pdf (m : ℝ) {v : NNReal} (hv : v ≠ 0) :
    Integrable (fun x : ℝ => (x - m) * gaussianPDFReal m v x) := by
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h := ((integrable_mul_exp_neg_mul_sq (b := 1 / (2 * (v : ℝ))) (by positivity)).comp_sub_right
    m).const_mul (√(2 * Real.pi * v))⁻¹
  refine h.congr (ae_of_all _ (fun x => ?_))
  show (√(2 * Real.pi * v))⁻¹ * ((x - m) * Real.exp (-(1 / (2 * (v : ℝ))) * (x - m) ^ 2)) =
    (x - m) * gaussianPDFReal m v x
  simp only [gaussianPDFReal]
  have : -(1 / (2 * (v : ℝ))) * (x - m) ^ 2 = -(x - m) ^ 2 / (2 * v) := by ring
  rw [this]
  ring

/-- Closed form of the expected overage `E[(S - D)^+]`. -/
lemma G_eq (m : ℝ) {v : NNReal} (hv : v ≠ 0) (S : ℝ) :
    ∫ x, max (S - x) 0 ∂(gaussianReal m v) = v * gaussianPDFReal m v S + (S - m) * Fi m v S := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  have h1 : (fun x => gaussianPDFReal m v x • max (S - x) 0) =
      (Iic S).indicator (fun x => (S - m) * gaussianPDFReal m v x -
        (x - m) * gaussianPDFReal m v x) := by
    funext x
    simp only [smul_eq_mul, Set.indicator_apply, Set.mem_Iic]
    split_ifs with h
    · rw [max_eq_left (by linarith)]; ring
    · rw [max_eq_right (by linarith)]; ring
  have hint1 : IntegrableOn (fun x => (S - m) * gaussianPDFReal m v x) (Iic S) :=
    ((integrable_gaussianPDFReal m v).const_mul _).integrableOn
  have hint2 := integrable_lin_pdf m hv
  rw [h1, integral_indicator measurableSet_Iic, integral_sub hint1 hint2.integrableOn,
    integral_const_mul]
  have hFTC : ∫ x in Iic S, (x - m) * gaussianPDFReal m v x =
      -(v : ℝ) * gaussianPDFReal m v S - 0 := by
    apply integral_Iic_of_hasDerivAt_of_tendsto' (f := fun x => -(v : ℝ) * gaussianPDFReal m v x)
    · intro x _
      refine ((pdf_hasDeriv m v x).const_mul (-(v : ℝ))).congr_deriv ?_
      have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
      field_simp
    · exact hint2.integrableOn
    · have := (pdf_tendsto_atBot m hv).const_mul (-(v : ℝ))
      simpa using this
  rw [hFTC]
  unfold Fi
  ring

lemma Gc_hasDeriv (m : ℝ) {v : NNReal} (hv : v ≠ 0) (S : ℝ) :
    HasDerivAt (fun S => (v : ℝ) * gaussianPDFReal m v S + (S - m) * Fi m v S) (Fi m v S) S := by
  have hm : HasDerivAt (fun y : ℝ => y - m) 1 S := by
    simpa using (hasDerivAt_id S).sub_const m
  refine (((pdf_hasDeriv m v S).const_mul (v : ℝ)).add (hm.mul (Fi_hasDeriv m v S))).congr_deriv ?_
  have hv' : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  field_simp
  ring

lemma integrable_id' (m : ℝ) (v : NNReal) : Integrable (fun x : ℝ => x) (gaussianReal m v) := by
  exact MemLp.integrable le_rfl (memLp_id_gaussianReal' (μ := m) (v := v) 1 ENNReal.one_ne_top)

lemma G_pos (m : ℝ) {v : NNReal} (hv : v ≠ 0) (S : ℝ) :
    0 < ∫ x, max (S - x) 0 ∂(gaussianReal m v) := by
  have hi : Integrable (fun x : ℝ => max (S - x) 0) (gaussianReal m v) :=
    ((integrable_const S).sub (integrable_id' m v)).pos_part
  rw [integral_pos_iff_support_of_nonneg (f := fun x : ℝ => max (S - x) 0)
    (fun x => le_max_right _ _) hi]
  have hsupp : Function.support (fun x : ℝ => max (S - x) 0) = Iio S := by
    ext x
    simp only [Function.mem_support, mem_Iio]
    constructor
    · intro h
      by_contra hx
      exact h (max_eq_right (by linarith))
    · intro h
      rw [max_eq_left (by linarith)]
      linarith
  rw [hsupp, pos_iff_ne_zero]
  intro h
  have h2 := gaussianReal_absolutelyContinuous' m hv h
  simp at h2

lemma Fi_std (μ σ z : ℝ) (hσ : 0 < σ) :
    Fi μ (Real.toNNReal (σ ^ 2)) (μ + z * σ) = EarlyInspect.Align.Φ z := by
  have hv : Real.toNNReal (σ ^ 2) ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  rw [← real_Iic μ hv]
  have hmap : (gaussianReal 0 1).map ((fun x : ℝ => x + μ) ∘ (fun x : ℝ => σ * x)) =
      gaussianReal μ (Real.toNNReal (σ ^ 2)) := by
    rw [← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
      gaussianReal_map_add_const]
    congr 1
    · ring
    · rw [mul_one]
      ext
      simp [Real.coe_toNNReal _ (sq_nonneg σ)]
  rw [← hmap, map_measureReal_apply (by fun_prop) measurableSet_Iic]
  have hset : ((fun x : ℝ => x + μ) ∘ (fun x : ℝ => σ * x)) ⁻¹' Iic (μ + z * σ) = Iic z := by
    ext x
    simp only [mem_preimage, Function.comp, mem_Iic]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  rw [hset, EarlyInspect.Align.Φ, cdf_eq_real]

/-- The inspection-time density at the target level, in standardized form. -/
lemma pY_at (μ σ z s : ℝ) (hσ : 0 < σ) (hs : 0 < s) :
    gaussianPDFReal (s ^ 2 * μ) (Real.toNNReal ((Real.sqrt (s ^ 2) * σ) ^ 2)) (μ + z * σ) =
      EarlyInspect.Align.φ ((μ / σ * (1 - s ^ 2) + z) / Real.sqrt (s ^ 2)) / (s * σ) := by
  rw [Real.sqrt_sq hs.le]
  have e1 : ((Real.toNNReal ((s * σ) ^ 2) : NNReal) : ℝ) = (s * σ) ^ 2 :=
    Real.coe_toNNReal _ (sq_nonneg _)
  simp only [EarlyInspect.Align.φ, gaussianPDFReal_def, e1, NNReal.coe_one, mul_one, sub_zero]
  rw [Real.sqrt_mul (by positivity) ((s * σ) ^ 2), Real.sqrt_sq (by positivity)]
  have hE : -(μ + z * σ - s ^ 2 * μ) ^ 2 / (2 * (s * σ) ^ 2) =
      -((μ / σ * (1 - s ^ 2) + z) / s) ^ 2 / 2 := by
    field_simp
    ring
  rw [hE, mul_inv]
  field_simp

lemma hM_at (μ σ z s : ℝ) (hσ : 0 < σ) (hs : 0 < s) :
    EarlyInspect.Align.incentiveM μ σ z (s ^ 2) *
      gaussianPDFReal (s ^ 2 * μ) (Real.toNNReal ((Real.sqrt (s ^ 2) * σ) ^ 2)) (μ + z * σ) =
      Fi μ (Real.toNNReal (σ ^ 2)) (μ + z * σ) := by
  rw [pY_at μ σ z s hσ hs, Fi_std μ σ z hσ]
  unfold EarlyInspect.Align.incentiveM
  have hφ : 0 < EarlyInspect.Align.φ ((μ / σ * (1 - s ^ 2) + z) / Real.sqrt (s ^ 2)) :=
    gaussianPDFReal_pos _ _ _ one_ne_zero
  rw [Real.sqrt_sq hs.le] at hφ ⊢
  set P := EarlyInspect.Align.φ ((μ / σ * (1 - s ^ 2) + z) / s)
  field_simp

lemma argmin_of_shape (f : ℝ → ℝ) (a I : ℝ) (ha : 0 ≤ a) (hI : 0 ≤ I)
    (h1 : StrictAntiOn f (Icc 0 a)) (h2 : StrictMonoOn f (Ici a)) :
    EarlyInspect.Align.argminFrom f I = {max I a} := by
  have key : ∀ S, I ≤ S → S ≠ max I a → f (max I a) < f S := by
    intro S hS hne
    rcases le_total I a with hIa | hIa
    · rw [max_eq_right hIa] at hne ⊢
      rcases lt_or_gt_of_ne hne with h | h
      · exact h1 ⟨by linarith, h.le⟩ ⟨ha, le_rfl⟩ h
      · exact h2 (le_refl a) (le_of_lt h) h
    · rw [max_eq_left hIa] at hne ⊢
      have h' : I < S := lt_of_le_of_ne hS (Ne.symm hne)
      exact h2 (show a ≤ I from hIa) (show a ≤ S by linarith) h'
  ext S
  simp only [EarlyInspect.Align.argminFrom, mem_setOf_eq, mem_singleton_iff]
  constructor
  · rintro ⟨hS, hmin⟩
    by_contra hne
    have := key S hS hne
    have := hmin (max I a) (le_max_left _ _)
    linarith
  · rintro rfl
    refine ⟨le_max_left _ _, fun S' hS' => ?_⟩
    by_cases h : S' = max I a
    · rw [h]
    · exact (key S' hS' h).le

lemma agent_argmin (μ σ M t z : ℝ) (hσ : 0 < σ) (ht0 : 0 < t) (ht1 : t < 1)
    (hS : 0 ≤ μ + z * σ)
    (hM : M * gaussianPDFReal (t * μ) (Real.toNNReal ((Real.sqrt t * σ) ^ 2)) (μ + z * σ) =
      Fi μ (Real.toNNReal (σ ^ 2)) (μ + z * σ)) (I : ℝ) (hI : 0 ≤ I) :
    EarlyInspect.Align.argminFrom (EarlyInspect.Align.agentCost μ σ M t) I =
      {max I (μ + z * σ)} := by
  set v := Real.toNNReal (σ ^ 2) with hvdef
  set vY := Real.toNNReal ((Real.sqrt t * σ) ^ 2) with hvYdef
  have hvc : (v : ℝ) = σ ^ 2 := Real.coe_toNNReal _ (sq_nonneg _)
  have hvYc : (vY : ℝ) = t * σ ^ 2 := by
    rw [hvYdef, Real.coe_toNNReal _ (sq_nonneg _), mul_pow, Real.sq_sqrt ht0.le]
  have hv : v ≠ 0 := by
    rw [hvdef, Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hvYpos : (0 : ℝ) < vY := by rw [hvYc]; positivity
  have hvY : vY ≠ 0 := by
    intro h; rw [h] at hvYpos; simp at hvYpos
  set a := μ + z * σ with ha
  have hf : EarlyInspect.Align.agentCost μ σ M t = fun S =>
      ((v : ℝ) * gaussianPDFReal μ v S + (S - μ) * Fi μ v S) + M * (1 - Fi (t * μ) vY S) := by
    funext S
    unfold EarlyInspect.Align.agentCost
    rw [InventoryControl.newsboyDemand_eq, InventoryControl.newsboyDemand_eq, G_eq μ hv,
      real_Ici _ hvY]
  have hd : ∀ S, HasDerivAt (EarlyInspect.Align.agentCost μ σ M t)
      (Fi μ v S - M * gaussianPDFReal (t * μ) vY S) S := by
    intro S
    rw [hf]
    refine ((Gc_hasDeriv μ hv S).add
      (((Fi_hasDeriv (t * μ) vY S).const_sub 1).const_mul M)).congr_deriv ?_
    ring
  have hpY : ∀ S, 0 < gaussianPDFReal (t * μ) vY S := fun S => gaussianPDFReal_pos _ _ _ hvY
  set R : ℝ → ℝ := fun S => Fi μ v S / gaussianPDFReal (t * μ) vY S with hRdef
  have hRd : ∀ S, HasDerivAt R ((gaussianPDFReal μ v S * gaussianPDFReal (t * μ) vY S -
      Fi μ v S * (-(S - t * μ) / vY * gaussianPDFReal (t * μ) vY S)) /
        (gaussianPDFReal (t * μ) vY S) ^ 2) S :=
    fun S => (Fi_hasDeriv μ v S).div (pdf_hasDeriv (t * μ) vY S) (hpY S).ne'
  have hRmono : StrictMonoOn R (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun x _ => (hRd x).continuousAt.continuousWithinAt)
    intro x hx
    rw [interior_Ici] at hx
    have hx0 : 0 < x := hx
    rw [(hRd x).deriv]
    have hG := G_pos μ hv x
    rw [G_eq μ hv] at hG
    have hF := Fi_nonneg μ v x
    have key : 0 < (vY : ℝ) * gaussianPDFReal μ v x + (x - t * μ) * Fi μ v x := by
      have e : (vY : ℝ) * gaussianPDFReal μ v x + (x - t * μ) * Fi μ v x =
          t * ((v : ℝ) * gaussianPDFReal μ v x + (x - μ) * Fi μ v x) + (1 - t) * x * Fi μ v x := by
        rw [hvYc, hvc]; ring
      rw [e]
      have h1 : 0 < t * ((v : ℝ) * gaussianPDFReal μ v x + (x - μ) * Fi μ v x) := mul_pos ht0 hG
      have h2 : 0 ≤ (1 - t) * x * Fi μ v x :=
        mul_nonneg (mul_nonneg (by linarith) hx0.le) hF
      linarith
    have e2 : gaussianPDFReal μ v x * gaussianPDFReal (t * μ) vY x -
        Fi μ v x * (-(x - t * μ) / vY * gaussianPDFReal (t * μ) vY x) =
        gaussianPDFReal (t * μ) vY x *
          ((vY : ℝ) * gaussianPDFReal μ v x + (x - t * μ) * Fi μ v x) / vY := by
      field_simp
      ring
    rw [e2]
    exact div_pos (div_pos (mul_pos (hpY x) key) hvYpos) (pow_pos (hpY x) 2)
  have hRa : R a = M := by
    simp only [hRdef]
    rw [← hM]
    field_simp [(hpY a).ne']
  have hcont : Continuous (EarlyInspect.Align.agentCost μ σ M t) :=
    continuous_iff_continuousAt.2 (fun x => (hd x).continuousAt)
  apply argmin_of_shape _ a I hS hI
  · apply strictAntiOn_of_deriv_neg (convex_Icc 0 a) hcont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have hlt : R x < R a := hRmono (show (0:ℝ) ≤ x from hx.1.le) (show (0:ℝ) ≤ a from hS) hx.2
    rw [hRa] at hlt
    simp only [hRdef] at hlt
    rw [div_lt_iff₀ (hpY x)] at hlt
    linarith
  · apply strictMonoOn_of_deriv_pos (convex_Ici a) hcont.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    have hx' : a < x := hx
    rw [(hd x).deriv]
    have hlt : R a < R x := hRmono (show (0:ℝ) ≤ a from hS) (show (0:ℝ) ≤ x by linarith) hx'
    rw [hRa] at hlt
    simp only [hRdef] at hlt
    rw [lt_div_iff₀ (hpY x)] at hlt
    linarith

lemma newsboy_argmin (co cu μ σ z : ℝ) (hco : 0 < co) (hcu : 0 < cu) (hσ : 0 < σ)
    (hz : EarlyInspect.Align.Φ z = cu / (co + cu)) (hS : 0 ≤ μ + z * σ) (I : ℝ) (hI : 0 ≤ I) :
    EarlyInspect.Align.argminFrom (InventoryControl.newsboyCost co cu μ σ) I =
      {max I (μ + z * σ)} := by
  set v := Real.toNNReal (σ ^ 2) with hvdef
  have hv : v ≠ 0 := by
    rw [hvdef, Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have hid := integrable_id' μ v
  have hf : InventoryControl.newsboyCost co cu μ σ = fun S =>
      (co + cu) * ((v : ℝ) * gaussianPDFReal μ v S + (S - μ) * Fi μ v S) - cu * (S - μ) := by
    funext S
    unfold InventoryControl.newsboyCost InventoryControl.newsboyLoss
    rw [InventoryControl.newsboyDemand_eq, ← hvdef, ← G_eq μ hv]
    have hG : Integrable (fun x : ℝ => max (S - x) 0) (gaussianReal μ v) :=
      ((integrable_const S).sub hid).pos_part
    have h1 : (fun x => co * max (S - x) 0 + cu * max (x - S) 0) =
        fun x => (co + cu) * max (S - x) 0 + cu * (x - S) := by
      funext x
      rcases le_total x S with h | h
      · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
      · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    have hA : Integrable (fun x : ℝ => (co + cu) * max (S - x) 0) (gaussianReal μ v) :=
      hG.const_mul _
    have hB : Integrable (fun x : ℝ => cu * (x - S)) (gaussianReal μ v) :=
      (hid.sub (integrable_const S)).const_mul cu
    have hC : Integrable (fun _ : ℝ => S) (gaussianReal μ v) := integrable_const S
    have hBint : ∫ x, cu * (x - S) ∂(gaussianReal μ v) = cu * (μ - S) := by
      rw [integral_const_mul, integral_sub hid hC, integral_id_gaussianReal]
      simp
    rw [h1, integral_add hA hB, integral_const_mul, hBint]
    ring
  have hd : ∀ S, HasDerivAt (InventoryControl.newsboyCost co cu μ σ)
      ((co + cu) * Fi μ v S - cu) S := by
    intro S
    rw [hf]
    have hm : HasDerivAt (fun y : ℝ => y - μ) 1 S := by
      simpa using (hasDerivAt_id S).sub_const μ
    refine (((Gc_hasDeriv μ hv S).const_mul (co + cu)).sub (hm.const_mul cu)).congr_deriv ?_
    ring
  have hFmono : StrictMono (Fi μ v) := by
    apply strictMono_of_deriv_pos
    intro x
    rw [(Fi_hasDeriv μ v x).deriv]
    exact gaussianPDFReal_pos _ _ _ hv
  have hFa : Fi μ v (μ + z * σ) = cu / (co + cu) := by
    rw [hvdef, Fi_std μ σ z hσ, hz]
  have hcc : 0 < co + cu := by linarith
  have hcont : Continuous (InventoryControl.newsboyCost co cu μ σ) :=
    continuous_iff_continuousAt.2 (fun x => (hd x).continuousAt)
  apply argmin_of_shape _ _ I hS hI
  · apply strictAntiOn_of_deriv_neg (convex_Icc 0 _) hcont.continuousOn
    intro x hx
    rw [interior_Icc] at hx
    rw [(hd x).deriv]
    have h := hFmono hx.2
    rw [hFa] at h
    have := mul_lt_mul_of_pos_left h hcc
    rw [mul_div_cancel₀ _ hcc.ne'] at this
    linarith
  · apply strictMonoOn_of_deriv_pos (convex_Ici _) hcont.continuousOn
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    have h := hFmono (show μ + z * σ < x from hx)
    rw [hFa] at h
    have := mul_lt_mul_of_pos_left h hcc
    rw [mul_div_cancel₀ _ hcc.ne'] at this
    linarith

lemma M_eq (μ₁ σ₁ μ₂ σ₂ z s : ℝ) (hσ₁ : 0 < σ₁) (hσ₂ : 0 < σ₂) (hs : 0 < s)
    (hins : EarlyInspect.Align.inspectionLHS (μ₁ / σ₁) (μ₂ / σ₂) z (s ^ 2) = σ₂ / σ₁) :
    EarlyInspect.Align.incentiveM μ₁ σ₁ z (s ^ 2) = EarlyInspect.Align.incentiveM μ₂ σ₂ z (s ^ 2) := by
  unfold EarlyInspect.Align.incentiveM EarlyInspect.Align.inspectionLHS at *
  rw [Real.sqrt_sq hs.le]
  set A₁ := μ₁ / σ₁ * (1 - s ^ 2) + z
  set A₂ := μ₂ / σ₂ * (1 - s ^ 2) + z
  have hφ : ∀ y, EarlyInspect.Align.φ y = (√(2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
    intro y
    simp [EarlyInspect.Align.φ, gaussianPDFReal_def]
  have hexp : Real.exp (-(A₂ / s) ^ 2 / 2) =
      Real.exp (-(A₁ / s) ^ 2 / 2) * Real.exp (-(1 / 2) * ((A₂ ^ 2 - A₁ ^ 2) / s ^ 2)) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hins] at hexp
  have key : σ₁ * EarlyInspect.Align.φ (A₂ / s) = σ₂ * EarlyInspect.Align.φ (A₁ / s) := by
    rw [hφ, hφ, hexp]
    field_simp
  have h1 : 0 < EarlyInspect.Align.φ (A₁ / s) := gaussianPDFReal_pos _ _ _ one_ne_zero
  have h2 : 0 < EarlyInspect.Align.φ (A₂ / s) := gaussianPDFReal_pos _ _ _ one_ne_zero
  field_simp
  linear_combination (EarlyInspect.Align.Φ z) * key

end EIA2

open EarlyInspect.Align InventoryControl in
theorem solution (co cu μ₁ σ₁ μ₂ σ₂ zhat : ℝ) (hco : 0 < co) (hcu : 0 < cu)
    (hσ₂ : 0 < σ₂) (hσ : σ₂ < σ₁) (hk : μ₁ / σ₁ < μ₂ / σ₂)
    (hzhat : Φ zhat = cu / (co + cu)) (hS : 0 ≤ μ₁ + zhat * σ₁) :
    ∃ τ : ℝ, 0 < τ ∧ τ < 1 ∧
      inspectionLHS (μ₁ / σ₁) (μ₂ / σ₂) zhat τ = σ₂ / σ₁ ∧
      incentiveM μ₁ σ₁ zhat τ = incentiveM μ₂ σ₂ zhat τ ∧
      ∀ I : ℝ, 0 ≤ I →
        argminFrom (agentCost μ₁ σ₁ (incentiveM μ₁ σ₁ zhat τ) τ) I = {max I (μ₁ + zhat * σ₁)} ∧
        argminFrom (agentCost μ₂ σ₂ (incentiveM μ₁ σ₁ zhat τ) τ) I = {max I (μ₂ + zhat * σ₂)} ∧
        argminFrom (newsboyCost co cu μ₁ σ₁) I = {max I (μ₁ + zhat * σ₁)} ∧
        argminFrom (newsboyCost co cu μ₂ σ₂) I = {max I (μ₂ + zhat * σ₂)} := by
  have hσ₁ : 0 < σ₁ := hσ₂.trans hσ
  have hk1z : 0 ≤ μ₁ / σ₁ + zhat := by
    have e : μ₁ / σ₁ + zhat = (μ₁ + zhat * σ₁) / σ₁ := by field_simp
    rw [e]; positivity
  have hk2z : 0 < μ₂ / σ₂ + zhat := by linarith
  have hS₂ : 0 ≤ μ₂ + zhat * σ₂ := by
    have e : μ₂ + zhat * σ₂ = σ₂ * (μ₂ / σ₂ + zhat) := by field_simp
    rw [e]; positivity
  set c := 2 * Real.log (σ₁ / σ₂) with hcdef
  have hc : 0 < c := mul_pos two_pos (Real.log_pos ((one_lt_div hσ₂).2 hσ))
  set N : ℝ → ℝ := fun τ => (μ₂ / σ₂ * (1 - τ) + zhat) ^ 2 - (μ₁ / σ₁ * (1 - τ) + zhat) ^ 2 - c * τ
    with hNdef
  have hN0 : 0 < N 0 := by
    simp only [hNdef]
    nlinarith
  have hN1 : N 1 < 0 := by
    simp only [hNdef]
    nlinarith
  have hNc : ContinuousOn N (Icc 0 1) := by
    simp only [hNdef]; fun_prop
  obtain ⟨τ, ⟨hτ0, hτ1⟩, hNτ⟩ := intermediate_value_Ioo' zero_le_one hNc ⟨hN1, hN0⟩
  have hins : inspectionLHS (μ₁ / σ₁) (μ₂ / σ₂) zhat τ = σ₂ / σ₁ := by
    unfold inspectionLHS
    have e : ((μ₂ / σ₂ * (1 - τ) + zhat) ^ 2 - (μ₁ / σ₁ * (1 - τ) + zhat) ^ 2) / τ = c := by
      simp only [hNdef] at hNτ
      rw [div_eq_iff hτ0.ne']
      linarith
    rw [e, show -(1 / 2 : ℝ) * c = -Real.log (σ₁ / σ₂) by rw [hcdef]; ring, Real.exp_neg,
      Real.exp_log (div_pos hσ₁ hσ₂), inv_div]
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ τ = s ^ 2 :=
    ⟨Real.sqrt τ, Real.sqrt_pos.2 hτ0, (Real.sq_sqrt hτ0.le).symm⟩
  have hMeq := EIA2.M_eq μ₁ σ₁ μ₂ σ₂ zhat s hσ₁ hσ₂ hs hins
  refine ⟨s ^ 2, hτ0, hτ1, hins, hMeq, fun I hI => ⟨?_, ?_, ?_, ?_⟩⟩
  · exact EIA2.agent_argmin μ₁ σ₁ _ (s ^ 2) zhat hσ₁ hτ0 hτ1 hS
      (EIA2.hM_at μ₁ σ₁ zhat s hσ₁ hs) I hI
  · rw [hMeq]
    exact EIA2.agent_argmin μ₂ σ₂ _ (s ^ 2) zhat hσ₂ hτ0 hτ1 hS₂
      (EIA2.hM_at μ₂ σ₂ zhat s hσ₂ hs) I hI
  · exact EIA2.newsboy_argmin co cu μ₁ σ₁ zhat hco hcu hσ₁ hzhat hS I hI
  · exact EIA2.newsboy_argmin co cu μ₂ σ₂ zhat hco hcu hσ₂ hzhat hS₂ I hI
