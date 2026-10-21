-- Prove2me | solution 1 for DimCallCenters.Rationalized.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T22:15:16.020599+00:00
-- url     : https://prove2.me/submissions/b260a94a-9f2b-4313-904f-f2e818e8ccfb

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Glam

set_option autoImplicit false
open DimCallCenters.Rationalized Set MeasureTheory

namespace DccC1

def DHyp (D : ℝ → ℝ) : Prop :=
  D 0 = 0 ∧ StrictMonoOn D (Ici 0) ∧
    ∀ θ : ℝ, 0 < θ → IntegrableOn (fun t => D t * Real.exp (-θ * t)) (Ioi 0)

noncomputable def E (D : ℝ → ℝ) (t : ℝ) : ℝ := D (max t 0)

noncomputable def mu (θ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0:ℝ))).withDensity (fun t => ENNReal.ofReal (θ * Real.exp (-(θ * t))))

noncomputable def gf (D : ℝ → ℝ) (θ : ℝ) : ℝ := ∫ t in Ioi (0:ℝ), θ * Real.exp (-(θ * t)) * D t

noncomputable def Phi (D : ℝ → ℝ) (θ y : ℝ) : ℝ := (mu θ {t | y < E D t}).toReal

lemma D_pos (D : ℝ → ℝ) (hD : DHyp D) (t : ℝ) (ht : 0 < t) : 0 < D t := by
  have := hD.2.1 (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht.le) ht
  rw [hD.1] at this
  exact this

lemma E_mono (D : ℝ → ℝ) (hD : DHyp D) : Monotone (E D) := by
  intro a b hab
  exact hD.2.1.monotoneOn (Set.mem_Ici.2 (le_max_right _ _)) (Set.mem_Ici.2 (le_max_right _ _))
    (max_le_max hab le_rfl)

lemma E_nonneg (D : ℝ → ℝ) (hD : DHyp D) (t : ℝ) : 0 ≤ E D t := by
  unfold E
  have := hD.2.1.monotoneOn (Set.mem_Ici.2 (le_refl (0:ℝ))) (Set.mem_Ici.2 (le_max_right t 0))
    (le_max_right t 0)
  rwa [hD.1] at this

lemma E_meas (D : ℝ → ℝ) (hD : DHyp D) : Measurable (E D) := (E_mono D hD).measurable

lemma E_pos (D : ℝ → ℝ) (t : ℝ) (ht : 0 < t) : E D t = D t := by
  unfold E; rw [max_eq_left ht.le]

lemma E_nonpos (D : ℝ → ℝ) (hD : DHyp D) (t : ℝ) (ht : t ≤ 0) : E D t = 0 := by
  unfold E; rw [max_eq_right ht]; exact hD.1

lemma rho_int (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun t : ℝ => θ * Real.exp (-(θ * t))) (Ioi 0) := by
  have h : IntegrableOn (fun t : ℝ => θ * Real.exp (-θ * t)) (Ioi 0) :=
    Integrable.const_mul (exp_neg_integrableOn_Ioi (0:ℝ) hθ) θ
  exact h.congr_fun (fun t _ => by simp only [neg_mul]) measurableSet_Ioi

lemma mu_fin (θ : ℝ) (hθ : 0 < θ) : IsFiniteMeasure (mu θ) :=
  isFiniteMeasure_withDensity_ofReal (rho_int θ hθ).hasFiniteIntegral

lemma mu_ac (θ : ℝ) : mu θ ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

lemma mu_apply (θ : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    mu θ S = ∫⁻ t in S ∩ Ioi 0, ENNReal.ofReal (θ * Real.exp (-(θ * t))) := by
  unfold mu
  rw [withDensity_apply _ hS, Measure.restrict_restrict hS]

lemma mu_Ioi (θ : ℝ) (hθ : 0 < θ) (u : ℝ) (hu : 0 ≤ u) :
    mu θ (Ioi u) = ENNReal.ofReal (Real.exp (-(θ * u))) := by
  rw [mu_apply θ _ measurableSet_Ioi, inter_eq_left.mpr (Ioi_subset_Ioi hu)]
  have hi : IntegrableOn (fun t : ℝ => θ * Real.exp (-(θ * t))) (Ioi u) := by
    have h : IntegrableOn (fun t : ℝ => θ * Real.exp (-θ * t)) (Ioi u) :=
      Integrable.const_mul (exp_neg_integrableOn_Ioi u hθ) θ
    exact h.congr_fun (fun t _ => by simp only [neg_mul]) measurableSet_Ioi
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall (fun t => by positivity))]
  congr 1
  rw [integral_const_mul]
  have := integral_exp_mul_Ioi (a := -θ) (by linarith) u
  simp only [neg_mul] at this
  rw [this]
  field_simp

lemma shape (D : ℝ → ℝ) (hD : DHyp D) (y : ℝ) (hy : 0 < y) :
    ((¬ ({t | y < E D t}).Nonempty) ∧ ∀ θ, mu θ {t | y < E D t} = 0) ∨
    (({t | y < E D t}).Nonempty ∧ 0 ≤ sInf {t | y < E D t} ∧
      ∀ θ : ℝ, 0 < θ → mu θ {t | y < E D t} =
        ENNReal.ofReal (Real.exp (-(θ * sInf {t | y < E D t})))) := by
  set U : Set ℝ := {t | y < E D t} with hU
  have hsub : U ⊆ Ioi 0 := by
    intro t ht
    by_contra h
    have : E D t = 0 := E_nonpos D hD t (not_lt.mp h)
    simp only [hU, mem_setOf_eq] at ht
    linarith
  have hup : ∀ t ∈ U, ∀ s, t ≤ s → s ∈ U := by
    intro t ht s hts
    exact lt_of_lt_of_le ht (E_mono D hD hts)
  by_cases hne : U.Nonempty
  · right
    refine ⟨hne, ?_, ?_⟩
    · exact le_csInf hne (fun t ht => (hsub ht).le)
    · intro θ hθ
      have hbdd : BddBelow U := ⟨0, fun t ht => (hsub ht).le⟩
      have hu0 : 0 ≤ sInf U := le_csInf hne (fun t ht => (hsub ht).le)
      have h1 : Ioi (sInf U) ⊆ U := by
        intro t ht
        obtain ⟨b, hb, hbt⟩ := exists_lt_of_csInf_lt hne ht
        exact hup b hb t hbt.le
      have h2 : U ⊆ Ici (sInf U) := fun t ht => csInf_le hbdd ht
      have h3 : U =ᵐ[volume] Ioi (sInf U) := by
        refine Filter.EventuallyLE.antisymm ?_ h1.eventuallyLE
        exact (h2.eventuallyLE).trans (Ioi_ae_eq_Ici.symm.le)
      rw [measure_congr ((mu_ac θ).ae_eq h3), mu_Ioi θ hθ _ hu0]
  · left
    refine ⟨hne, fun θ => ?_⟩
    rw [not_nonempty_iff_eq_empty.mp hne]
    exact measure_empty

lemma Phi_shape (D : ℝ → ℝ) (hD : DHyp D) (y : ℝ) (hy : 0 < y) :
    (∀ θ, Phi D θ y = 0) ∨
    (∃ u : ℝ, 0 ≤ u ∧ ∀ θ : ℝ, 0 < θ → Phi D θ y = Real.exp (-(θ * u))) := by
  rcases shape D hD y hy with ⟨_, h⟩ | ⟨_, hu, h⟩
  · left; intro θ; unfold Phi; rw [h θ]; simp
  · right
    refine ⟨_, hu, fun θ hθ => ?_⟩
    unfold Phi; rw [h θ hθ, ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma gf_int (D : ℝ → ℝ) (hD : DHyp D) (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (fun t => θ * Real.exp (-(θ * t)) * D t) (Ioi 0) := by
  have h : IntegrableOn (fun t => θ * (D t * Real.exp (-θ * t))) (Ioi 0) :=
    Integrable.const_mul (hD.2.2 θ hθ) θ
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [neg_mul]; ring

lemma gf_nonneg (D : ℝ → ℝ) (hD : DHyp D) (θ : ℝ) (hθ : 0 < θ) : 0 ≤ gf D θ := by
  unfold gf
  refine setIntegral_nonneg measurableSet_Ioi (fun t ht => ?_)
  have := D_pos D hD t ht
  positivity

lemma lint_gf (D : ℝ → ℝ) (hD : DHyp D) (θ : ℝ) (hθ : 0 < θ) :
    ∫⁻ y in Ioi (0:ℝ), mu θ {t | y < E D t} = ENNReal.ofReal (gf D θ) := by
  have hlc := lintegral_eq_lintegral_meas_lt (mu θ) (f := E D)
    (Filter.Eventually.of_forall (fun t => E_nonneg D hD t)) (E_meas D hD).aemeasurable
  rw [← hlc]
  unfold mu
  rw [lintegral_withDensity_eq_lintegral_mul (g := fun ω => ENNReal.ofReal (E D ω)) _ (by fun_prop)
    (ENNReal.measurable_ofReal.comp (E_meas D hD))]
  unfold gf
  rw [ofReal_integral_eq_lintegral_ofReal (gf_int D hD θ hθ)
    (by
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall (fun t ht => ?_))
      have := D_pos D hD t ht
      positivity)]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  simp only [Pi.mul_apply, Function.comp]
  rw [← ENNReal.ofReal_mul (by positivity), E_pos D t ht]

lemma Phi_meas (D : ℝ → ℝ) (θ : ℝ) : Measurable (Phi D θ) := by
  have : Antitone (fun y : ℝ => mu θ {t | y < E D t}) :=
    fun a b hab => measure_mono (fun t ht => lt_of_le_of_lt hab ht)
  exact this.measurable.ennreal_toReal

lemma Phi_int (D : ℝ → ℝ) (hD : DHyp D) (θ : ℝ) (hθ : 0 < θ) :
    IntegrableOn (Phi D θ) (Ioi 0) ∧ ∫ y in Ioi (0:ℝ), Phi D θ y = gf D θ := by
  haveI := mu_fin θ hθ
  have hl : ∫⁻ y in Ioi (0:ℝ), ENNReal.ofReal (Phi D θ y) = ENNReal.ofReal (gf D θ) := by
    rw [← lint_gf D hD θ hθ]
    refine lintegral_congr (fun y => ?_)
    unfold Phi
    rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] Phi D θ :=
    Filter.Eventually.of_forall (fun y => ENNReal.toReal_nonneg)
  refine ⟨⟨Measurable.aestronglyMeasurable (Phi_meas D θ),
    (hasFiniteIntegral_iff_ofReal hnn).2 (by rw [hl]; exact ENNReal.ofReal_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn (Measurable.aestronglyMeasurable (Phi_meas D θ)), hl,
    ENNReal.toReal_ofReal (gf_nonneg D hD θ hθ)]

lemma gf_conv_anti (D : ℝ → ℝ) (hD : DHyp D) :
    StrictConvexOn ℝ (Ioi 0) (gf D) ∧ StrictAntiOn (gf D) (Ioi 0) := by
  have hE12 : E D 1 < E D 2 := by
    rw [E_pos D 1 one_pos, E_pos D 2 two_pos]
    exact hD.2.1 (Set.mem_Ici.2 zero_le_one) (Set.mem_Ici.2 (by norm_num)) one_lt_two
  have hE1pos : 0 < E D 1 := by rw [E_pos D 1 one_pos]; exact D_pos D hD 1 one_pos
  have hAmeas : 0 < volume (Ico (E D 1) (E D 2)) := by
    rw [Real.volume_Ico]; simpa using hE12
  -- on A, the shape is a genuine exponential with u ≥ 1
  have hA : ∀ y ∈ Ico (E D 1) (E D 2), 0 < y ∧
      ∃ u : ℝ, 1 ≤ u ∧ ∀ θ : ℝ, 0 < θ → Phi D θ y = Real.exp (-(θ * u)) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le hE1pos hy.1
    refine ⟨hy0, ?_⟩
    rcases shape D hD y hy0 with ⟨hne, _⟩ | ⟨hne, hu, h⟩
    · exact absurd ⟨2, hy.2⟩ hne
    · refine ⟨sInf {t | y < E D t}, ?_, fun θ hθ => ?_⟩
      · refine le_csInf hne (fun t ht => ?_)
        by_contra hlt
        have : E D t ≤ E D 1 := E_mono D hD (not_le.mp hlt).le
        simp only [mem_setOf_eq] at ht
        linarith [hy.1]
      · unfold Phi; rw [h θ hθ, ENNReal.toReal_ofReal (Real.exp_pos _).le]
  constructor
  · refine ⟨convex_Ioi 0, ?_⟩
    intro θ1 h1 θ2 h2 hne a b ha hb hab
    simp only [smul_eq_mul]
    have h1' : 0 < θ1 := h1
    have h2' : 0 < θ2 := h2
    have hθ : 0 < a * θ1 + b * θ2 := by positivity
    obtain ⟨i1, e1⟩ := Phi_int D hD θ1 h1'
    obtain ⟨i2, e2⟩ := Phi_int D hD θ2 h2'
    obtain ⟨i3, e3⟩ := Phi_int D hD _ hθ
    have hint : IntegrableOn (fun y => a * Phi D θ1 y + b * Phi D θ2 y - Phi D (a * θ1 + b * θ2) y)
        (Ioi 0) := ((i1.const_mul a).add (i2.const_mul b)).sub i3
    have hpw : ∀ y ∈ Ioi (0:ℝ),
        0 ≤ a * Phi D θ1 y + b * Phi D θ2 y - Phi D (a * θ1 + b * θ2) y := by
      intro y hy
      rcases Phi_shape D hD y hy with h | ⟨u, hu, h⟩
      · simp [h]
      · rw [h _ hθ, h _ h1', h _ h2']
        have := convexOn_exp.2 (mem_univ (-(θ1 * u))) (mem_univ (-(θ2 * u))) ha.le hb.le hab
        simp only [smul_eq_mul] at this
        have e : -((a * θ1 + b * θ2) * u) = a * -(θ1 * u) + b * -(θ2 * u) := by ring
        rw [e]; linarith
    have hpos : 0 < ∫ y in Ioi (0:ℝ),
        (a * Phi D θ1 y + b * Phi D θ2 y - Phi D (a * θ1 + b * θ2) y) := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hpw)) hint]
      refine lt_of_lt_of_le hAmeas (measure_mono (fun y hy => ?_))
      obtain ⟨hy0, u, hu1, h⟩ := hA y hy
      refine ⟨?_, hy0⟩
      rw [Function.mem_support, h _ hθ, h _ h1', h _ h2']
      have := strictConvexOn_exp.2 (mem_univ (-(θ1 * u))) (mem_univ (-(θ2 * u)))
        (by intro heq; apply hne; have : θ1 * u = θ2 * u := by linarith
            exact mul_right_cancel₀ (by linarith) this) ha hb hab
      simp only [smul_eq_mul] at this
      have e : -((a * θ1 + b * θ2) * u) = a * -(θ1 * u) + b * -(θ2 * u) := by ring
      rw [e]; linarith
    have hsum : IntegrableOn (fun y => a * Phi D θ1 y + b * Phi D θ2 y) (Ioi 0) :=
      (i1.const_mul a).add (i2.const_mul b)
    rw [integral_sub hsum i3, integral_add (i1.const_mul a) (i2.const_mul b),
      integral_const_mul, integral_const_mul, e1, e2, e3] at hpos
    linarith
  · intro θ1 h1 θ2 h2 hlt
    have h1' : 0 < θ1 := h1
    have h2' : 0 < θ2 := h2
    obtain ⟨i1, e1⟩ := Phi_int D hD θ1 h1'
    obtain ⟨i2, e2⟩ := Phi_int D hD θ2 h2'
    have hint := i1.sub i2
    have hpw : ∀ y ∈ Ioi (0:ℝ), 0 ≤ Phi D θ1 y - Phi D θ2 y := by
      intro y hy
      rcases Phi_shape D hD y hy with h | ⟨u, hu, h⟩
      · simp [h]
      · rw [h _ h1', h _ h2']
        have : Real.exp (-(θ2 * u)) ≤ Real.exp (-(θ1 * u)) :=
          Real.exp_le_exp.2 (by nlinarith)
        linarith
    have hpos : 0 < ∫ y in Ioi (0:ℝ), (Phi D θ1 y - Phi D θ2 y) := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae
        ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall hpw)) hint]
      refine lt_of_lt_of_le hAmeas (measure_mono (fun y hy => ?_))
      obtain ⟨hy0, u, hu1, h⟩ := hA y hy
      refine ⟨?_, hy0⟩
      rw [Function.mem_support, h _ h1', h _ h2']
      have : Real.exp (-(θ2 * u)) < Real.exp (-(θ1 * u)) :=
        Real.exp_lt_exp.2 (by nlinarith)
      linarith
    rw [integral_sub i1 i2, e1, e2] at hpos
    linarith

end DccC1

open DccC1 in
theorem solution (M : WaitModel) (lam : ℝ) (hlam : 0 < lam) :
    StrictConvexOn ℝ (Set.Ioi 0) (Glam M lam) ∧ StrictAntiOn (Glam M lam) (Set.Ioi 0) := by
  have hD : DHyp (M.D lam) := ⟨M.hD0 lam hlam, M.hDmono lam hlam, M.hDint lam hlam⟩
  obtain ⟨hc, ha⟩ := gf_conv_anti _ hD
  have hμ := M.hμ
  set c : ℝ := M.μ * Real.sqrt (lam / M.μ) with hcdef
  have hcpos : 0 < c := by
    have : 0 < Real.sqrt (lam / M.μ) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hG : ∀ x, Glam M lam x = lam * gf (M.D lam) (c * x) := by
    intro x
    unfold Glam waitCost gf servers
    have : (lam / M.μ + x * Real.sqrt (lam / M.μ)) * M.μ - lam = c * x := by
      rw [hcdef]; field_simp; ring
    rw [this, ← integral_const_mul]
    congr 2
    funext t
    simp only [neg_mul]
    ring
  have hfun : Glam M lam = fun x => lam * gf (M.D lam) (c * x) := funext hG
  rw [hfun]
  constructor
  · refine ⟨convex_Ioi 0, ?_⟩
    intro x hx y hy hxy a b ha0 hb0 hab
    have hx' : 0 < c * x := mul_pos hcpos hx
    have hy' : 0 < c * y := mul_pos hcpos hy
    have := hc.2 (show c * x ∈ Ioi 0 from hx') (show c * y ∈ Ioi 0 from hy')
      (fun h => hxy (mul_left_cancel₀ hcpos.ne' h)) ha0 hb0 hab
    simp only [smul_eq_mul] at this ⊢
    have e : c * (a * x + b * y) = a * (c * x) + b * (c * y) := by ring
    rw [e]
    nlinarith
  · intro x hx y hy hxy
    have hx' : 0 < c * x := mul_pos hcpos hx
    have hy' : 0 < c * y := mul_pos hcpos hy
    have := ha (show c * x ∈ Ioi 0 from hx') (show c * y ∈ Ioi 0 from hy')
      (mul_lt_mul_of_pos_left hxy hcpos)
    show lam * _ < lam * _
    exact mul_lt_mul_of_pos_left this hlam
