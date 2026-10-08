-- Prove2me | solution 1 for DimCallCenters.QualityDriven.lemma_C_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:53:59.741737+00:00
-- url     : https://prove2.me/submissions/3fe9f74c-7bc7-402e-8ceb-fdc9a3425e48

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Glam

set_option autoImplicit false

namespace LC1Aux73877692

open MeasureTheory Set

noncomputable def dens (θ : ℝ) (t : ℝ) : NNReal := Real.toNNReal (θ * Real.exp (-θ * t))

lemma dens_meas (θ : ℝ) : Measurable (dens θ) := by
  unfold dens
  fun_prop

noncomputable def mu (θ : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t => (dens θ t : ENNReal))

lemma lint_Ioi (θ : ℝ) (hθ : 0 < θ) (a : ℝ) :
    ∫⁻ t in Ioi a, (dens θ t : ENNReal) = ENNReal.ofReal (Real.exp (-θ * a)) := by
  have hint : IntegrableOn (fun t => θ * Real.exp (-θ * t)) (Ioi a) :=
    (exp_neg_integrableOn_Ioi a hθ).const_mul θ
  have hval : ∫ t in Ioi a, θ * Real.exp (-θ * t) = Real.exp (-θ * a) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) a]
    field_simp
  rw [← hval, ofReal_integral_eq_lintegral_ofReal hint]
  · rfl
  · exact ae_of_all _ (fun t => by positivity)

lemma mu_apply (θ : ℝ) (S : Set ℝ) :
    mu θ S = ∫⁻ t in S ∩ Ioi 0, (dens θ t : ENNReal) := by
  rw [mu, withDensity_apply', Measure.restrict_restrict' measurableSet_Ioi]

lemma mu_up (θ : ℝ) (hθ : 0 < θ) (S : Set ℝ) (hne : (S ∩ Ioi 0).Nonempty)
    (hup : ∀ s t, s ∈ S ∩ Ioi 0 → s ≤ t → t ∈ S) :
    mu θ S = ENNReal.ofReal (Real.exp (-θ * sInf (S ∩ Ioi 0))) := by
  have hbdd : BddBelow (S ∩ Ioi 0) := ⟨0, fun t ht => le_of_lt ht.2⟩
  have ha0 : 0 ≤ sInf (S ∩ Ioi 0) := le_csInf hne (fun t ht => le_of_lt ht.2)
  have h1 : Ioi (sInf (S ∩ Ioi 0)) ⊆ S ∩ Ioi 0 := by
    intro t ht
    obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne ht
    exact ⟨hup s t hs hst.le, lt_of_le_of_lt ha0 ht⟩
  have h2 : S ∩ Ioi 0 ⊆ Ici (sInf (S ∩ Ioi 0)) := fun t ht => csInf_le hbdd ht
  have hae : (S ∩ Ioi 0 : Set ℝ) =ᵐ[volume] Ioi (sInf (S ∩ Ioi 0)) := by
    refine (ae_eq_set).2 ⟨?_, ?_⟩
    · refine measure_mono_null (t := {sInf (S ∩ Ioi 0)}) ?_ (measure_singleton _)
      intro t ht
      have h3 := h2 ht.1
      have h4 := ht.2
      simp only [mem_Ioi, not_lt, mem_Ici] at h3 h4
      simp only [mem_singleton_iff]
      linarith
    · rw [sdiff_eq_empty.2 h1]
      simp
  rw [mu_apply, setLIntegral_congr hae, lint_Ioi θ hθ]

lemma mu_empty (θ : ℝ) (S : Set ℝ) (h : S ∩ Ioi 0 = ∅) : mu θ S = 0 := by
  rw [mu_apply, h]
  simp

noncomputable def phi (D : ℝ → ℝ) (v θ : ℝ) : ℝ := (mu θ {t | v < D t}).toReal

noncomputable def Hf (D : ℝ → ℝ) (θ : ℝ) : ℝ := θ * ∫ t in Ioi 0, D t * Real.exp (-θ * t)

lemma phi_cases (D : ℝ → ℝ) (hmono : StrictMonoOn D (Ici 0)) (v : ℝ) :
    (D 1 ≤ v ∧ ∀ θ, 0 < θ → phi D v θ = 0) ∨
    ∃ a, 0 ≤ a ∧ (D (1/2) < v → 1/2 ≤ a) ∧ ∀ θ, 0 < θ → phi D v θ = Real.exp (-θ * a) := by
  by_cases hne : ({t | v < D t} ∩ Ioi 0).Nonempty
  · right
    refine ⟨sInf ({t | v < D t} ∩ Ioi 0), le_csInf hne (fun t ht => le_of_lt ht.2), ?_, ?_⟩
    · intro hv
      refine le_csInf hne (fun t ht => ?_)
      by_contra h
      push_neg at h
      have h5 : D t ≤ D (1/2) :=
        hmono.monotoneOn (mem_Ici.2 (le_of_lt ht.2)) (by norm_num [mem_Ici]) h.le
      have h6 := ht.1
      simp only [mem_setOf_eq] at h6
      linarith
    · intro θ hθ
      rw [phi, mu_up θ hθ _ hne ?_, ENNReal.toReal_ofReal (Real.exp_pos _).le]
      intro s t hs hst
      have h7 := hs.1
      simp only [mem_setOf_eq] at h7 ⊢
      exact lt_of_lt_of_le h7 (hmono.monotoneOn (mem_Ici.2 (le_of_lt hs.2))
        (mem_Ici.2 (le_trans (le_of_lt hs.2) hst)) hst)
  · left
    refine ⟨?_, ?_⟩
    · by_contra h
      push_neg at h
      exact hne ⟨1, by simpa using h, by norm_num⟩
    · intro θ hθ
      rw [phi, mu_empty θ _ (not_nonempty_iff_eq_empty.1 hne)]
      simp

lemma layer (D : ℝ → ℝ) (hD0 : D 0 = 0) (hmono : StrictMonoOn D (Ici 0))
    (hint : ∀ θ : ℝ, 0 < θ → IntegrableOn (fun t => D t * Real.exp (-θ * t)) (Ioi 0))
    (θ : ℝ) (hθ : 0 < θ) :
    Hf D θ = ∫ v in Ioi 0, phi D v θ ∧ IntegrableOn (fun v => phi D v θ) (Ioi 0) := by
  have hpt : ∀ x : ℝ, dens θ x • D x = θ * (D x * Real.exp (-θ * x)) := by
    intro x
    rw [NNReal.smul_def, dens, Real.coe_toNNReal _ (by positivity), smul_eq_mul]
    ring
  have hI : Integrable D (mu θ) := by
    rw [mu, integrable_withDensity_iff_integrable_smul (dens_meas θ)]
    simp_rw [hpt]
    exact (hint θ hθ).const_mul θ
  have hnn : 0 ≤ᵐ[mu θ] D := by
    refine (withDensity_absolutelyContinuous _ _).ae_le
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun t ht => ?_))
    have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 (le_of_lt ht)) ht
    rw [hD0] at this
    exact this.le
  refine ⟨?_, ?_⟩
  · have L := Integrable.integral_eq_integral_meas_lt hI hnn
    calc Hf D θ = ∫ t, D t ∂(mu θ) := by
          rw [mu, integral_withDensity_eq_integral_smul (dens_meas θ)]
          simp_rw [hpt]
          rw [integral_const_mul, Hf]
      _ = _ := L
      _ = _ := rfl
  · have key := lintegral_eq_lintegral_meas_lt (mu θ) hnn hI.aemeasurable
    have hfin : ∫⁻ ω, ENNReal.ofReal (D ω) ∂(mu θ) ≠ ⊤ := (Integrable.lintegral_lt_top hI).ne
    rw [key] at hfin
    have hanti : Antitone (fun v : ℝ => mu θ {t | v < D t}) := by
      intro v1 v2 h
      apply measure_mono
      intro t ht
      simp only [mem_setOf_eq] at ht ⊢
      linarith
    exact integrable_toReal_of_lintegral_ne_top hanti.measurable.aemeasurable hfin

lemma int_lt_of (f g : ℝ → ℝ) (hf : IntegrableOn f (Ioi 0)) (hg : IntegrableOn g (Ioi 0))
    (p q : ℝ) (hp : 0 ≤ p) (hpq : p < q)
    (hle : ∀ v : ℝ, 0 < v → f v ≤ g v) (hlt : ∀ v, p < v → v < q → f v < g v) :
    ∫ v in Ioi 0, f v < ∫ v in Ioi 0, g v := by
  rw [← sub_pos, ← integral_sub hg hf]
  rw [integral_pos_iff_support_of_nonneg_ae]
  · have hsub : Ioo p q ⊆ Function.support (fun v => g v - f v) ∩ Ioi 0 := by
      intro v hv
      refine ⟨?_, lt_of_le_of_lt hp hv.1⟩
      simp only [Function.mem_support]
      have := hlt v hv.1 hv.2
      linarith
    rw [Measure.restrict_apply' measurableSet_Ioi]
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.2 (sub_pos.2 hpq)
  · exact ae_restrict_of_forall_mem measurableSet_Ioi (fun v hv => sub_nonneg.2 (hle v hv))
  · exact hg.sub hf

lemma H_main (D : ℝ → ℝ) (hD0 : D 0 = 0) (hmono : StrictMonoOn D (Ici 0))
    (hint : ∀ θ : ℝ, 0 < θ → IntegrableOn (fun t => D t * Real.exp (-θ * t)) (Ioi 0)) :
    StrictConvexOn ℝ (Ioi 0) (Hf D) ∧ StrictAntiOn (Hf D) (Ioi 0) := by
  have hp : 0 ≤ D (1/2) := by
    have := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 (by norm_num)) (by norm_num : (0:ℝ) < 1/2)
    rw [hD0] at this
    exact this.le
  have hpq : D (1/2) < D 1 := hmono (mem_Ici.2 (by norm_num)) (mem_Ici.2 (by norm_num))
    (by norm_num)
  refine ⟨⟨convex_Ioi 0, ?_⟩, ?_⟩
  · intro x hx y hy hxy a b ha hb hab
    have hx' : (0 : ℝ) < x := hx
    have hy' : (0 : ℝ) < y := hy
    simp only [smul_eq_mul]
    have hz : 0 < a * x + b * y := by positivity
    obtain ⟨ez, iz⟩ := layer D hD0 hmono hint _ hz
    obtain ⟨ex, ix⟩ := layer D hD0 hmono hint _ hx'
    obtain ⟨ey, iy⟩ := layer D hD0 hmono hint _ hy'
    rw [ez, ex, ey]
    rw [← integral_const_mul, ← integral_const_mul,
      ← integral_add (ix.const_mul a) (iy.const_mul b)]
    refine int_lt_of _ _ iz ((ix.const_mul a).add (iy.const_mul b)) _ _ hp hpq ?_ ?_
    · intro v hv
      rcases phi_cases D hmono v with ⟨_, h0⟩ | ⟨c, hc0, _, hc⟩
      · rw [h0 _ hz, h0 _ hx', h0 _ hy']
        simp
      · rw [hc _ hz, hc _ hx', hc _ hy']
        have := convexOn_exp.2 (mem_univ (-x * c)) (mem_univ (-y * c)) ha.le hb.le hab
        simp only [smul_eq_mul] at this ⊢
        calc Real.exp (-(a * x + b * y) * c) = Real.exp (a * (-x * c) + b * (-y * c)) := by
              ring_nf
          _ ≤ _ := this
          _ = _ := by ring_nf
    · intro v hv1 hv2
      rcases phi_cases D hmono v with ⟨h1, _⟩ | ⟨c, _, hc1, hc⟩
      · linarith
      · have hc' := hc1 hv1
        rw [hc _ hz, hc _ hx', hc _ hy']
        have hne : -x * c ≠ -y * c := by
          intro h
          apply hxy
          have : c ≠ 0 := by linarith
          have := mul_right_cancel₀ this h
          linarith
        have := strictConvexOn_exp.2 (mem_univ (-x * c)) (mem_univ (-y * c)) hne ha hb hab
        simp only [smul_eq_mul] at this ⊢
        calc Real.exp (-(a * x + b * y) * c) = Real.exp (a * (-x * c) + b * (-y * c)) := by
              ring_nf
          _ < _ := this
          _ = _ := by ring_nf
  · intro x hx y hy hxy
    have hx' : (0 : ℝ) < x := hx
    have hy' : (0 : ℝ) < y := hy
    obtain ⟨ex, ix⟩ := layer D hD0 hmono hint _ hx'
    obtain ⟨ey, iy⟩ := layer D hD0 hmono hint _ hy'
    rw [ex, ey]
    refine int_lt_of _ _ iy ix _ _ hp hpq ?_ ?_
    · intro v hv
      rcases phi_cases D hmono v with ⟨_, h0⟩ | ⟨c, hc0, _, hc⟩
      · rw [h0 _ hx', h0 _ hy']
      · rw [hc _ hx', hc _ hy']
        exact Real.exp_le_exp.2 (by nlinarith)
    · intro v hv1 hv2
      rcases phi_cases D hmono v with ⟨h1, _⟩ | ⟨c, _, hc1, hc⟩
      · linarith
      · have hc' := hc1 hv1
        rw [hc _ hx', hc _ hy']
        exact Real.exp_lt_exp.2 (by nlinarith)

end LC1Aux73877692

theorem solution (M : DimCallCenters.Rationalized.WaitModel) (lam : ℝ) (hlam : 0 < lam) :
    StrictConvexOn ℝ (Set.Ioi 0) (DimCallCenters.Rationalized.Glam M lam) ∧ StrictAntiOn (DimCallCenters.Rationalized.Glam M lam) (Set.Ioi 0) := by
  have hμ := M.hμ
  set c : ℝ := Real.sqrt (lam / M.μ) * M.μ with hcdef
  have hc : 0 < c := by
    have : 0 < Real.sqrt (lam / M.μ) := Real.sqrt_pos.2 (div_pos hlam hμ)
    positivity
  have key : ∀ x, DimCallCenters.Rationalized.Glam M lam x = lam * LC1Aux73877692.Hf (M.D lam) (c * x) := by
    intro x
    have h : DimCallCenters.Rationalized.servers M.μ lam x * M.μ - lam = c * x := by
      unfold DimCallCenters.Rationalized.servers
      rw [hcdef]
      field_simp
      ring
    rw [DimCallCenters.Rationalized.Glam, DimCallCenters.Rationalized.waitCost, h]
    rfl
  obtain ⟨hcv, han⟩ := LC1Aux73877692.H_main (M.D lam) (M.hD0 lam hlam) (M.hDmono lam hlam) (M.hDint lam hlam)
  refine ⟨⟨convex_Ioi 0, ?_⟩, ?_⟩
  · intro x hx y hy hxy a b ha hb hab
    have hx' : (0 : ℝ) < x := hx
    have hy' : (0 : ℝ) < y := hy
    have hcx : c * x ∈ Set.Ioi (0 : ℝ) := mul_pos hc hx'
    have hcy : c * y ∈ Set.Ioi (0 : ℝ) := mul_pos hc hy'
    have hne : c * x ≠ c * y := fun h => hxy (mul_left_cancel₀ hc.ne' h)
    have := hcv.2 hcx hcy hne ha hb hab
    rw [key, key, key]
    simp only [smul_eq_mul] at this ⊢
    have e : c * (a * x + b * y) = a * (c * x) + b * (c * y) := by ring
    rw [e]
    nlinarith
  · intro x hx y hy hxy
    have hx' : (0 : ℝ) < x := hx
    have hy' : (0 : ℝ) < y := hy
    have := han (mul_pos hc hx') (mul_pos hc hy') (mul_lt_mul_of_pos_left hxy hc)
    rw [key, key]
    nlinarith
