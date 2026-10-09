-- Prove2me | solution 1 for DimCallCenters.Rationalized.theorem_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T01:09:42.553496+00:00
-- url     : https://prove2.me/submissions/43f09974-6d8f-4597-a824-fd1d926ca792

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Flam
import Definitions.Def_DimCallCenters_Rationalized_Glam
import Definitions.Def_DimCallCenters_Rationalized_surrogate
import Definitions.Def_DimCallCenters_Rationalized_delayFn
import Definitions.Def_DimCallCenters_Rationalized_staffCost

set_option autoImplicit false

open Filter Topology

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

theorem LC1_glam (M : DimCallCenters.Rationalized.WaitModel) (lam : ℝ) (hlam : 0 < lam) :
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

namespace DimCC1e7
open DimCallCenters.Rationalized

lemma erlang_pos_le (N : ℕ) (ν : ℝ) (hν : 0 < ν) (hN : ν < N) :
    0 < erlangC N ν ∧ erlangC N ν ≤ 1 ∧
      1 / erlangC N ν - 1 = (1 - ν / N) * (∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ)) /
        (ν ^ N / (N.factorial : ℝ)) := by
  have hNpos : (0 : ℝ) < N := lt_trans hν hN
  have ha : 0 < ν ^ N / (N.factorial : ℝ) := by positivity
  have hq : 0 < 1 - ν / N := by rw [sub_pos, div_lt_one hNpos]; exact hN
  have hb : 0 ≤ ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ) :=
    Finset.sum_nonneg (fun n _ => by positivity)
  set a := ν ^ N / (N.factorial : ℝ)
  set b := ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ)
  set q := 1 - ν / N
  have hden : 0 < q * b + a := by nlinarith
  have hE : erlangC N ν = a * (q * b + a)⁻¹ := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hE]; positivity
  · rw [hE, ← div_eq_mul_inv, div_le_one hden]; nlinarith
  · rw [hE]; field_simp; ring

lemma erlangC_pos (ν : ℝ) (hν : 0 < ν) (N : ℕ) (h : ν < (N : ℝ)) : 0 < erlangC N ν :=
  (erlang_pos_le N ν hν h).1

lemma erlangC_succ_le (ν : ℝ) (hν : 0 < ν) (N : ℕ) (h : ν < (N : ℝ)) :
    erlangC (N + 1) ν ≤ erlangC N ν := by
  have h' : ν < ((N + 1 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨p0, -, e0⟩ := erlang_pos_le N ν hν h
  obtain ⟨p1, -, e1⟩ := erlang_pos_le (N + 1) ν hν h'
  have hNpos : (0 : ℝ) < N := lt_trans hν h
  set S := ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ) with hS
  set a := ν ^ N / (N.factorial : ℝ) with ha
  have ha0 : 0 < a := by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun n _ => by positivity)
  have hS1 : ∑ n ∈ Finset.range (N + 1), ν ^ n / (n.factorial : ℝ) = S + a := by
    rw [Finset.sum_range_succ]
  have ha1 : ν ^ (N + 1) / ((N + 1).factorial : ℝ) = a * ν / (N + 1) := by
    rw [ha, Nat.factorial_succ, pow_succ]; push_cast; field_simp
  rw [hS1, ha1] at e1
  set T := S / a with hT
  have hT0 : 0 ≤ T := div_nonneg hS0 ha0.le
  have e0' : 1 / erlangC N ν - 1 = ((N - ν) / N) * T := by
    rw [e0, hT]; field_simp
  have e1' : 1 / erlangC (N + 1) ν - 1 = ((N + 1 - ν) / ν) * (T + 1) := by
    rw [e1, hT]; push_cast; field_simp
  have hc : (N - ν) / N ≤ (N + 1 - ν) / ν := by
    rw [div_le_div_iff₀ hNpos hν]; nlinarith
  have hc0 : 0 ≤ (N - ν) / N := div_nonneg (by linarith) hNpos.le
  have key : 1 / erlangC N ν ≤ 1 / erlangC (N + 1) ν := by
    have : ((N - ν) / N) * T ≤ ((N + 1 - ν) / ν) * (T + 1) :=
      mul_le_mul hc (by linarith) hT0 (le_trans hc0 hc)
    linarith
  rwa [one_div_le_one_div p0 p1] at key

theorem erlangC_anti (ν : ℝ) (hν : 0 < ν) (N1 N2 : ℕ) (h1 : ν < (N1 : ℝ)) (h12 : N1 ≤ N2) :
    erlangC N2 ν ≤ erlangC N1 ν := by
  induction N2, h12 using Nat.le_induction with
  | base => exact le_rfl
  | succ n hn ih =>
    have : ν < (n : ℝ) := lt_of_lt_of_le h1 (by exact_mod_cast hn)
    exact le_trans (erlangC_succ_le ν hν n this) ih

end DimCC1e7

namespace DimCC1e7
open DimCallCenters.Rationalized MeasureTheory Filter Topology

lemma stdPdf_pos (x : ℝ) : 0 < stdPdf x := by unfold stdPdf; positivity

lemma stdPdf_neg (x : ℝ) : stdPdf (-x) = stdPdf x := by unfold stdPdf; rw [neg_sq]

lemma stdPdf_eq (x : ℝ) : stdPdf x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2) := by
  unfold stdPdf; congr 2; ring

lemma stdPdf_int : Integrable stdPdf := by
  have : stdPdf = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2) :=
    funext stdPdf_eq
  rw [this]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul _

lemma stdPdf_total : ∫ x, stdPdf x = 1 := by
  have : stdPdf = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2) :=
    funext stdPdf_eq
  rw [this, integral_const_mul, integral_gaussian]
  have h1 : Real.pi / (1/2) = 2 * Real.pi := by ring
  rw [h1]
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-- `Q x = 1 - Φ(-x) = ∫_{(-x,∞)} φ`. -/
lemma one_sub_cdf (x : ℝ) : 1 - stdCdf (-x) = ∫ t in Set.Ioi (-x), stdPdf t := by
  unfold stdCdf
  rw [← stdPdf_total, ← integral_add_compl (measurableSet_Iic (a := -x)) stdPdf_int,
    Set.compl_Iic]
  ring

lemma Q_mono {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Set.Ioi (-a), stdPdf t ≤ ∫ t in Set.Ioi (-b), stdPdf t := by
  apply setIntegral_mono_set stdPdf_int.integrableOn
  · exact Eventually.of_forall (fun t => (stdPdf_pos t).le)
  · exact Eventually.of_forall (Set.Ioi_subset_Ioi (by linarith))

lemma Q_pos (x : ℝ) : 0 < ∫ t in Set.Ioi (-x), stdPdf t := by
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall (fun t => (stdPdf_pos t).le)) stdPdf_int.integrableOn]
  have : Function.support stdPdf = Set.univ :=
    Set.eq_univ_of_forall (fun t => (stdPdf_pos t).ne')
  rw [this, Set.univ_inter, Real.volume_Ioi]
  exact ENNReal.zero_lt_top

lemma ratio_eq (x : ℝ) :
    x / hazard (-x) = x * (∫ t in Set.Ioi (-x), stdPdf t) / stdPdf x := by
  unfold hazard
  rw [stdPdf_neg, one_sub_cdf, div_div_eq_mul_div]

lemma stdPdf_anti {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : stdPdf b ≤ stdPdf a := by
  unfold stdPdf
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.2
  nlinarith

lemma g_mono {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a / hazard (-a) ≤ b / hazard (-b) := by
  rw [ratio_eq, ratio_eq]
  have hQ := Q_mono hab
  have hQa := Q_pos a
  have hpa := stdPdf_pos a
  have hpb := stdPdf_pos b
  have h1 : a * (∫ t in Set.Ioi (-a), stdPdf t) ≤ b * (∫ t in Set.Ioi (-b), stdPdf t) :=
    mul_le_mul hab hQ hQa.le (by linarith)
  calc a * (∫ t in Set.Ioi (-a), stdPdf t) / stdPdf a
      ≤ b * (∫ t in Set.Ioi (-b), stdPdf t) / stdPdf a := div_le_div_of_nonneg_right h1 hpa.le
    _ ≤ b * (∫ t in Set.Ioi (-b), stdPdf t) / stdPdf b :=
        div_le_div_of_nonneg_left (mul_nonneg (by linarith) (Q_pos b).le) hpb
          (stdPdf_anti ha hab)

lemma g_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ x / hazard (-x) := by
  rw [ratio_eq]; exact div_nonneg (mul_nonneg hx (Q_pos x).le) (stdPdf_pos x).le

theorem delayFn_props : AntitoneOn delayFn (Set.Ici 0) ∧ (∀ x : ℝ, 0 ≤ x → 0 < delayFn x) ∧
    Tendsto delayFn atTop (𝓝 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    have ha' : (0:ℝ) ≤ a := ha
    unfold delayFn
    exact one_div_le_one_div_of_le (by linarith [g_nonneg ha']) (by linarith [g_mono ha' hab])
  · intro x hx
    unfold delayFn
    have := g_nonneg hx
    positivity
  · set c := (∫ t in Set.Ioi (-0 : ℝ), stdPdf t) / stdPdf 0 with hc
    have hc0 : 0 < c := div_pos (Q_pos 0) (stdPdf_pos 0)
    have hlow : ∀ᶠ x in atTop, c * x ≤ 1 + x / hazard (-x) := by
      filter_upwards [eventually_ge_atTop 0] with x hx
      rw [ratio_eq]
      have hQ := Q_mono hx
      have hp := stdPdf_anti (le_refl 0) hx
      have hpx := stdPdf_pos x
      have h1 : c * x ≤ x * (∫ t in Set.Ioi (-x), stdPdf t) / stdPdf x := by
        rw [hc, div_mul_eq_mul_div, mul_comm (∫ t in Set.Ioi (-0 : ℝ), stdPdf t) x]
        calc x * (∫ t in Set.Ioi (-0 : ℝ), stdPdf t) / stdPdf 0
            ≤ x * (∫ t in Set.Ioi (-x), stdPdf t) / stdPdf 0 :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hQ hx) (stdPdf_pos 0).le
          _ ≤ x * (∫ t in Set.Ioi (-x), stdPdf t) / stdPdf x :=
              div_le_div_of_nonneg_left (mul_nonneg hx (Q_pos x).le) hpx hp
      linarith
    have hinf : Tendsto (fun x => 1 + x / hazard (-x)) atTop atTop :=
      tendsto_atTop_mono' atTop hlow (tendsto_id.const_mul_atTop hc0)
    have := tendsto_inv_atTop_zero.comp hinf
    unfold delayFn
    simp only [one_div]
    exact this

end DimCC1e7

section HWsec
open Filter Topology MeasureTheory Set

namespace DimCC1e7h

noncomputable def Fi (ν x w : ℝ) : ℝ :=
  w * Real.exp (-Real.sqrt ν * w) * (1 + w / Real.sqrt ν) ^ (ν + x * Real.sqrt ν - 1)

noncomputable def Gi (x w : ℝ) : ℝ := w * Real.exp (x * w - w ^ 2 / 2)

noncomputable def Ex (ν x w : ℝ) : ℝ :=
  -Real.sqrt ν * w + (ν + x * Real.sqrt ν - 1) * Real.log (1 + w / Real.sqrt ν)

noncomputable def bnd (B w : ℝ) : ℝ :=
  Real.exp (3 * B ^ 2) * (w * Real.exp (-(1/12) * w ^ 2)) + w ^ 1 * Real.exp (-1 * w)

lemma log_le_aux (t : ℝ) (ht : 0 ≤ t) : Real.log (1 + t) ≤ t - t ^ 2 / (2 * (2 + t)) := by
  have h1 : Real.log (1 + t / 2) ≤ t / 2 := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + t / 2 by positivity); linarith
  have h2 : Real.log ((1 + t) / (1 + t / 2)) ≤ t / (2 + t) := by
    have := Real.log_le_sub_one_of_pos (show 0 < (1 + t) / (1 + t / 2) by positivity)
    have e : (1 + t) / (1 + t / 2) - 1 = t / (2 + t) := by field_simp; ring
    linarith
  have h3 : Real.log (1 + t) = Real.log (1 + t / 2) + Real.log ((1 + t) / (1 + t / 2)) := by
    rw [← Real.log_mul (by positivity) (by positivity)]; congr 1; field_simp
  have e2 : t / 2 + t / (2 + t) = t - t ^ 2 / (2 * (2 + t)) := by field_simp; ring
  linarith

lemma Fi_eq (ν x w : ℝ) (hν : 0 < ν) (hw : 0 ≤ w) : Fi ν x w = w * Real.exp (Ex ν x w) := by
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  unfold Fi Ex
  rw [Real.rpow_def_of_pos (by positivity), Real.exp_add, mul_comm (Real.log _) _]
  ring

/-- Uniform domination of the scaled Erlang integrand. -/
lemma exp_Ex_le (B ν x w : ℝ) (hB : 0 < B) (hν1 : 1 ≤ ν) (hs6 : 6 * (B + 1) ≤ Real.sqrt ν)
    (hx0 : 0 ≤ x) (hxB : x ≤ B) (hw : 0 < w) :
    Real.exp (Ex ν x w) ≤ Real.exp (3 * B ^ 2) * Real.exp (-(1/12) * w ^ 2) + Real.exp (-1 * w) := by
  set s := Real.sqrt ν with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = ν := Real.sq_sqrt (by linarith)
  set t := w / s with ht_def
  have ht : 0 ≤ t := by positivity
  have hL0 : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
  have hLt : Real.log (1 + t) ≤ t := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith); linarith
  have hLb := log_le_aux t ht
  have ha : 0 ≤ ν + x * s - 1 := by nlinarith
  have hQ : ν * (t ^ 2 / (2 * (2 + t))) = w ^ 2 * s / (2 * (2 * s + w)) := by
    rw [← hs2, ht_def]; field_simp
  have hνt : ν * t = s * w := by rw [← hs2, ht_def]; field_simp
  have hxt : x * s * t = x * w := by rw [ht_def]; field_simp
  -- Ex ≤ x w - Q
  have hE : Ex ν x w ≤ B * w - w ^ 2 * s / (2 * (2 * s + w)) := by
    have e1 : (ν + x * s - 1) * Real.log (1 + t) ≤ (ν + x * s) * Real.log (1 + t) := by nlinarith
    have e2 : ν * Real.log (1 + t) ≤ ν * (t - t ^ 2 / (2 * (2 + t))) :=
      mul_le_mul_of_nonneg_left hLb (by linarith)
    have e3 : x * s * Real.log (1 + t) ≤ x * s * t :=
      mul_le_mul_of_nonneg_left hLt (by positivity)
    have e4 : x * w ≤ B * w := mul_le_mul_of_nonneg_right hxB hw.le
    have : Ex ν x w = -s * w + (ν + x * s - 1) * Real.log (1 + t) := rfl
    rw [this]
    have e5 : ν * (t - t ^ 2 / (2 * (2 + t))) = s * w - w ^ 2 * s / (2 * (2 * s + w)) := by
      rw [mul_sub, hνt, hQ]
    nlinarith
  have hpos : 0 < 2 * (2 * s + w) := by positivity
  rcases le_or_gt w s with hws | hws
  · have hq : w ^ 2 / 6 ≤ w ^ 2 * s / (2 * (2 * s + w)) := by
      rw [div_le_div_iff₀ (by norm_num) hpos]; nlinarith [sq_nonneg w]
    have : Ex ν x w ≤ 3 * B ^ 2 + (-(1/12) * w ^ 2) := by nlinarith [sq_nonneg (w - 6 * B)]
    calc Real.exp (Ex ν x w) ≤ Real.exp (3 * B ^ 2 + (-(1/12) * w ^ 2)) := Real.exp_le_exp.2 this
      _ = Real.exp (3 * B ^ 2) * Real.exp (-(1/12) * w ^ 2) := Real.exp_add _ _
      _ ≤ _ := le_add_of_nonneg_right (Real.exp_pos _).le
  · have hq : w * s / 6 ≤ w ^ 2 * s / (2 * (2 * s + w)) := by
      rw [div_le_div_iff₀ (by norm_num) hpos]; nlinarith [mul_pos hw hs]
    have h6 : (B + 1) * w ≤ w * s / 6 := by nlinarith
    have : Ex ν x w ≤ -1 * w := by nlinarith
    calc Real.exp (Ex ν x w) ≤ Real.exp (-1 * w) := Real.exp_le_exp.2 this
      _ ≤ _ := le_add_of_nonneg_left (by positivity)

lemma Fi_le (B ν x w : ℝ) (hB : 0 < B) (hν1 : 1 ≤ ν) (hs6 : 6 * (B + 1) ≤ Real.sqrt ν)
    (hx0 : 0 ≤ x) (hxB : x ≤ B) (hw : 0 < w) : ‖Fi ν x w‖ ≤ bnd B w := by
  rw [Fi_eq ν x w (by linarith) hw.le, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have := exp_Ex_le B ν x w hB hν1 hs6 hx0 hxB hw
  unfold bnd
  rw [pow_one]
  nlinarith

lemma Gi_le (B x w : ℝ) (hx0 : 0 ≤ x) (hxB : x ≤ B) (hw : 0 < w) : ‖Gi x w‖ ≤ bnd B w := by
  unfold Gi bnd
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_one]
  have h1 : x * w - w ^ 2 / 2 ≤ 3 * B ^ 2 + (-(1/12) * w ^ 2) := by
    nlinarith [sq_nonneg (w - 6 * B), mul_le_mul_of_nonneg_right hxB hw.le]
  have h2 : Real.exp (x * w - w ^ 2 / 2) ≤ Real.exp (3 * B ^ 2) * Real.exp (-(1/12) * w ^ 2) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 h1
  have h3 : 0 ≤ w * Real.exp (-1 * w) := by positivity
  nlinarith

lemma bnd_int (B : ℝ) : IntegrableOn (bnd B) (Ioi 0) := by
  unfold bnd
  refine Integrable.add ?_ ?_
  · exact ((integrable_mul_exp_neg_mul_sq (b := 1/12) (by norm_num)).const_mul _).integrableOn
  · have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (1 : ℝ)) (p := 1) (b := 1)
      (by norm_num) one_pos one_pos
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [Real.rpow_one]

/-- Pointwise error of the exponent. -/
lemma Ex_err (ν x w : ℝ) (hν : 0 < ν) (hw : 0 < w) (ht4 : w / Real.sqrt ν ≤ 1 / 4) :
    |Ex ν x w - (x * w - w ^ 2 / 2)| ≤ (2 * w ^ 3 + |x| * w ^ 2 + w) * (Real.sqrt ν)⁻¹ := by
  set s := Real.sqrt ν with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hν
  have hs2 : s ^ 2 = ν := Real.sq_sqrt hν.le
  set t := w / s with ht_def
  have ht : 0 < t := by positivity
  have hwst : w = s * t := by rw [ht_def]; field_simp
  set L := Real.log (1 + t) with hL_def
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hLt : L ≤ t := by
    have := Real.log_le_sub_one_of_pos (show 0 < 1 + t by linarith); linarith
  have hT := Real.abs_log_sub_add_sum_range_le (x := -t) (by rw [abs_neg, abs_of_pos ht]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_pos ht] at hT
  have hr : |L - t + t ^ 2 / 2| ≤ 2 * t ^ 3 := by
    have e : (0 + (-t) ^ (0 + 1) / ((0:ℕ) + 1 : ℝ) + (-t) ^ (1 + 1) / ((1:ℕ) + 1 : ℝ)
        + Real.log (1 - -t)) = L - t + t ^ 2 / 2 := by
      rw [hL_def, sub_neg_eq_add]; push_cast; ring
    rw [e, show (2:ℕ) + 1 = 3 from rfl] at hT
    refine hT.trans ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_pos ht 3, ht4]
  set r := L - t + t ^ 2 / 2 with hr_def
  have hLt2 : |L - t| ≤ t ^ 2 := by
    have : L - t = r - t ^ 2 / 2 := by rw [hr_def]; ring
    rw [this]
    calc |r - t ^ 2 / 2| ≤ |r| + |t ^ 2 / 2| := abs_sub _ _
      _ ≤ 2 * t ^ 3 + t ^ 2 / 2 := by rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2 / 2)]; linarith
      _ ≤ t ^ 2 := by nlinarith [sq_nonneg t]
  have key : Ex ν x w - (x * w - w ^ 2 / 2) = s ^ 2 * r + x * s * (L - t) - L := by
    have : Ex ν x w = -s * w + (ν + x * s - 1) * L := rfl
    rw [this, ← hs2, hwst, hr_def]; ring
  rw [key]
  calc |s ^ 2 * r + x * s * (L - t) - L| ≤ |s ^ 2 * r + x * s * (L - t)| + |L| := abs_sub _ _
    _ ≤ |s ^ 2 * r| + |x * s * (L - t)| + |L| := by gcongr; exact abs_add_le _ _
    _ = s ^ 2 * |r| + |x| * s * |L - t| + L := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_pos hs, abs_of_nonneg hL0, abs_of_pos (by positivity : 0 < s ^ 2)]
    _ ≤ s ^ 2 * (2 * t ^ 3) + |x| * s * t ^ 2 + t := by
        gcongr
    _ = (2 * w ^ 3 + |x| * w ^ 2 + w) * s⁻¹ := by rw [hwst]; field_simp


lemma Ex_tendsto (w xs : ℝ) (hw : 0 < w) :
    Tendsto (fun q : ℝ × ℝ => Ex q.1 q.2 w) (atTop ×ˢ 𝓝 xs) (𝓝 (xs * w - w ^ 2 / 2)) := by
  have h1 : Tendsto (fun q : ℝ × ℝ => q.2) (atTop ×ˢ 𝓝 xs) (𝓝 xs) := tendsto_snd
  have h2 : Tendsto (fun q : ℝ × ℝ => (Real.sqrt q.1)⁻¹) (atTop ×ˢ 𝓝 xs) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_fst)
  have hg : Tendsto (fun q : ℝ × ℝ => |q.2 - xs| * w + (2 * w ^ 3 + |q.2| * w ^ 2 + w) * (Real.sqrt q.1)⁻¹)
      (atTop ×ˢ 𝓝 xs) (𝓝 0) := by
    have := (((h1.sub_const xs).abs).mul_const w).add
      (((((h1.abs).mul_const (w ^ 2)).const_add (2 * w ^ 3)).add_const w).mul h2)
    simpa using this
  have hev : ∀ᶠ q : ℝ × ℝ in atTop ×ˢ 𝓝 xs, ‖Ex q.1 q.2 w - (xs * w - w ^ 2 / 2)‖ ≤
      |q.2 - xs| * w + (2 * w ^ 3 + |q.2| * w ^ 2 + w) * (Real.sqrt q.1)⁻¹ := by
    filter_upwards [tendsto_fst.eventually (eventually_ge_atTop (max 1 (16 * w ^ 2)))] with q hq
    have hq1 : 1 ≤ q.1 := le_trans (le_max_left _ _) hq
    have hq2 : 16 * w ^ 2 ≤ q.1 := le_trans (le_max_right _ _) hq
    have hν : 0 < q.1 := by linarith
    have hs : 4 * w ≤ Real.sqrt q.1 := Real.le_sqrt_of_sq_le (by nlinarith)
    have ht4 : w / Real.sqrt q.1 ≤ 1 / 4 := by
      rw [div_le_iff₀ (Real.sqrt_pos.2 hν)]; linarith
    have e := Ex_err q.1 q.2 w hν hw ht4
    have : Ex q.1 q.2 w - (xs * w - w ^ 2 / 2) =
        (Ex q.1 q.2 w - (q.2 * w - w ^ 2 / 2)) + (q.2 - xs) * w := by ring
    rw [Real.norm_eq_abs, this]
    calc _ ≤ |Ex q.1 q.2 w - (q.2 * w - w ^ 2 / 2)| + |(q.2 - xs) * w| := abs_add_le _ _
      _ ≤ _ := by rw [abs_mul, abs_of_pos hw]; linarith
  have h0 : Tendsto (fun q : ℝ × ℝ => Ex q.1 q.2 w - (xs * w - w ^ 2 / 2)) (atTop ×ˢ 𝓝 xs) (𝓝 0) :=
    squeeze_zero_norm' hev hg
  have h4 := h0.add_const (xs * w - w ^ 2 / 2)
  simp only [sub_add_cancel, zero_add] at h4
  exact h4

lemma Fi_tendsto (w xs : ℝ) (hw : 0 < w) :
    Tendsto (fun q : ℝ × ℝ => Fi q.1 q.2 w) (atTop ×ˢ 𝓝 xs) (𝓝 (Gi xs w)) := by
  have hE := (Real.continuous_exp.tendsto _).comp (Ex_tendsto w xs hw)
  have hm := hE.const_mul w
  rw [show Gi xs w = w * Real.exp (xs * w - w ^ 2 / 2) from rfl]
  refine hm.congr' ?_
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop 0)] with q hq
  exact (Fi_eq q.1 q.2 w hq hw.le).symm

lemma int_F_tendsto (B xs : ℝ) (hB : 0 < B) :
    Tendsto (fun q : ℝ × ℝ => ∫ w in Ioi (0:ℝ), Fi q.1 q.2 w) (atTop ×ˢ 𝓝[Icc 0 B] xs)
      (𝓝 (∫ w in Ioi (0:ℝ), Gi xs w)) := by
  refine tendsto_integral_filter_of_dominated_convergence (bnd B) ?_ ?_ (bnd_int B) ?_
  · exact Eventually.of_forall (fun q =>
      (by unfold Fi; fun_prop : Measurable (Fi q.1 q.2)).aestronglyMeasurable)
  · have hmem : ∀ᶠ q : ℝ × ℝ in atTop ×ˢ 𝓝[Icc 0 B] xs, q.2 ∈ Icc 0 B :=
      tendsto_snd.eventually self_mem_nhdsWithin
    filter_upwards [hmem, tendsto_fst.eventually (eventually_ge_atTop (max 1 (36 * (B + 1) ^ 2)))]
      with q hq hq1
    rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall (fun w hw => ?_)
    have hν1 : 1 ≤ q.1 := le_trans (le_max_left _ _) hq1
    have hν2 : 36 * (B + 1) ^ 2 ≤ q.1 := le_trans (le_max_right _ _) hq1
    have hs6 : 6 * (B + 1) ≤ Real.sqrt q.1 := Real.le_sqrt_of_sq_le (by nlinarith)
    exact Fi_le B q.1 q.2 w hB hν1 hs6 hq.1 hq.2 hw
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall (fun w hw => ?_)
    exact (Fi_tendsto w xs hw).mono_left (Filter.prod_mono le_rfl nhdsWithin_le_nhds)

lemma int_G_tendsto (B xs : ℝ) :
    Tendsto (fun x => ∫ w in Ioi (0:ℝ), Gi x w) (𝓝[Icc 0 B] xs) (𝓝 (∫ w in Ioi (0:ℝ), Gi xs w)) := by
  refine tendsto_integral_filter_of_dominated_convergence (bnd B) ?_ ?_ (bnd_int B) ?_
  · exact Eventually.of_forall (fun x =>
      (by unfold Gi; fun_prop : Continuous (Gi x)).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall (fun w hw => Gi_le B x w hx.1 hx.2 hw)
  · refine Eventually.of_forall (fun w => ?_)
    have : Continuous (fun x => Gi x w) := by unfold Gi; fun_prop
    exact this.continuousAt.tendsto.mono_left nhdsWithin_le_nhds

lemma unif (B : ℝ) (hB : 0 < B) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ ν in atTop, ∀ x ∈ Icc 0 B, |(∫ w in Ioi (0:ℝ), Fi ν x w) - ∫ w in Ioi (0:ℝ), Gi x w| < δ := by
  have hloc : TendstoLocallyUniformlyOn (fun ν x => ∫ w in Ioi (0:ℝ), Fi ν x w)
      (fun x => ∫ w in Ioi (0:ℝ), Gi x w) atTop (Icc 0 B) := by
    rw [tendstoLocallyUniformlyOn_iff_filter]
    intro xs _
    rw [Metric.tendstoUniformlyOnFilter_iff]
    intro ε hε
    have hG := (int_G_tendsto B xs).comp (tendsto_snd (f := (atTop : Filter ℝ)))
    have h := hG.sub (int_F_tendsto B xs hB)
    rw [sub_self] at h
    filter_upwards [Metric.tendsto_nhds.1 h ε hε] with q hq
    rw [Real.dist_eq] at hq ⊢
    simpa using hq
  have hu := (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_Icc).1 hloc
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu δ hδ] with ν hν x hx
  have := hν x hx
  rw [Real.dist_eq, abs_sub_comm] at this
  exact this

end DimCC1e7h

namespace DimCC1e7h
open DimCallCenters.Rationalized

lemma stdPdf_pos (x : ℝ) : 0 < stdPdf x := by unfold stdPdf; positivity

lemma stdPdf_neg (x : ℝ) : stdPdf (-x) = stdPdf x := by unfold stdPdf; rw [neg_sq]

lemma stdPdf_eq (x : ℝ) : stdPdf x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2) := by
  unfold stdPdf; congr 2; ring

lemma stdPdf_int : Integrable stdPdf := by
  have : stdPdf = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2) :=
    funext stdPdf_eq
  rw [this]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)).const_mul _

lemma stdPdf_total : ∫ x, stdPdf x = 1 := by
  have : stdPdf = fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2) :=
    funext stdPdf_eq
  rw [this, integral_const_mul, integral_gaussian]
  have h1 : Real.pi / (1/2) = 2 * Real.pi := by ring
  rw [h1]
  have : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  field_simp

/-- `Q x = 1 - Φ(-x) = ∫_{(-x,∞)} φ`. -/
lemma one_sub_cdf (x : ℝ) : 1 - stdCdf (-x) = ∫ t in Set.Ioi (-x), stdPdf t := by
  unfold stdCdf
  rw [← stdPdf_total, ← integral_add_compl (measurableSet_Iic (a := -x)) stdPdf_int,
    Set.compl_Iic]
  ring

lemma ratio_eq (x : ℝ) :
    x / hazard (-x) = x * (∫ t in Set.Ioi (-x), stdPdf t) / stdPdf x := by
  unfold hazard
  rw [stdPdf_neg, one_sub_cdf, div_div_eq_mul_div]


lemma gauss_shift (x : ℝ) : ∫ w in Ioi (0:ℝ), stdPdf (w - x) = ∫ u in Ioi (-x), stdPdf u := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  refine Eq.trans ?_ (integral_sub_right_eq_self (μ := volume) (fun u => (Ioi (-x)).indicator stdPdf u) x)
  congr 1
  ext w
  simp only [Set.indicator, Set.mem_Ioi]
  by_cases h : 0 < w
  · rw [if_pos h, if_pos (by linarith)]
  · rw [if_neg h, if_neg (by linarith)]

lemma pdf_shift (x w : ℝ) : stdPdf (w - x) = stdPdf x * Real.exp (x * w - w ^ 2 / 2) := by
  unfold stdPdf; rw [mul_assoc, ← Real.exp_add]; congr 2; ring

lemma exp_quad_le (x w : ℝ) :
    Real.exp (x * w - w ^ 2 / 2) ≤ Real.exp (x ^ 2) * Real.exp (-(1/4) * w ^ 2) := by
  rw [← Real.exp_add]; apply Real.exp_le_exp.2; nlinarith [sq_nonneg (w - 2 * x)]

lemma int_e (x : ℝ) : Integrable (fun w => Real.exp (x * w - w ^ 2 / 2)) := by
  refine Integrable.mono' ((integrable_exp_neg_mul_sq (b := 1/4) (by norm_num)).const_mul
    (Real.exp (x ^ 2))) (by fun_prop : Continuous _).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]; exact exp_quad_le x w

lemma int_we (x : ℝ) : Integrable (fun w => w * Real.exp (x * w - w ^ 2 / 2)) := by
  refine Integrable.mono' (((integrable_mul_exp_neg_mul_sq (b := 1/4) (by norm_num)).norm).const_mul
    (Real.exp (x ^ 2))) (by fun_prop : Continuous _).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos (x * w - _)),
    abs_of_pos (Real.exp_pos (-(1/4) * w ^ 2))]
  have := exp_quad_le x w
  calc |w| * Real.exp (x * w - w ^ 2 / 2)
      ≤ |w| * (Real.exp (x ^ 2) * Real.exp (-(1/4) * w ^ 2)) :=
        mul_le_mul_of_nonneg_left this (abs_nonneg w)
    _ = _ := by ring

lemma int_sub (x : ℝ) : Integrable (fun w => (w - x) * Real.exp (x * w - w ^ 2 / 2)) := by
  have := (int_we x).sub ((int_e x).const_mul x)
  refine this.congr (Eventually.of_forall fun w => ?_)
  simp only [Pi.sub_apply]; ring

lemma ibp (x : ℝ) : ∫ w in Ioi (0:ℝ), (w - x) * Real.exp (x * w - w ^ 2 / 2) = 1 := by
  have hlim : Tendsto (fun w : ℝ => -Real.exp (x * w - w ^ 2 / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun w : ℝ => -(1/4) * w ^ 2) atTop atBot := by
      have := (tendsto_pow_atTop (two_ne_zero)).const_mul_atTop (show (0:ℝ) < 1/4 by norm_num)
      have h2 := tendsto_neg_atTop_atBot.comp this
      refine h2.congr (fun w => ?_)
      simp [neg_mul]
    have h2 := (Real.tendsto_exp_atBot.comp h1).const_mul (Real.exp (x ^ 2))
    rw [mul_zero] at h2
    have h3 : Tendsto (fun w : ℝ => Real.exp (x * w - w ^ 2 / 2)) atTop (𝓝 0) :=
      squeeze_zero (fun w => (Real.exp_pos _).le) (fun w => exp_quad_le x w) h2
    simpa using h3.neg
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun w => -Real.exp (x * w - w ^ 2 / 2))
    (f' := fun w => (w - x) * Real.exp (x * w - w ^ 2 / 2)) (a := 0) (m := 0)
    (by fun_prop : Continuous fun w : ℝ => -Real.exp (x * w - w ^ 2 / 2)).continuousWithinAt
    (fun w _ => by
      have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * w) w := by simpa using hasDerivAt_pow 2 w
      have hd : HasDerivAt (fun w : ℝ => x * w - w ^ 2 / 2) (x - w) w := by
        have := ((hasDerivAt_id' w).const_mul x).sub (hp.div_const 2)
        exact this.congr_deriv (by ring)
      have h2 : HasDerivAt (fun w => -Real.exp (x * w - w ^ 2 / 2))
          (-(Real.exp (x * w - w ^ 2 / 2) * (x - w))) w := hd.exp.neg
      show HasDerivAt _ ((w - x) * Real.exp (x * w - w ^ 2 / 2)) w
      exact h2.congr_deriv (by ring))
    (int_sub x).integrableOn hlim
  rw [h]; simp

lemma inv_delay (x : ℝ) : 1 / delayFn x = ∫ w in Ioi (0:ℝ), Gi x w := by
  have hshift : ∫ w in Ioi (0:ℝ), Real.exp (x * w - w ^ 2 / 2)
      = (∫ u in Ioi (-x), stdPdf u) / stdPdf x := by
    rw [← gauss_shift, eq_div_iff (stdPdf_pos x).ne', mul_comm, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
    rw [pdf_shift]
  have hsplit : ∫ w in Ioi (0:ℝ), Gi x w = (∫ w in Ioi (0:ℝ), (w - x) * Real.exp (x * w - w ^ 2 / 2))
      + x * ∫ w in Ioi (0:ℝ), Real.exp (x * w - w ^ 2 / 2) := by
    rw [← integral_const_mul, ← integral_add ((int_sub x).integrableOn)
      (((int_e x).const_mul x).integrableOn)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
    unfold Gi; ring
  rw [hsplit, ibp, hshift]
  unfold delayFn
  rw [one_div_one_div, ratio_eq]; ring

lemma intOn_pow (k : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-a * t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (k : ℝ)) (p := 1) (b := a)
    (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) one_pos ha
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast, Real.rpow_one]

lemma int_pow (k : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0:ℝ), t ^ k * Real.exp (-a * t) = (k.factorial : ℝ) / a ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := a)
    (by positivity) ha
  have h2 : ∫ t in Ioi (0:ℝ), t ^ k * Real.exp (-a * t)
      = ∫ t in Ioi (0:ℝ), t ^ ((k : ℝ) + 1 - 1) * Real.exp (-(a * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp [Real.rpow_natCast, neg_mul]
  rw [h2, h]
  have hG : Real.Gamma ((k : ℝ) + 1) = (k.factorial : ℝ) := Real.Gamma_nat_eq_factorial k
  rw [hG]
  have : (1 / a) ^ ((k : ℝ) + 1) = 1 / a ^ (k + 1) := by
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    rw [one_div_pow]
  rw [this]; ring

lemma integrand_eq (m : ℕ) (a t : ℝ) :
    Real.exp (-a * t) * (1 + t) ^ m
      = ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (t ^ k * Real.exp (-a * t)) := by
  rw [add_comm (1:ℝ) t, add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [one_pow]; ring

lemma intOn_A (m : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => Real.exp (-a * t) * (1 + t) ^ m) (Ioi 0) := by
  simp_rw [integrand_eq m a]
  exact integrable_finsetSum _ (fun k _ => (intOn_pow k ha).const_mul _)

lemma sum_eq (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * ((k.factorial : ℝ) / a ^ (k + 1))
      = (m.factorial : ℝ) / a ^ (m + 1) *
          ∑ j ∈ Finset.range (m + 1), a ^ j / (j.factorial : ℝ) := by
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsub : m + 1 - 1 - k = m - k := by omega
  rw [hsub]
  have hfac : ((m.choose k : ℕ) : ℝ) * (k.factorial : ℝ) * ((m - k).factorial : ℝ)
      = (m.factorial : ℝ) := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk'
  have hpow : a ^ (m + 1) = a ^ (k + 1) * a ^ (m - k) := by
    rw [← pow_add]; congr 1; omega
  rw [← hfac, hpow]
  have h1 : (0:ℝ) < (k.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos k
  have h2 : (0:ℝ) < ((m - k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  field_simp
  rw [Nat.choose_symm hk']
  ring

lemma int_A (m : ℕ) {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioi (0:ℝ), Real.exp (-a * t) * (1 + t) ^ m
      = (m.factorial : ℝ) / a ^ (m + 1) *
          ∑ j ∈ Finset.range (m + 1), a ^ j / (j.factorial : ℝ) := by
  simp_rw [integrand_eq m a]
  rw [integral_finsetSum _ (fun k _ => (intOn_pow k ha).const_mul _)]
  simp_rw [integral_const_mul, int_pow _ ha]
  exact sum_eq m ha


lemma contE (n : ℕ) (a : ℝ) (ha : 0 < a) :
    (a * ∫ t in Ioi (0:ℝ), Real.exp (-a * t) * t * (1 + t) ^ (((n + 1 : ℕ) : ℝ) - 1))⁻¹
      = erlangC (n + 1) a := by
  unfold erlangC
  have hint : ∫ t in Ioi (0:ℝ), Real.exp (-a * t) * t * (1 + t) ^ (((n + 1 : ℕ) : ℝ) - 1)
      = ∫ t in Ioi (0:ℝ), (Real.exp (-a * t) * (1 + t) ^ (n + 1)
          - Real.exp (-a * t) * (1 + t) ^ n) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    rw [show (((n + 1 : ℕ) : ℝ) - 1) = (n : ℝ) by push_cast; ring, Real.rpow_natCast]
    ring
  rw [hint, integral_sub (intOn_A _ ha) (intOn_A _ ha), int_A _ ha, int_A _ ha]
  rw [Finset.sum_range_succ (fun j => a ^ j / (j.factorial : ℝ)) (n + 1)]
  set S := ∑ j ∈ Finset.range (n + 1), a ^ j / (j.factorial : ℝ)
  rw [Nat.factorial_succ]
  push_cast
  have hf : (0:ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  rw [← inv_inv (a ^ (n + 1) / (((n:ℝ) + 1) * (n.factorial : ℝ))), ← mul_inv]
  congr 1
  field_simp
  ring

lemma scale (ν c : ℝ) (hν : 0 < ν) :
    ν * ∫ t in Ioi (0:ℝ), Real.exp (-ν * t) * t * (1 + t) ^ c =
      ∫ w in Ioi (0:ℝ), w * Real.exp (-Real.sqrt ν * w) * (1 + w / Real.sqrt ν) ^ c := by
  set s := Real.sqrt ν with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hν
  have hs2 : s ^ 2 = ν := Real.sq_sqrt hν.le
  have h : ∫ w in Ioi (0:ℝ), (fun t => Real.exp (-ν * t) * t * (1 + t) ^ c) (s⁻¹ * w)
      = s * ∫ t in Ioi (0:ℝ), Real.exp (-ν * t) * t * (1 + t) ^ c := by
    have := integral_comp_mul_left_Ioi (fun t => Real.exp (-ν * t) * t * (1 + t) ^ c) 0 (inv_pos.2 hs)
    rw [mul_zero, inv_inv, smul_eq_mul] at this
    exact this
  have e : ν * ∫ t in Ioi (0:ℝ), Real.exp (-ν * t) * t * (1 + t) ^ c
      = s * ∫ w in Ioi (0:ℝ), (fun t => Real.exp (-ν * t) * t * (1 + t) ^ c) (s⁻¹ * w) := by
    rw [h, ← mul_assoc, ← sq, hs2]
  rw [e, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun w _ => ?_)
  have e1 : -ν * (s⁻¹ * w) = -s * w := by rw [← hs2]; field_simp
  have hsw : s * (w / s) = w := by field_simp
  simp only
  rw [e1, show s⁻¹ * w = w / s by ring]
  rw [show s * (Real.exp (-s * w) * (w / s) * (1 + w / s) ^ c)
      = (s * (w / s)) * Real.exp (-s * w) * (1 + w / s) ^ c by ring, hsw]

theorem HW_diff (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ) :
    ∃ ν0 : ℝ, ∀ ν : ℝ, ν0 ≤ ν → ∀ N : ℕ, ν < (N : ℝ) → ((N : ℝ) - ν) / Real.sqrt ν ≤ B →
      |1 / erlangC N ν - 1 / delayFn (((N : ℝ) - ν) / Real.sqrt ν)| ≤ δ := by
  obtain ⟨ν0, hν0⟩ := eventually_atTop.1 (unif B hB δ hδ)
  refine ⟨max ν0 1, fun ν hν N hN hxB => ?_⟩
  have hνpos : 0 < ν := by linarith [le_max_right ν0 1]
  have hs : 0 < Real.sqrt ν := Real.sqrt_pos.2 hνpos
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := by
    have h0 : (0:ℝ) < N := by linarith
    have : 0 < N := by exact_mod_cast h0
    exact ⟨N - 1, by omega⟩
  set x := (((n + 1 : ℕ) : ℝ) - ν) / Real.sqrt ν with hx_def
  have hx0 : 0 ≤ x := div_nonneg (by linarith) hs.le
  have hc : (((n + 1 : ℕ) : ℝ) - 1) = ν + x * Real.sqrt ν - 1 := by
    rw [hx_def, div_mul_cancel₀ _ hs.ne']; ring
  have hE : 1 / erlangC (n + 1) ν = ∫ w in Ioi (0:ℝ), Fi ν x w := by
    rw [one_div, ← contE n ν hνpos, inv_inv, hc, scale ν _ hνpos]; rfl
  rw [hE, inv_delay]
  exact (hν0 ν (le_trans (le_max_left _ _) hν) x ⟨hx0, hxB⟩).le

end DimCC1e7h

end HWsec

namespace DimCC1e7
open DimCallCenters.Rationalized

/-- D4' (the one remaining child): integer Halfin–Whitt, difference form, uniform on
`0 < (N-ν)/√ν ≤ B`. Note `1/erlangC N ν = contErlangC N ν⁻¹ = ν ∫ e^{-νt} t (1+t)^{N-1}` (ab091a2a) and
`1/delayFn x = 1 + x/h(-x) = ∫_0^∞ w e^{xw - w²/2} dw`. -/
theorem HW_diff (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ) :
    ∃ ν0 : ℝ, ∀ ν : ℝ, ν0 ≤ ν → ∀ N : ℕ, ν < (N : ℝ) → ((N : ℝ) - ν) / Real.sqrt ν ≤ B →
      |1 / erlangC N ν - 1 / delayFn (((N : ℝ) - ν) / Real.sqrt ν)| ≤ δ :=
  DimCC1e7h.HW_diff B δ hB hδ

lemma xpos0 (ν : ℝ) (hν : 0 < ν) (N : ℝ) (h : ν < N) : 0 < (N - ν) / Real.sqrt ν :=
  div_pos (by linarith) (Real.sqrt_pos.2 hν)

theorem erlangC_halfinWhitt (B η : ℝ) (hB : 0 < B) (hη : 0 < η) :
    ∃ ν0 : ℝ, ∀ ν : ℝ, ν0 ≤ ν → ∀ N : ℕ, ν < (N : ℝ) → ((N : ℝ) - ν) / Real.sqrt ν ≤ B →
      (1 - η) * delayFn (((N : ℝ) - ν) / Real.sqrt ν) ≤ erlangC N ν ∧
      erlangC N ν ≤ (1 + η) * delayFn (((N : ℝ) - ν) / Real.sqrt ν) := by
  obtain ⟨ν0, h⟩ := HW_diff B (η / 2) hB (by positivity)
  refine ⟨max ν0 1, fun ν hν N hN hx => ?_⟩
  have hν0 : 0 < ν := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hν)
  have hx0 : 0 ≤ ((N : ℝ) - ν) / Real.sqrt ν := (xpos0 ν hν0 N hN).le
  have hd := h ν (le_trans (le_max_left _ _) hν) N hN hx
  obtain ⟨hp, hp1, -⟩ := erlang_pos_le N ν hν0 hN
  have hq := delayFn_props.2.1 _ hx0
  have hb1 : 1 ≤ 1 / delayFn (((N : ℝ) - ν) / Real.sqrt ν) := by
    unfold delayFn; rw [one_div_one_div]; linarith [g_nonneg hx0]
  set p := erlangC N ν with hpdef
  set q := delayFn (((N : ℝ) - ν) / Real.sqrt ν) with hqdef
  have ha1 : 1 ≤ 1 / p := by rw [le_div_iff₀ hp]; linarith
  rw [abs_le] at hd
  obtain ⟨hd1, hd2⟩ := hd
  constructor
  · have key : 0 ≤ 1 / q - (1 - η) * (1 / p) := by
      rcases le_or_gt η 1 with h1 | h1
      · nlinarith
      · nlinarith
    have e : p - (1 - η) * q = p * q * (1 / q - (1 - η) * (1 / p)) := by
      field_simp
    have : 0 ≤ p - (1 - η) * q := by rw [e]; exact mul_nonneg (mul_pos hp hq).le key
    linarith
  · have key : 0 ≤ (1 + η) * (1 / p) - 1 / q := by nlinarith
    have e : (1 + η) * q - p = p * q * ((1 + η) * (1 / p) - 1 / q) := by
      field_simp
    have : 0 ≤ (1 + η) * q - p := by rw [e]; exact mul_nonneg (mul_pos hp hq).le key
    linarith

/-- proved (73877692). -/
theorem glam_anti (M : WaitModel) (lam : ℝ) (hlam : 0 < lam) :
    StrictAntiOn (Glam M lam) (Set.Ioi 0) := (LC1_glam M lam hlam).2

/-- proved (b058416f waitCost_nonneg). -/
theorem waitCost_nonneg (M : WaitModel) (lam : ℝ) (hlam : 0 < lam) (N : ℝ)
    (hN : lam / M.μ < N) : 0 ≤ waitCost M N lam := by
  unfold waitCost
  have hμ := M.hμ
  have h1 : 0 ≤ N * M.μ - lam := by
    have := (div_lt_iff₀ hμ).1 hN; linarith
  apply mul_nonneg h1
  apply MeasureTheory.setIntegral_nonneg measurableSet_Ioi
  intro t ht
  have ht' : (0 : ℝ) < t := ht
  have hD : M.D lam 0 < M.D lam t :=
    M.hDmono lam hlam (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht'.le) ht'
  rw [M.hD0 lam hlam] at hD
  exact mul_nonneg hD.le (Real.exp_pos _).le

lemma servers_x (μ lam N : ℝ) (hν : 0 < lam / μ) :
    servers μ lam ((N - lam / μ) / Real.sqrt (lam / μ)) = N := by
  have hs : Real.sqrt (lam / μ) ≠ 0 := (Real.sqrt_pos.2 hν).ne'
  unfold servers
  rw [div_mul_cancel₀ _ hs]
  ring


lemma glam_nonneg (M : WaitModel) (lam : ℝ) (hlam : 0 < lam) (x : ℝ) (hx : 0 < x) :
    0 ≤ Glam M lam x := by
  have hν : 0 < lam / M.μ := div_pos hlam M.hμ
  unfold Glam
  apply mul_nonneg hlam.le
  apply waitCost_nonneg M lam hlam
  unfold servers
  have : 0 < x * Real.sqrt (lam / M.μ) := mul_pos hx (Real.sqrt_pos.2 hν)
  linarith

lemma xpos (ν : ℝ) (hν : 0 < ν) (N : ℝ) (h : ν < N) : 0 < (N - ν) / Real.sqrt ν :=
  div_pos (by linarith) (Real.sqrt_pos.2 hν)

end DimCC1e7

namespace DimCC2c3
open DimCallCenters.Rationalized DimCC1e7 MeasureTheory Set

lemma delay_le_one (x : ℝ) (hx : 0 ≤ x) : delayFn x ≤ 1 := by
  have := g_nonneg hx
  unfold delayFn
  rw [div_le_one (by linarith)]
  linarith

lemma inv_delay_ge (x : ℝ) (hx : 0 ≤ x) : 1 ≤ 1 / delayFn x := by
  have := g_nonneg hx
  unfold delayFn; rw [one_div_one_div]; linarith

noncomputable def Kc (B : ℝ) : ℝ := ∫ w in Ioi (0:ℝ), w ^ 2 * Real.exp (B * w - w ^ 2 / 2)

lemma int_w2 (B : ℝ) : IntegrableOn (fun w : ℝ => w ^ 2 * Real.exp (B * w - w ^ 2 / 2)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (2 : ℝ)) (p := 2) (b := 1/4)
      (by norm_num) (by norm_num) (by norm_num)
  refine Integrable.mono' (h.const_mul (Real.exp (B ^ 2)))
    (by fun_prop : Continuous fun w : ℝ => w ^ 2 * Real.exp (B * w - w ^ 2 / 2)).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun w hw => ?_)
  have hw' : (0:ℝ) < w := hw
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  simp only [Real.rpow_two]
  have := DimCC1e7h.exp_quad_le B w
  calc w ^ 2 * Real.exp (B * w - w ^ 2 / 2)
      ≤ w ^ 2 * (Real.exp (B ^ 2) * Real.exp (-(1/4) * w ^ 2)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = _ := by ring

lemma Kc_nonneg (B : ℝ) : 0 ≤ Kc B :=
  setIntegral_nonneg measurableSet_Ioi (fun w _ => by positivity)

lemma Gi_diff (B a b w : ℝ) (hab : a ≤ b) (hbB : b ≤ B) (hw : 0 < w) :
    DimCC1e7h.Gi b w - DimCC1e7h.Gi a w ≤ w ^ 2 * Real.exp (B * w - w ^ 2 / 2) * (b - a) := by
  unfold DimCC1e7h.Gi
  have e : Real.exp (a * w - w ^ 2 / 2) =
      Real.exp (b * w - w ^ 2 / 2) * Real.exp (-((b - a) * w)) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 := Real.add_one_le_exp (-((b - a) * w))
  have hbw : b * w ≤ B * w := mul_le_mul_of_nonneg_right hbB hw.le
  have h2 : Real.exp (b * w - w ^ 2 / 2) ≤ Real.exp (B * w - w ^ 2 / 2) :=
    Real.exp_le_exp.2 (by linarith)
  have hE := Real.exp_pos (b * w - w ^ 2 / 2)
  have hu : 0 ≤ (b - a) * w := mul_nonneg (by linarith) hw.le
  rw [e]
  have h3 := mul_le_mul_of_nonneg_left h1 (mul_pos hw hE).le
  have h4 : w * Real.exp (b * w - w ^ 2 / 2) * ((b - a) * w) ≤
      w * Real.exp (B * w - w ^ 2 / 2) * ((b - a) * w) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hw.le) hu
  nlinarith

lemma delay_lip (B a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hbB : b ≤ B) :
    delayFn a - delayFn b ≤ Kc B * (b - a) := by
  have hIa := DimCC1e7h.inv_delay a
  have hIb := DimCC1e7h.inv_delay b
  have hia : IntegrableOn (fun w => DimCC1e7h.Gi a w) (Ioi 0) := (DimCC1e7h.int_we a).integrableOn
  have hib : IntegrableOn (fun w => DimCC1e7h.Gi b w) (Ioi 0) := (DimCC1e7h.int_we b).integrableOn
  have hint : (∫ w in Ioi (0:ℝ), DimCC1e7h.Gi b w) - ∫ w in Ioi (0:ℝ), DimCC1e7h.Gi a w
      ≤ Kc B * (b - a) := by
    rw [← integral_sub hib hia, Kc, ← integral_mul_const]
    refine setIntegral_mono_on (hib.sub hia) ((int_w2 B).mul_const _) measurableSet_Ioi
      (fun w hw => ?_)
    exact Gi_diff B a b w hab hbB hw
  rw [← hIa, ← hIb] at hint
  have hb0 : 0 ≤ b := le_trans ha hab
  have hpa := delayFn_props.2.1 a ha
  have hpb := delayFn_props.2.1 b hb0
  have hmono : delayFn b ≤ delayFn a :=
    delayFn_props.1 (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hb0) hab
  have hla := delay_le_one a ha
  have hlb := delay_le_one b hb0
  have e : 1 / delayFn b - 1 / delayFn a = (delayFn a - delayFn b) / (delayFn a * delayFn b) := by
    field_simp
  have key : delayFn a - delayFn b ≤ (delayFn a - delayFn b) / (delayFn a * delayFn b) := by
    rw [le_div_iff₀ (mul_pos hpa hpb)]
    have : 0 ≤ (delayFn a - delayFn b) * (1 - delayFn a * delayFn b) :=
      mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  linarith

/-- Rounding up: a grid point `a` right of the surrogate minimizer `y` costs at most the cost at
any grid point `b ≥ a`, up to the variation of `P` over `[y, a]`. -/
lemma round_right (Fl G P : ℝ → ℝ) (K : ℝ)
    (hFl : ConvexOn ℝ (Ioi 0) Fl) (hG : ConvexOn ℝ (Ioi 0) G)
    (y a b : ℝ) (hy : 0 < y) (hya : y ≤ a) (hab : a ≤ b)
    (hGy : 0 ≤ G y) (hGb : 0 ≤ G b) (hPa0 : 0 ≤ P a) (hPay : P a ≤ P y)
    (hlip : P a - P b ≤ K * (b - a)) (hK : 0 ≤ K)
    (hopt : Fl y + P y * G y ≤ Fl b + P b * G b) :
    Fl a + P a * G a ≤ Fl b + P b * G b + K * (a - y) * G b := by
  rcases eq_or_lt_of_le (hya.trans hab) with hyb | hyb
  · have h1 : a = b := le_antisymm hab (by linarith)
    have h2 : a - y = 0 := by linarith
    rw [h2, h1]; simp
  · set t := (a - y) / (b - y) with ht
    have hby : 0 < b - y := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hby.le
    have ht1 : t ≤ 1 := (div_le_one hby).2 (by linarith)
    have hat : (1 - t) • y + t • b = a := by
      simp only [smul_eq_mul]; rw [ht]; field_simp; ring
    have hyI : y ∈ Ioi (0:ℝ) := hy
    have hbI : b ∈ Ioi (0:ℝ) := show (0:ℝ) < b by linarith
    have hF := hFl.2 hyI hbI (sub_nonneg.2 ht1) ht0 (by ring)
    have hGc := hG.2 hyI hbI (sub_nonneg.2 ht1) ht0 (by ring)
    rw [hat] at hF hGc
    simp only [smul_eq_mul] at hF hGc
    have htba : t * (b - a) ≤ a - y := by
      rw [ht, div_mul_eq_mul_div, div_le_iff₀ hby]; nlinarith
    have e1 : P a * G a ≤ (1 - t) * (P y * G y) + t * (P a * G b) := by
      have h1 := mul_le_mul_of_nonneg_left hGc hPa0
      have h2 : P a * G y ≤ P y * G y := mul_le_mul_of_nonneg_right hPay hGy
      have h3 := mul_le_mul_of_nonneg_left h2 (sub_nonneg.2 ht1)
      nlinarith
    have h3 : t * (P a - P b) ≤ K * (a - y) := by
      calc t * (P a - P b) ≤ t * (K * (b - a)) := mul_le_mul_of_nonneg_left hlip ht0
        _ = K * (t * (b - a)) := by ring
        _ ≤ K * (a - y) := mul_le_mul_of_nonneg_left htba hK
    have e2 := mul_le_mul_of_nonneg_right h3 hGb
    have e3 := mul_le_mul_of_nonneg_left hopt (sub_nonneg.2 ht1)
    nlinarith

/-- Rounding down: symmetric version. -/
lemma round_left (Fl G P : ℝ → ℝ) (K : ℝ)
    (hFl : ConvexOn ℝ (Ioi 0) Fl) (hG : ConvexOn ℝ (Ioi 0) G)
    (y a b : ℝ) (hb : 0 < b) (hba : b ≤ a) (hay : a ≤ y)
    (hGy : 0 ≤ G y) (hGb : 0 ≤ G b) (hPa0 : 0 ≤ P a) (hPab : P a ≤ P b)
    (hlip : P a - P y ≤ K * (y - a)) (hK : 0 ≤ K)
    (hopt : Fl y + P y * G y ≤ Fl b + P b * G b) :
    Fl a + P a * G a ≤ Fl b + P b * G b + K * (y - a) * G y := by
  rcases eq_or_lt_of_le (hba.trans hay) with hyb | hyb
  · have h1 : a = b := le_antisymm (by linarith) hba
    have h2 : y - a = 0 := by linarith
    rw [h2, h1]; simp
  · set t := (y - a) / (y - b) with ht
    have hby : 0 < y - b := by linarith
    have ht0 : 0 ≤ t := div_nonneg (by linarith) hby.le
    have ht1 : t ≤ 1 := (div_le_one hby).2 (by linarith)
    have hat : (1 - t) • y + t • b = a := by
      simp only [smul_eq_mul]; rw [ht]; field_simp; ring
    have hyI : y ∈ Ioi (0:ℝ) := show (0:ℝ) < y by linarith
    have hbI : b ∈ Ioi (0:ℝ) := hb
    have hF := hFl.2 hyI hbI (sub_nonneg.2 ht1) ht0 (by ring)
    have hGc := hG.2 hyI hbI (sub_nonneg.2 ht1) ht0 (by ring)
    rw [hat] at hF hGc
    simp only [smul_eq_mul] at hF hGc
    have e1 : P a * G a ≤ (1 - t) * (P a * G y) + t * (P b * G b) := by
      have h1 := mul_le_mul_of_nonneg_left hGc hPa0
      have h2 : P a * G b ≤ P b * G b := mul_le_mul_of_nonneg_right hPab hGb
      have h3 := mul_le_mul_of_nonneg_left h2 ht0
      nlinarith
    have h3 : (1 - t) * (P a - P y) ≤ K * (y - a) := by
      calc (1 - t) * (P a - P y) ≤ (1 - t) * (K * (y - a)) :=
            mul_le_mul_of_nonneg_left hlip (sub_nonneg.2 ht1)
        _ ≤ K * (y - a) := by
            have : 0 ≤ K * (y - a) := mul_nonneg hK (by linarith)
            nlinarith
    have e2 := mul_le_mul_of_nonneg_right h3 hGy
    have e3 := mul_le_mul_of_nonneg_left hopt (sub_nonneg.2 ht1)
    nlinarith

lemma flam_convex (F : ℝ → ℝ) (hFconv : ConvexOn ℝ (Ioi 0) F) (μ lam : ℝ) (hν : 0 < lam / μ) :
    ConvexOn ℝ (Ioi 0) (Flam F μ lam) := by
  refine ⟨convex_Ioi 0, fun x hx z hz a b ha hb hab => ?_⟩
  have hs := Real.sqrt_pos.2 hν
  have hx' : (0:ℝ) < x := hx
  have hz' : (0:ℝ) < z := hz
  have hxs : servers μ lam x ∈ Ioi (0:ℝ) := by
    show (0:ℝ) < _; unfold servers; have := mul_pos hx' hs; linarith
  have hzs : servers μ lam z ∈ Ioi (0:ℝ) := by
    show (0:ℝ) < _; unfold servers; have := mul_pos hz' hs; linarith
  have h := hFconv.2 hxs hzs ha hb hab
  have e : servers μ lam (a • x + b • z) = a • servers μ lam x + b • servers μ lam z := by
    simp only [smul_eq_mul]; unfold servers
    linear_combination (-(lam / μ)) * hab
  unfold Flam
  rw [e]
  simp only [smul_eq_mul] at h ⊢
  have : a * F (lam / μ) + b * F (lam / μ) = F (lam / μ) := by rw [← add_mul, hab, one_mul]
  linarith

lemma flam_nonneg (F : ℝ → ℝ) (hFmono : StrictMonoOn F (Ioi 0)) (μ lam : ℝ) (hν : 0 < lam / μ)
    (x : ℝ) (hx : 0 ≤ x) : 0 ≤ Flam F μ lam x := by
  unfold Flam servers
  have := mul_nonneg hx (Real.sqrt_nonneg (lam / μ))
  have h := hFmono.monotoneOn (show lam / μ ∈ Ioi (0:ℝ) from hν)
    (show lam / μ + x * Real.sqrt (lam / μ) ∈ Ioi (0:ℝ) from by show (0:ℝ) < _; linarith)
    (by linarith)
  linarith

lemma flam_pos (F : ℝ → ℝ) (hFmono : StrictMonoOn F (Ioi 0)) (μ lam : ℝ) (hν : 0 < lam / μ)
    (x : ℝ) (hx : 0 < x) : 0 < Flam F μ lam x := by
  unfold Flam servers
  have := mul_pos hx (Real.sqrt_pos.2 hν)
  have h := hFmono (show lam / μ ∈ Ioi (0:ℝ) from hν)
    (show lam / μ + x * Real.sqrt (lam / μ) ∈ Ioi (0:ℝ) from by show (0:ℝ) < _; linarith)
    (by linarith)
  linarith

lemma flam_mono (F : ℝ → ℝ) (hFmono : StrictMonoOn F (Ioi 0)) (μ lam : ℝ) (hν : 0 < lam / μ)
    (x z : ℝ) (hx : 0 ≤ x) (hxz : x ≤ z) : Flam F μ lam x ≤ Flam F μ lam z := by
  unfold Flam servers
  have hs := Real.sqrt_nonneg (lam / μ)
  have h1 := mul_nonneg hx hs
  have h2 := mul_le_mul_of_nonneg_right hxz hs
  have h := hFmono.monotoneOn
    (show lam / μ + x * Real.sqrt (lam / μ) ∈ Ioi (0:ℝ) from by show (0:ℝ) < _; linarith)
    (show lam / μ + z * Real.sqrt (lam / μ) ∈ Ioi (0:ℝ) from by show (0:ℝ) < _; linarith)
    (by linarith)
  linarith

/-- Linear growth: `x · F_λ(a) ≤ a · F_λ(x)` for `0 < a ≤ x` (convexity, `F_λ(0) = 0`). -/
lemma flam_linear (F : ℝ → ℝ) (hFconv : ConvexOn ℝ (Ioi 0) F) (μ lam : ℝ) (hν : 0 < lam / μ)
    (a x : ℝ) (ha : 0 < a) (hax : a ≤ x) : x * Flam F μ lam a ≤ a * Flam F μ lam x := by
  have hx : 0 < x := lt_of_lt_of_le ha hax
  have hs := Real.sqrt_pos.2 hν
  have hxs : servers μ lam x ∈ Ioi (0:ℝ) := by
    show (0:ℝ) < _; unfold servers; have := mul_pos hx hs; linarith
  have hνI : lam / μ ∈ Ioi (0:ℝ) := hν
  have hw0 : 0 ≤ 1 - a / x := by rw [sub_nonneg, div_le_one hx]; exact hax
  have hw1 : 0 ≤ a / x := (div_pos ha hx).le
  have h := hFconv.2 hνI hxs hw0 hw1 (by ring)
  have e : (1 - a / x) • (lam / μ) + (a / x) • servers μ lam x = servers μ lam a := by
    simp only [smul_eq_mul]; unfold servers; field_simp; ring
  rw [e] at h
  simp only [smul_eq_mul] at h
  unfold Flam
  have h2 := mul_le_mul_of_nonneg_left h hx.le
  have e2 : x * ((1 - a / x) * F (lam / μ) + a / x * F (servers μ lam x)) =
      (x - a) * F (lam / μ) + a * F (servers μ lam x) := by field_simp
  rw [e2] at h2
  nlinarith

lemma cost_eq (M : WaitModel) (F : ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam) (N : ℕ) :
    cost M F N lam - F (lam / M.μ) =
      Flam F M.μ lam (((N:ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ)) +
      erlangC N (lam / M.μ) * Glam M lam (((N:ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ)) := by
  have hν : 0 < lam / M.μ := div_pos hlam M.hμ
  unfold cost Flam Glam
  rw [servers_x M.μ lam (N:ℝ) hν]
  ring

end DimCC2c3

namespace DimCC2c3
open DimCallCenters.Rationalized DimCC1e7 MeasureTheory Set

/-- Core per-`λ` estimate, abstracted from the definitions. -/
lemma core (ν s : ℝ) (hν : 0 < ν) (hs0 : 0 < s)
    (Fl G : ℝ → ℝ) (c π : ℕ → ℝ)
    (hFlc : ConvexOn ℝ (Ioi 0) Fl) (hGc : ConvexOn ℝ (Ioi 0) G)
    (hFl0 : ∀ x, 0 < x → 0 < Fl x) (hG0 : ∀ x, 0 < x → 0 ≤ G x)
    (hc : ∀ N : ℕ, c N = Fl (((N:ℝ) - ν) / s) + π N * G (((N:ℝ) - ν) / s))
    (B η : ℝ) (hB : 0 < B) (hη0 : 0 < η) (hη1 : η < 1)
    (hHW : ∀ N : ℕ, ν < N → ((N:ℝ) - ν) / s ≤ B →
        (1 - η) * delayFn (((N:ℝ) - ν) / s) ≤ π N ∧ π N ≤ (1 + η) * delayFn (((N:ℝ) - ν) / s))
    (hs : Kc B ≤ η * delayFn B * s)
    (yl : ℝ) (hyl : 0 < yl) (hyB : yl ≤ B)
    (hyopt : ∀ y', 0 < y' → Fl yl + delayFn yl * G yl ≤ Fl y' + delayFn y' * G y')
    (Ns : ℕ) (hNs : ν < Ns) (hxB : ((Ns:ℝ) - ν) / s ≤ B)
    (hNsopt : ∀ N : ℕ, ν < N → c Ns ≤ c N)
    (m S : ℝ) (hm : m = ν + yl * s)
    (hS : S = if (⌊m⌋₊ : ℝ) ≤ ν then c ⌈m⌉₊ else min (c ⌊m⌋₊) (c ⌈m⌉₊)) :
    0 < c Ns ∧ c Ns ≤ S ∧ (1 - η) * S ≤ (1 + η) ^ 2 * c Ns := by
  have hP0 : ∀ x, 0 ≤ x → 0 < delayFn x := delayFn_props.2.1
  have hPanti : ∀ x z, 0 ≤ x → x ≤ z → delayFn z ≤ delayFn x := fun x z hx hxz =>
    delayFn_props.1 (Set.mem_Ici.2 hx) (Set.mem_Ici.2 (le_trans hx hxz)) hxz
  have hp0 : 0 < delayFn B := hP0 B hB.le
  have hK := Kc_nonneg B
  have hb0 : 0 < ((Ns:ℝ) - ν) / s := div_pos (by linarith) hs0
  set b := ((Ns:ℝ) - ν) / s with hbdef
  have hcNs := hc Ns
  have hHWs := hHW Ns hNs hxB
  have hFlb := hFl0 b hb0
  have hGb := hG0 b hb0
  have hπs : 0 ≤ π Ns := le_trans (mul_nonneg (by linarith) (hP0 b hb0.le).le) hHWs.1
  have hcpos : 0 < c Ns := by
    rw [hcNs]; have := mul_nonneg hπs hGb; linarith
  have hlow : (1 - η) * (Fl b + delayFn b * G b) ≤ c Ns := by
    rw [hcNs]
    have h1 := mul_le_mul_of_nonneg_right hHWs.1 hGb
    have h2 := mul_nonneg hη0.le hFlb.le
    linarith
  have hopt := hyopt b hb0
  have hm0 : ν < m := by rw [hm]; have := mul_pos hyl hs0; linarith
  have hceil : ν < (⌈m⌉₊ : ℝ) := lt_of_lt_of_le hm0 (Nat.le_ceil m)
  have hm0' : 0 ≤ m := by linarith
  -- lower bound
  have hlowS : c Ns ≤ S := by
    rw [hS]
    split_ifs with h
    · exact hNsopt _ hceil
    · exact le_min (hNsopt _ (not_le.1 h)) (hNsopt _ hceil)
  -- upper bound: some stable neighbour N with S ≤ c N ≤ (1+η)^2 Ĉ(b)
  have hup : ∃ N : ℕ, S ≤ c N ∧ c N ≤ (1 + η) ^ 2 * (Fl b + delayFn b * G b) := by
    rcases le_or_gt m (Ns : ℝ) with h | h
    · -- round up
      have hN2 : ⌈m⌉₊ ≤ Ns := Nat.ceil_le.2 h
      have hN2r : (⌈m⌉₊ : ℝ) ≤ Ns := by exact_mod_cast hN2
      set a := ((⌈m⌉₊ : ℝ) - ν) / s with hadef
      have has : a * s = (⌈m⌉₊ : ℝ) - ν := by rw [hadef]; field_simp
      have hya : yl ≤ a := by
        rw [hadef, le_div_iff₀ hs0]; have := Nat.le_ceil m; linarith
      have hab : a ≤ b := div_le_div_of_nonneg_right (by linarith) hs0.le
      have hd : (a - yl) * s ≤ 1 := by
        have := Nat.ceil_lt_add_one hm0'
        have e : (a - yl) * s = a * s - yl * s := by ring
        rw [e, has]; linarith
      have ha0 : 0 < a := lt_of_lt_of_le hyl hya
      have hlip := delay_lip B a b ha0.le hab hxB
      have hR := round_right Fl G delayFn (Kc B) hFlc hGc yl a b hyl hya hab (hG0 yl hyl) hGb
        (hP0 a ha0.le).le (hPanti yl a hyl.le hya) hlip hK hopt
      have hKd : Kc B * (a - yl) ≤ η * delayFn B := by
        have h1 := mul_le_mul_of_nonneg_right hs (show 0 ≤ a - yl by linarith)
        have h2 : η * delayFn B * s * (a - yl) ≤ η * delayFn B :=
          calc η * delayFn B * s * (a - yl) = η * delayFn B * ((a - yl) * s) := by ring
            _ ≤ η * delayFn B * 1 := mul_le_mul_of_nonneg_left hd (by positivity)
            _ = η * delayFn B := by ring
        linarith
      have hpb : delayFn B ≤ delayFn b := hPanti b B hb0.le hxB
      have hextra : Kc B * (a - yl) * G b ≤ η * (Fl b + delayFn b * G b) := by
        have h1 := mul_le_mul_of_nonneg_right hKd hGb
        have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpb hGb) hη0.le
        have h4 := mul_nonneg hη0.le hFlb.le
        linarith
      have hCa : Fl a + delayFn a * G a ≤ (1 + η) * (Fl b + delayFn b * G b) := by linarith
      have hHWa := hHW ⌈m⌉₊ hceil (le_trans hab hxB)
      have hca : c ⌈m⌉₊ ≤ (1 + η) * (Fl a + delayFn a * G a) := by
        rw [hc]
        have h1 := mul_le_mul_of_nonneg_right hHWa.2 (hG0 a ha0)
        have h2 := hFl0 a ha0
        have h3 := mul_nonneg hη0.le h2.le
        linarith
      refine ⟨⌈m⌉₊, ?_, ?_⟩
      · rw [hS]; split_ifs
        · exact le_rfl
        · exact min_le_right _ _
      · calc c ⌈m⌉₊ ≤ (1 + η) * (Fl a + delayFn a * G a) := hca
          _ ≤ (1 + η) * ((1 + η) * (Fl b + delayFn b * G b)) :=
            mul_le_mul_of_nonneg_left hCa (by linarith)
          _ = (1 + η) ^ 2 * (Fl b + delayFn b * G b) := by ring
    · -- round down
      have hN1 : Ns ≤ ⌊m⌋₊ := Nat.le_floor h.le
      have hN1r : (Ns : ℝ) ≤ ⌊m⌋₊ := by exact_mod_cast hN1
      have hfl : ν < (⌊m⌋₊ : ℝ) := lt_of_lt_of_le hNs hN1r
      set a := ((⌊m⌋₊ : ℝ) - ν) / s with hadef
      have has : a * s = (⌊m⌋₊ : ℝ) - ν := by rw [hadef]; field_simp
      have hay : a ≤ yl := by
        rw [hadef, div_le_iff₀ hs0]; have := Nat.floor_le hm0'; linarith
      have hba : b ≤ a := div_le_div_of_nonneg_right (by linarith) hs0.le
      have hd : (yl - a) * s ≤ 1 := by
        have := Nat.lt_floor_add_one m
        have e : (yl - a) * s = yl * s - a * s := by ring
        rw [e, has]; linarith
      have ha0 : 0 < a := lt_of_lt_of_le hb0 hba
      have hlip := delay_lip B a yl ha0.le hay hyB
      have hL := round_left Fl G delayFn (Kc B) hFlc hGc yl a b hb0 hba hay (hG0 yl hyl) hGb
        (hP0 a ha0.le).le (hPanti b a hb0.le hba) hlip hK hopt
      have hKd : Kc B * (yl - a) ≤ η * delayFn B := by
        have h1 := mul_le_mul_of_nonneg_right hs (show 0 ≤ yl - a by linarith)
        have h2 : η * delayFn B * s * (yl - a) ≤ η * delayFn B :=
          calc η * delayFn B * s * (yl - a) = η * delayFn B * ((yl - a) * s) := by ring
            _ ≤ η * delayFn B * 1 := mul_le_mul_of_nonneg_left hd (by positivity)
            _ = η * delayFn B := by ring
        linarith
      have hpy : delayFn B ≤ delayFn yl := hPanti yl B hyl.le hyB
      have hGy := hG0 yl hyl
      have hFly := hFl0 yl hyl
      have hextra : Kc B * (yl - a) * G yl ≤ η * (Fl b + delayFn b * G b) := by
        have h1 := mul_le_mul_of_nonneg_right hKd hGy
        have h2 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpy hGy) hη0.le
        have h3 := mul_le_mul_of_nonneg_left hopt hη0.le
        have h4 := mul_nonneg hη0.le hFly.le
        linarith
      have hCa : Fl a + delayFn a * G a ≤ (1 + η) * (Fl b + delayFn b * G b) := by linarith
      have hHWa := hHW ⌊m⌋₊ hfl (le_trans hay hyB)
      have hca : c ⌊m⌋₊ ≤ (1 + η) * (Fl a + delayFn a * G a) := by
        rw [hc]
        have h1 := mul_le_mul_of_nonneg_right hHWa.2 (hG0 a ha0)
        have h2 := hFl0 a ha0
        have h3 := mul_nonneg hη0.le h2.le
        linarith
      refine ⟨⌊m⌋₊, ?_, ?_⟩
      · rw [hS]; split_ifs with h'
        · exact absurd h' (not_le.2 hfl)
        · exact min_le_left _ _
      · calc c ⌊m⌋₊ ≤ (1 + η) * (Fl a + delayFn a * G a) := hca
          _ ≤ (1 + η) * ((1 + η) * (Fl b + delayFn b * G b)) :=
            mul_le_mul_of_nonneg_left hCa (by linarith)
          _ = (1 + η) ^ 2 * (Fl b + delayFn b * G b) := by ring
  obtain ⟨N, hSN, hNb⟩ := hup
  refine ⟨hcpos, hlowS, ?_⟩
  have h1 : (1 - η) * S ≤ (1 - η) * ((1 + η) ^ 2 * (Fl b + delayFn b * G b)) :=
    mul_le_mul_of_nonneg_left (le_trans hSN hNb) (by linarith)
  have h2 : (1 + η) ^ 2 * ((1 - η) * (Fl b + delayFn b * G b)) ≤ (1 + η) ^ 2 * c Ns :=
    mul_le_mul_of_nonneg_left hlow (by positivity)
  linarith

/-- Boundedness of the surrogate minimizer and of the optimal integer staffing (regime (18)). -/
lemma bound_core (ν s : ℝ) (hν : 0 < ν) (hs0 : 0 < s) (Fl G : ℝ → ℝ) (c π : ℕ → ℝ)
    (hFl0 : ∀ x, 0 < x → 0 < Fl x) (hFlm : ∀ x z, 0 ≤ x → x ≤ z → Fl x ≤ Fl z)
    (hFlin : ∀ a x, 0 < a → a ≤ x → x * Fl a ≤ a * Fl x)
    (hG0 : ∀ x, 0 < x → 0 ≤ G x) (hGa : ∀ x z, 0 < x → x ≤ z → G z ≤ G x)
    (hc : ∀ N : ℕ, c N = Fl (((N:ℝ) - ν) / s) + π N * G (((N:ℝ) - ν) / s))
    (hπ0 : ∀ N : ℕ, ν < N → 0 ≤ π N) (hπ1 : ∀ N : ℕ, ν < N → π N ≤ 1)
    (κ γ : ℝ) (hκ : 0 < κ) (hγ : 0 < γ) (hrat : γ / 2 < Fl κ / G κ) (hsκ : 1 ≤ κ * s)
    (yl : ℝ) (hyl : 0 < yl)
    (hyopt : ∀ y', 0 < y' → Fl yl + delayFn yl * G yl ≤ Fl y' + delayFn y' * G y')
    (Ns : ℕ) (hNs : ν < Ns) (hNsopt : ∀ N : ℕ, ν < N → c Ns ≤ c N) :
    yl ≤ 2 * κ * (1 + 2 / γ) ∧ ((Ns:ℝ) - ν) / s ≤ 2 * κ * (1 + 2 / γ) := by
  have hP0 : ∀ x, 0 ≤ x → 0 < delayFn x := delayFn_props.2.1
  have hFk := hFl0 κ hκ
  have hGk0 := hG0 κ hκ
  have hGk : 0 < G κ := by
    rcases eq_or_lt_of_le hGk0 with h | h
    · rw [← h, div_zero] at hrat; linarith
    · exact h
  have hGγ : G κ * γ < 2 * Fl κ := by
    rw [lt_div_iff₀ hGk] at hrat; linarith
  have hBe : 2 * κ * (1 + 2 / γ) = 2 * κ * (γ + 2) / γ := by field_simp
  rw [hBe]
  constructor
  · rw [le_div_iff₀ hγ]
    have h1 := hyopt κ hκ
    have hPk1 : delayFn κ ≤ 1 := delay_le_one κ hκ.le
    have h2 : delayFn κ * G κ ≤ G κ := by nlinarith
    have h3 : 0 ≤ delayFn yl * G yl := mul_nonneg (hP0 yl hyl.le).le (hG0 yl hyl)
    have hFy : Fl yl ≤ Fl κ + G κ := by linarith
    rcases le_or_gt yl κ with hk | hk
    · nlinarith
    · have h4 := hFlin κ yl hκ hk.le
      -- yl * Fl κ ≤ κ * (Fl κ + G κ)
      have h5 : yl * Fl κ ≤ κ * (Fl κ + G κ) := le_trans h4 (mul_le_mul_of_nonneg_left hFy hκ.le)
      have h6 : yl * Fl κ * γ ≤ κ * (Fl κ + G κ) * γ := mul_le_mul_of_nonneg_right h5 hγ.le
      have h7 : yl * γ * Fl κ ≤ κ * (γ + 2) * Fl κ := by nlinarith
      have h8 := le_of_mul_le_mul_right h7 hFk
      nlinarith
  · set b := ((Ns:ℝ) - ν) / s with hbdef
    have hb0 : 0 < b := div_pos (by linarith) hs0
    rw [le_div_iff₀ hγ]
    -- comparison staffing Nκ = ⌈ν + κ s⌉
    set Nk := ⌈ν + κ * s⌉₊ with hNk
    have hks : 0 < κ * s := mul_pos hκ hs0
    have hNk1 : ν + κ * s ≤ (Nk : ℝ) := Nat.le_ceil _
    have hNk2 : (Nk : ℝ) < ν + κ * s + 1 := Nat.ceil_lt_add_one (by linarith)
    have hNkν : ν < (Nk : ℝ) := by linarith
    set xk := ((Nk:ℝ) - ν) / s with hxk
    have hxk1 : κ ≤ xk := by rw [hxk, le_div_iff₀ hs0]; linarith
    have hxk2 : xk ≤ 2 * κ := by rw [hxk, div_le_iff₀ hs0]; linarith
    have hxk0 : 0 < xk := lt_of_lt_of_le hκ hxk1
    have hcNk : c Nk ≤ Fl (2 * κ) + G κ := by
      rw [hc]
      have h1 := hFlm xk (2 * κ) hxk0.le hxk2
      have h2 := hGa κ xk hκ hxk1
      have h3 := hG0 xk hxk0
      have h4 := hπ1 Nk hNkν
      have h5 := hπ0 Nk hNkν
      have h6 : π Nk * G xk ≤ G xk := by nlinarith
      linarith
    have hcb : Fl b ≤ c Ns := by
      rw [hc]; have := mul_nonneg (hπ0 Ns hNs) (hG0 b hb0); linarith
    have hFb : Fl b ≤ Fl (2 * κ) + G κ := le_trans hcb (le_trans (hNsopt Nk hNkν) hcNk)
    have hF2 : Fl κ ≤ Fl (2 * κ) := hFlm κ (2 * κ) hκ.le (by linarith)
    have hF2p : 0 < Fl (2 * κ) := by linarith
    rcases le_or_gt b (2 * κ) with hk | hk
    · nlinarith
    · have h4 := hFlin (2 * κ) b (by linarith) hk.le
      have h5 : b * Fl (2 * κ) ≤ 2 * κ * (Fl (2 * κ) + G κ) :=
        le_trans h4 (mul_le_mul_of_nonneg_left hFb (by linarith))
      have h6 : b * Fl (2 * κ) * γ ≤ 2 * κ * (Fl (2 * κ) + G κ) * γ :=
        mul_le_mul_of_nonneg_right h5 hγ.le
      have h7 : b * γ * Fl (2 * κ) ≤ 2 * κ * (γ + 2) * Fl (2 * κ) := by nlinarith
      exact le_of_mul_le_mul_right h7 hF2p

end DimCC2c3

open DimCC1e7 DimCC2c3 in
open DimCallCenters.Rationalized Filter Topology in
theorem solution (M : WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hGinf : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun N => waitCost M N lam) (𝓝[>] (lam / M.μ)) atTop)
    (hreg : ∃ κ : ℝ, 0 < κ ∧ ∃ γ : ℝ, 0 < γ ∧
      Tendsto (fun lam => Flam F M.μ lam κ / Glam M lam κ) atTop (𝓝 γ))
    (y : ℝ → ℝ)
    (hy : ∀ lam : ℝ, 0 < lam → 0 < y lam ∧
      ∀ y' : ℝ, 0 < y' →
        surrogate (Flam F M.μ lam) delayFn (Glam M lam) (y lam) ≤
          surrogate (Flam F M.μ lam) delayFn (Glam M lam) y')
    (Nstar : ℝ → ℕ)
    (hN : ∀ lam : ℝ, 0 < lam → lam / M.μ < Nstar lam ∧
      ∀ N : ℕ, lam / M.μ < N → cost M F (Nstar lam) lam ≤ cost M F N lam) :
    Tendsto (fun lam => (staffCost M F lam (y lam) - F (lam / M.μ)) /
      (cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (𝓝 1) := by
  obtain ⟨κ, hκ, γ, hγ, hlim⟩ := hreg
  have hμ := M.hμ
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hB : 0 < 2 * κ * (1 + 2 / γ) := by positivity
  set B := 2 * κ * (1 + 2 / γ) with hBdef
  set η := min (ε / 8) (1 / 2) with hηdef
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η ≤ 1 / 2 := min_le_right _ _
  have hηε : η ≤ ε / 8 := min_le_left _ _
  obtain ⟨ν0, hHW⟩ := erlangC_halfinWhitt B η hB hη0
  have hp0 : 0 < delayFn B := delayFn_props.2.1 B hB.le
  have hK := Kc_nonneg B
  have hdiv : Tendsto (fun lam : ℝ => lam / M.μ) atTop atTop := tendsto_id.atTop_div_const hμ
  have hev1 : ∀ᶠ lam in atTop, max ν0 (max ((Kc B / (η * delayFn B)) ^ 2) ((1 / κ) ^ 2)) ≤ lam / M.μ :=
    hdiv.eventually_ge_atTop _
  have hev2 : ∀ᶠ lam in atTop, γ / 2 < Flam F M.μ lam κ / Glam M lam κ :=
    hlim.eventually (lt_mem_nhds (by linarith))
  obtain ⟨L, hL⟩ := eventually_atTop.1 (hev1.and (hev2.and (eventually_gt_atTop 0)))
  refine ⟨L, fun lam hlam => ?_⟩
  obtain ⟨hT, hrat, hlam0⟩ := hL lam hlam
  have hν : 0 < lam / M.μ := div_pos hlam0 hμ
  have hs0 : 0 < Real.sqrt (lam / M.μ) := Real.sqrt_pos.2 hν
  have hT1 : ν0 ≤ lam / M.μ := le_trans (le_max_left _ _) hT
  have hT2 : (Kc B / (η * delayFn B)) ^ 2 ≤ lam / M.μ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT3 : (1 / κ) ^ 2 ≤ lam / M.μ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hsK : Kc B / (η * delayFn B) ≤ Real.sqrt (lam / M.μ) := by
    have := Real.sqrt_le_sqrt hT2
    rwa [Real.sqrt_sq (div_nonneg hK (by positivity))] at this
  have hs : Kc B ≤ η * delayFn B * Real.sqrt (lam / M.μ) := by
    rw [div_le_iff₀ (by positivity)] at hsK; linarith
  have hsκ : 1 ≤ κ * Real.sqrt (lam / M.μ) := by
    have := Real.sqrt_le_sqrt hT3
    rw [Real.sqrt_sq (by positivity), div_le_iff₀ hκ] at this
    linarith
  obtain ⟨hy0, hyopt⟩ := hy lam hlam0
  obtain ⟨hNs, hNsopt⟩ := hN lam hlam0
  have hc : ∀ N : ℕ, (fun N : ℕ => cost M F N lam - F (lam / M.μ)) N =
      Flam F M.μ lam (((N:ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ)) +
      (fun N : ℕ => erlangC N (lam / M.μ)) N *
        Glam M lam (((N:ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ)) :=
    fun N => cost_eq M F lam hlam0 N
  have hFl0 : ∀ x, 0 < x → 0 < Flam F M.μ lam x := fun x hx => flam_pos F hFmono M.μ lam hν x hx
  have hG0 : ∀ x, 0 < x → 0 ≤ Glam M lam x := fun x hx => glam_nonneg M lam hlam0 x hx
  have hNsopt' : ∀ N : ℕ, lam / M.μ < N →
      (fun N : ℕ => cost M F N lam - F (lam / M.μ)) (Nstar lam) ≤
        (fun N : ℕ => cost M F N lam - F (lam / M.μ)) N := by
    intro N hN'; have := hNsopt N hN'; simp only; linarith
  obtain ⟨hyB, hxB⟩ := bound_core (lam / M.μ) (Real.sqrt (lam / M.μ)) hν hs0 (Flam F M.μ lam)
    (Glam M lam) (fun N : ℕ => cost M F N lam - F (lam / M.μ)) (fun N : ℕ => erlangC N (lam / M.μ))
    hFl0 (fun x z hx hxz => flam_mono F hFmono M.μ lam hν x z hx hxz)
    (fun a x ha hax => flam_linear F hFconv M.μ lam hν a x ha hax) hG0
    (fun x z hx hxz => (glam_anti M lam hlam0).antitoneOn hx (lt_of_lt_of_le hx hxz) hxz)
    hc (fun N hN' => (erlang_pos_le N _ hν hN').1.le) (fun N hN' => (erlang_pos_le N _ hν hN').2.1)
    κ γ hκ hγ hrat hsκ (y lam) hy0 hyopt (Nstar lam) hNs hNsopt'
  have hS : staffCost M F lam (y lam) - F (lam / M.μ) =
      if (⌊lam / M.μ + y lam * Real.sqrt (lam / M.μ)⌋₊ : ℝ) ≤ lam / M.μ then
        (fun N : ℕ => cost M F N lam - F (lam / M.μ)) ⌈lam / M.μ + y lam * Real.sqrt (lam / M.μ)⌉₊
      else min ((fun N : ℕ => cost M F N lam - F (lam / M.μ)) ⌊lam / M.μ + y lam * Real.sqrt (lam / M.μ)⌋₊)
        ((fun N : ℕ => cost M F N lam - F (lam / M.μ)) ⌈lam / M.μ + y lam * Real.sqrt (lam / M.μ)⌉₊) := by
    unfold staffCost servers
    split_ifs
    · rfl
    · exact (min_sub_sub_right _ _ _).symm
  obtain ⟨hcpos, hlow, hupp⟩ := core (lam / M.μ) (Real.sqrt (lam / M.μ)) hν hs0 (Flam F M.μ lam)
    (Glam M lam) (fun N : ℕ => cost M F N lam - F (lam / M.μ)) (fun N : ℕ => erlangC N (lam / M.μ))
    (flam_convex F hFconv M.μ lam hν) (LC1_glam M lam hlam0).1.convexOn hFl0 hG0 hc B η hB hη0
    (by linarith) (hHW (lam / M.μ) hT1) hs (y lam) hy0 hyB hyopt (Nstar lam) hNs hxB hNsopt'
    _ _ rfl hS
  rw [Real.dist_eq, abs_lt]
  set S := staffCost M F lam (y lam) - F (lam / M.μ)
  set C := cost M F (Nstar lam) lam - F (lam / M.μ)
  have hr1 : 1 ≤ S / C := by rw [le_div_iff₀ hcpos]; linarith
  have hkey : (1 + η) ^ 2 < (1 + ε) * (1 - η) := by nlinarith
  have hr2 : S / C < 1 + ε := by
    rw [div_lt_iff₀ hcpos]
    have h1 : (1 - η) * S < (1 - η) * ((1 + ε) * C) := by nlinarith
    exact lt_of_mul_lt_mul_left h1 (by linarith)
  constructor <;> linarith
