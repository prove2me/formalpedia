-- Prove2me | solution 1 for DimCallCenters.QualityDriven.theorem_7_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T06:55:12.446051+00:00
-- url     : https://prove2.me/submissions/2866d9e1-5f8e-449a-a22b-2cd83a6b9fb3

import Mathlib
import Definitions.Def_DimCallCenters_Rationalized_Flam
import Definitions.Def_DimCallCenters_Rationalized_Glam
import Definitions.Def_DimCallCenters_Rationalized_surrogate
import Definitions.Def_DimCallCenters_QualityDriven_Qlam
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

namespace B058Aux

open DimCallCenters.Rationalized Filter Set

lemma fact_le (N : ℕ) (hN : 1 ≤ N) :
    (N.factorial : ℝ) ≤ Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N := by
  have h := Stirling.stirlingSeq'_antitone (Nat.zero_le (N - 1))
  simp only [Function.comp, Nat.succ_eq_add_one, zero_add, Stirling.stirlingSeq_one] at h
  have hN1 : N - 1 + 1 = N := Nat.sub_add_cancel hN
  rw [hN1, Stirling.stirlingSeq] at h
  have hpos : 0 < Real.sqrt (2 * (N : ℝ)) * ((N : ℝ) / Real.exp 1) ^ N := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  rw [div_le_iff₀ hpos] at h
  have h2 : Real.sqrt (2 * (N : ℝ)) = Real.sqrt 2 * Real.sqrt N := by
    rw [Real.sqrt_mul (by norm_num)]
  rw [h2] at h
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  calc (N.factorial : ℝ) ≤ Real.exp 1 / Real.sqrt 2 * (Real.sqrt 2 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N) := h
    _ = Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N := by field_simp

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

lemma erlang_bound (N : ℕ) (ν : ℝ) (hν : 0 < ν) (hN : ν < N) :
    1 / erlangC N ν - 1 ≤
      Real.exp 1 * ((N - ν) / Real.sqrt ν) * Real.exp (((N - ν) / Real.sqrt ν) ^ 2) := by
  obtain ⟨-, -, heq⟩ := erlang_pos_le N ν hν hN
  rw [heq]
  have hNpos : (0 : ℝ) < N := lt_trans hν hN
  have hN1 : 1 ≤ N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp at hNpos
    · exact h
  have hfact := fact_le N hN1
  have hb : ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ) ≤ Real.exp ν :=
    Real.sum_le_exp_of_nonneg hν.le N
  have hb0 : 0 ≤ ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ) :=
    Finset.sum_nonneg (fun n _ => by positivity)
  set d := (N : ℝ) - ν with hd
  have hdpos : 0 < d := by rw [hd]; linarith
  have hsν : 0 < Real.sqrt ν := Real.sqrt_pos.2 hν
  have hsN : Real.sqrt ν ≤ Real.sqrt N := Real.sqrt_le_sqrt hN.le
  have hsNpos : 0 < Real.sqrt N := lt_of_lt_of_le hsν hsN
  -- N^N ≤ ν^N * exp (d * N / ν)
  have hpow : (N : ℝ) ^ N ≤ ν ^ N * Real.exp (d * N / ν) := by
    have h1 : (N : ℝ) = ν * (d / ν + 1) := by rw [hd]; field_simp; ring
    have h2 : (d / ν + 1) ^ N ≤ Real.exp (d / ν) ^ N :=
      pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp _) N
    rw [← Real.exp_nat_mul] at h2
    calc (N : ℝ) ^ N = ν ^ N * (d / ν + 1) ^ N := by rw [← mul_pow, ← h1]
      _ ≤ ν ^ N * Real.exp (N * (d / ν)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ν ^ N * Real.exp (d * N / ν) := by ring_nf
  have hexp : Real.exp (d * N / ν) * Real.exp ν * (Real.exp 1)⁻¹ ^ N =
      Real.exp ((d / Real.sqrt ν) ^ 2) := by
    rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [div_pow, Real.sq_sqrt hν.le, hd]
    field_simp
    ring
  -- main estimate
  have ha : 0 < ν ^ N / (N.factorial : ℝ) := by positivity
  rw [div_le_iff₀ ha]
  have hq : 1 - ν / N = d / N := by rw [hd]; field_simp
  rw [hq]
  have key1 : d / N * (∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ)) ≤ d / N * Real.exp ν :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  have hfpos : (0 : ℝ) < N.factorial := by positivity
  -- reduce to: d/N * exp ν * N! ≤ RHS * ν^N
  have goal2 : d / N * Real.exp ν * (N.factorial : ℝ) ≤
      Real.exp 1 * (d / Real.sqrt ν) * Real.exp ((d / Real.sqrt ν) ^ 2) * ν ^ N := by
    have step1 : d / N * Real.exp ν * (N.factorial : ℝ) ≤
        d / N * Real.exp ν * (Real.exp 1 * Real.sqrt N * ((N : ℝ) / Real.exp 1) ^ N) :=
      mul_le_mul_of_nonneg_left hfact (by positivity)
    refine le_trans step1 ?_
    have e1 : ((N : ℝ) / Real.exp 1) ^ N = (N : ℝ) ^ N * (Real.exp 1)⁻¹ ^ N := by
      rw [div_eq_mul_inv, mul_pow]
    rw [e1]
    have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
    have hdN : d / N * Real.sqrt N ≤ d / Real.sqrt ν := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hNpos hsν]
      have : Real.sqrt N * Real.sqrt ν ≤ Real.sqrt N * Real.sqrt N :=
        mul_le_mul_of_nonneg_left hsN hsNpos.le
      nlinarith
    have hP : (N : ℝ) ^ N * (Real.exp 1)⁻¹ ^ N * Real.exp ν ≤
        ν ^ N * Real.exp ((d / Real.sqrt ν) ^ 2) := by
      rw [← hexp]
      have : 0 ≤ (Real.exp 1)⁻¹ ^ N * Real.exp ν := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hpow this]
    have hpos1 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
    calc d / N * Real.exp ν * (Real.exp 1 * Real.sqrt N * ((N : ℝ) ^ N * (Real.exp 1)⁻¹ ^ N))
        = Real.exp 1 * (d / N * Real.sqrt N) * ((N : ℝ) ^ N * (Real.exp 1)⁻¹ ^ N * Real.exp ν) := by ring
      _ ≤ Real.exp 1 * (d / Real.sqrt ν) * (ν ^ N * Real.exp ((d / Real.sqrt ν) ^ 2)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hdN hpos1) hP (by positivity) (by positivity)
      _ = _ := by ring
  have : d / N * (∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ)) =
      d / N * (∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ)) / (ν ^ N / (N.factorial : ℝ)) *
        (ν ^ N / (N.factorial : ℝ)) := by field_simp
  -- goal: d/N*b ≤ RHS * (ν^N/N!)
  calc d / N * (∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ))
      ≤ d / N * Real.exp ν := key1
    _ = d / N * Real.exp ν * (N.factorial : ℝ) / (N.factorial : ℝ) := by field_simp
    _ ≤ Real.exp 1 * (d / Real.sqrt ν) * Real.exp ((d / Real.sqrt ν) ^ 2) * ν ^ N / (N.factorial : ℝ) :=
        div_le_div_of_nonneg_right goal2 hfpos.le
    _ = _ := by ring

end B058Aux

namespace B058Aux

open DimCallCenters.Rationalized Set

lemma waitCost_nonneg (M : WaitModel) (lam : ℝ) (hlam : 0 < lam) (N : ℝ) (hN : lam / M.μ < N) :
    0 ≤ waitCost M N lam := by
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

end B058Aux

namespace DimCC8b6

open DimCallCenters.Rationalized DimCallCenters.QualityDriven Set

/-- `log (√(2π) Q)` in the server variable `N`. -/
noncomputable def qg (ν N : ℝ) : ℝ :=
  N - ν + N * Real.log ν - N * Real.log N + Real.log N / 2 - Real.log (N - ν)

noncomputable def d1 (ν N : ℝ) : ℝ := Real.log ν - Real.log N + N⁻¹ / 2 - (N - ν)⁻¹

noncomputable def d2 (ν N : ℝ) : ℝ := -N⁻¹ - (N ^ 2)⁻¹ / 2 + ((N - ν) ^ 2)⁻¹

lemma qg_deriv (ν N : ℝ) (hν : 0 < ν) (hN : ν < N) : HasDerivAt (qg ν) (d1 ν N) N := by
  have hN0 : N ≠ 0 := (lt_trans hν hN).ne'
  have hu0 : N - ν ≠ 0 := (sub_pos.2 hN).ne'
  have h1 : HasDerivAt (fun N : ℝ => N - ν) 1 N := (hasDerivAt_id' N).sub_const ν
  have h2 : HasDerivAt (fun N : ℝ => N * Real.log ν) (1 * Real.log ν) N := (hasDerivAt_id' N).mul_const _
  have h3 : HasDerivAt (fun N : ℝ => N * Real.log N) (1 * Real.log N + N * N⁻¹) N :=
    (hasDerivAt_id' N).mul (Real.hasDerivAt_log hN0)
  have h4 : HasDerivAt (fun N : ℝ => Real.log N / 2) (N⁻¹ / 2) N := (Real.hasDerivAt_log hN0).div_const 2
  have h5 : HasDerivAt (fun N : ℝ => Real.log (N - ν)) (1 / (N - ν)) N := h1.log hu0
  have h := (((h1.add h2).sub h3).add h4).sub h5
  refine h.congr_deriv ?_
  unfold d1
  field_simp
  ring

lemma d1_deriv (ν N : ℝ) (hν : 0 < ν) (hN : ν < N) : HasDerivAt (d1 ν) (d2 ν N) N := by
  have hN0 : N ≠ 0 := (lt_trans hν hN).ne'
  have hu0 : N - ν ≠ 0 := (sub_pos.2 hN).ne'
  have h1 : HasDerivAt (fun N : ℝ => N - ν) 1 N := (hasDerivAt_id' N).sub_const ν
  have h2 : HasDerivAt (fun _ : ℝ => Real.log ν) 0 N := hasDerivAt_const _ _
  have h3 : HasDerivAt (fun N : ℝ => Real.log N) N⁻¹ N := Real.hasDerivAt_log hN0
  have h4 : HasDerivAt (fun N : ℝ => N⁻¹ / 2) (-(N ^ 2)⁻¹ / 2) N := (hasDerivAt_inv hN0).div_const 2
  have h5 : HasDerivAt (fun N : ℝ => (N - ν)⁻¹) (-1 / (N - ν) ^ 2) N := h1.inv hu0
  have h := ((h2.sub h3).add h4).sub h5
  refine h.congr_deriv ?_
  unfold d2
  field_simp
  ring

/-- The key inequality `d1² + d2 > 0`. -/
lemma d_pos (ν N : ℝ) (hν : 0 < ν) (hN : ν < N) : 0 < d1 ν N ^ 2 + d2 ν N := by
  have hNp : 0 < N := lt_trans hν hN
  set u := N - ν with hu
  have hup : 0 < u := sub_pos.2 hN
  have huN : u < N := by linarith
  -- -d1 ≥ B
  have hlog : u / N ≤ Real.log N - Real.log ν := by
    rw [← Real.log_div hNp.ne' hν.ne']
    have := Real.one_sub_inv_le_log_of_pos (div_pos hNp hν)
    rw [inv_div] at this
    have e : 1 - ν / N = u / N := by rw [hu]; field_simp
    linarith
  set B := u / N + u⁻¹ - N⁻¹ / 2 with hB
  have hBpos : 0 < B := by
    have : N⁻¹ < u⁻¹ := inv_strictAnti₀ hup huN
    have : 0 < u / N := div_pos hup hNp
    have : 0 < N⁻¹ := inv_pos.2 hNp
    linarith
  have hd1 : d1 ν N ≤ -B := by
    unfold d1; rw [← hu]; linarith
  have hsq : B ^ 2 ≤ d1 ν N ^ 2 := by nlinarith
  have hT : 0 < B ^ 2 + d2 ν N := by
    have e : B ^ 2 + d2 ν N =
        ((N - u) * (2 * N + u + u ^ 2) + u ^ 4 + 3 / 4 * u ^ 2) / (N ^ 2 * u ^ 2) := by
      rw [hB]; unfold d2; rw [← hu]; field_simp; ring
    rw [e]
    apply div_pos _ (by positivity)
    have : 0 < (N - u) * (2 * N + u + u ^ 2) := mul_pos (by linarith) (by positivity)
    positivity
  linarith

noncomputable def qf (ν N : ℝ) : ℝ := Real.exp (qg ν N)

lemma qf_convex (ν : ℝ) (hν : 0 < ν) : ConvexOn ℝ (Ioi ν) (qf ν) ∧ StrictAntiOn (qf ν) (Ioi ν) := by
  have hD : ∀ N ∈ Ioi ν, HasDerivAt (qf ν) (Real.exp (qg ν N) * d1 ν N) N := by
    intro N hN
    exact (qg_deriv ν N hν hN).exp
  have hD2 : ∀ N ∈ Ioi ν, HasDerivAt (fun N => Real.exp (qg ν N) * d1 ν N)
      (Real.exp (qg ν N) * (d1 ν N ^ 2 + d2 ν N)) N := by
    intro N hN
    have h := ((qg_deriv ν N hν hN).exp).mul (d1_deriv ν N hν hN)
    refine h.congr_deriv ?_
    ring
  have hcont : ContinuousOn (qf ν) (Ioi ν) := fun N hN => (hD N hN).continuousAt.continuousWithinAt
  refine ⟨?_, ?_⟩
  · apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi ν) hcont
    · intro N hN; rw [interior_Ioi] at hN ⊢; exact (hD N hN).hasDerivWithinAt
    · intro N hN; rw [interior_Ioi] at hN ⊢; exact (hD2 N hN).hasDerivWithinAt
    · intro N hN
      rw [interior_Ioi] at hN
      exact (mul_pos (Real.exp_pos _) (d_pos ν N hν hN)).le
  · apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi ν) hcont
    · intro N hN; rw [interior_Ioi] at hN ⊢; exact (hD N hN).hasDerivWithinAt
    · intro N hN
      rw [interior_Ioi] at hN
      have hNp : 0 < N := lt_trans hν hN
      have hd : d1 ν N < 0 := by
        have hup : 0 < N - ν := sub_pos.2 hN
        have hlog : (N - ν) / N ≤ Real.log N - Real.log ν := by
          rw [← Real.log_div hNp.ne' hν.ne']
          have := Real.one_sub_inv_le_log_of_pos (div_pos hNp hν)
          rw [inv_div] at this
          have e : 1 - ν / N = (N - ν) / N := by field_simp
          linarith
        have : N⁻¹ < (N - ν)⁻¹ := inv_strictAnti₀ hup (by linarith)
        have : 0 < (N - ν) / N := div_pos hup hNp
        have : 0 < N⁻¹ := inv_pos.2 hNp
        unfold d1; linarith
      exact mul_neg_of_pos_of_neg (Real.exp_pos _) hd

lemma Q_eq (μ lam x : ℝ) (hν : 0 < lam / μ) (hx : 0 < x) :
    Qlam μ lam x = qf (lam / μ) (servers μ lam x) / Real.sqrt (2 * Real.pi) := by
  have hs := Real.sqrt_pos.2 hν
  have hN : lam / μ < servers μ lam x := by
    unfold servers; have := mul_pos hx hs; linarith
  set ν := lam / μ with hνdef
  set N := servers μ lam x with hNdef
  have hNp : 0 < N := lt_trans hν hN
  have hup : 0 < N - ν := sub_pos.2 hN
  unfold Qlam ratioLam qf qg
  rw [← hνdef, ← hNdef]
  have e1 : N - ν + N * Real.log ν - N * Real.log N + Real.log N / 2 - Real.log (N - ν) =
      N * (1 - ν / N + Real.log (ν / N)) + Real.log N / 2 - Real.log (N - ν) := by
    rw [Real.log_div hν.ne' hNp.ne']; field_simp; ring
  rw [e1, Real.exp_sub, Real.exp_add, Real.exp_half, Real.exp_log hNp, Real.exp_log hup,
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi)]
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNp.le
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have e2 : 1 - ν / N = (N - ν) / N := by field_simp
  rw [e2]
  field_simp
  rw [Real.sq_sqrt hNp.le]

lemma Q_convex_anti (μ lam : ℝ) (hν : 0 < lam / μ) :
    ConvexOn ℝ (Ioi 0) (Qlam μ lam) ∧ AntitoneOn (Qlam μ lam) (Ioi 0) := by
  obtain ⟨hc, ha⟩ := qf_convex (lam / μ) hν
  have hs := Real.sqrt_pos.2 hν
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have hmem : ∀ x : ℝ, 0 < x → servers μ lam x ∈ Ioi (lam / μ) := by
    intro x hx; show lam / μ < _; unfold servers; have := mul_pos hx hs; linarith
  refine ⟨⟨convex_Ioi 0, fun x hx z hz a b ha0 hb0 hab => ?_⟩, fun x hx z hz hxz => ?_⟩
  · have hx' : (0:ℝ) < x := hx
    have hz' : (0:ℝ) < z := hz
    have hxz : 0 < a • x + b • z := by
      simp only [smul_eq_mul]
      rcases eq_or_lt_of_le ha0 with h | h
      · rw [← h] at hab ⊢; simp at hab; rw [hab]; linarith
      · have := mul_pos h hx'; have := mul_nonneg hb0 hz'.le; linarith
    have h := hc.2 (hmem x hx') (hmem z hz') ha0 hb0 hab
    have e : servers μ lam (a • x + b • z) = a • servers μ lam x + b • servers μ lam z := by
      simp only [smul_eq_mul]; unfold servers
      linear_combination (-(lam / μ)) * hab
    rw [Q_eq μ lam _ hν hxz, Q_eq μ lam _ hν hx', Q_eq μ lam _ hν hz', e]
    simp only [smul_eq_mul] at h ⊢
    rw [div_le_iff₀ hpi]
    have : a * (qf (lam / μ) (servers μ lam x) / Real.sqrt (2 * Real.pi)) +
        b * (qf (lam / μ) (servers μ lam z) / Real.sqrt (2 * Real.pi)) =
        (a * qf (lam / μ) (servers μ lam x) + b * qf (lam / μ) (servers μ lam z)) /
          Real.sqrt (2 * Real.pi) := by ring
    rw [this, div_mul_cancel₀ _ hpi.ne']
    exact h
  · have hx' : (0:ℝ) < x := hx
    have hz' : (0:ℝ) < z := hz
    rw [Q_eq μ lam _ hν hx', Q_eq μ lam _ hν hz']
    apply div_le_div_of_nonneg_right _ hpi.le
    apply ha.antitoneOn (hmem x hx') (hmem z hz')
    unfold servers
    have := mul_le_mul_of_nonneg_right hxz hs.le
    linarith

end DimCC8b6


namespace DimCC8b6

open DimCallCenters.Rationalized DimCallCenters.QualityDriven Set

/-- Stirling ratio `σ_N = N! / (√(2πN) (N/e)^N)`. -/
noncomputable def sig (N : ℕ) : ℝ :=
  (N.factorial : ℝ) / (Real.sqrt (2 * Real.pi * N) * ((N : ℝ) / Real.exp 1) ^ N)

lemma sig_eq (N : ℕ) : sig N = Stirling.stirlingSeq N / Real.sqrt Real.pi := by
  unfold sig Stirling.stirlingSeq
  have e : Real.sqrt (2 * Real.pi * N) = Real.sqrt (2 * (N : ℝ)) * Real.sqrt Real.pi := by
    rw [← Real.sqrt_mul (by positivity)]; ring_nf
  rw [e, div_div, mul_right_comm]

lemma sig_ge_one (N : ℕ) (hN : N ≠ 0) : 1 ≤ sig N := by
  rw [sig_eq, le_div_iff₀ (Real.sqrt_pos.2 Real.pi_pos), one_mul]
  exact Stirling.sqrt_pi_le_stirlingSeq hN

lemma sig_tendsto : Tendsto sig atTop (𝓝 1) := by
  have h := Stirling.tendsto_stirlingSeq_sqrt_pi.div_const (Real.sqrt Real.pi)
  rw [div_self (Real.sqrt_pos.2 Real.pi_pos).ne'] at h
  have e : sig = fun N => Stirling.stirlingSeq N / Real.sqrt Real.pi := funext sig_eq
  rw [e]; exact h

lemma term_le (ν : ℝ) (hν : 0 ≤ ν) (N : ℕ) (hN : 0 < N) (j : ℕ) :
    ν ^ (N + j) / ((N + j).factorial : ℝ) ≤ ν ^ N / (N.factorial : ℝ) * (ν / N) ^ j := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hf : (N.factorial : ℝ) * (N : ℝ) ^ j ≤ ((N + j).factorial : ℝ) := by
    have h1 := Nat.factorial_mul_pow_le_factorial (m := N) (n := j)
    have h2 : (N.factorial : ℝ) * (N : ℝ) ^ j ≤ (N.factorial : ℝ) * ((N : ℝ) + 1) ^ j := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact pow_le_pow_left₀ hNr.le (by linarith) j
    have h3 : (N.factorial : ℝ) * ((N : ℝ) + 1) ^ j ≤ ((N + j).factorial : ℝ) := by exact_mod_cast h1
    linarith
  have hpos : (0 : ℝ) < (N.factorial : ℝ) * (N : ℝ) ^ j := by positivity
  calc ν ^ (N + j) / ((N + j).factorial : ℝ) ≤ ν ^ (N + j) / ((N.factorial : ℝ) * (N : ℝ) ^ j) :=
        div_le_div_of_nonneg_left (by positivity) hpos hf
    _ = ν ^ N / (N.factorial : ℝ) * (ν / N) ^ j := by
        rw [pow_add, div_pow]; field_simp

lemma exp_hasSum (ν : ℝ) : HasSum (fun n : ℕ => ν ^ n / (n.factorial : ℝ)) (Real.exp ν) := by
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  exact (Real.summable_pow_div_factorial ν).hasSum

/-- Tail bound: `e^ν ≤ ∑_{n<N} ν^n/n! + (ν^N/N!)/(1 - ν/N)`. -/
lemma tail (ν : ℝ) (hν : 0 ≤ ν) (N : ℕ) (hN : ν < N) :
    Real.exp ν ≤ ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ) +
      ν ^ N / (N.factorial : ℝ) / (1 - ν / N) := by
  have hNr : (0 : ℝ) < N := lt_of_le_of_lt hν hN
  have hN0 : 0 < N := by exact_mod_cast hNr
  set a := ν ^ N / (N.factorial : ℝ) with ha
  set r := ν / N with hr
  have hr0 : 0 ≤ r := div_nonneg hν hNr.le
  have hr1 : r < 1 := by rw [hr, div_lt_one hNr]; exact hN
  have ha0 : 0 ≤ a := by positivity
  set S := ∑ n ∈ Finset.range N, ν ^ n / (n.factorial : ℝ) with hS
  have hpart : ∀ m : ℕ, ∑ n ∈ Finset.range (N + m), ν ^ n / (n.factorial : ℝ) ≤
      S + a * ∑ j ∈ Finset.range m, r ^ j := by
    intro m
    induction m with
    | zero => simp [hS]
    | succ m ih =>
      rw [← add_assoc, Finset.sum_range_succ, Finset.sum_range_succ, mul_add]
      have := term_le ν hν N hN0 m
      linarith
  have hgeom : ∀ m : ℕ, ∑ j ∈ Finset.range m, r ^ j ≤ 1 / (1 - r) := by
    intro m
    have h1r : 0 < 1 - r := by linarith
    rw [geom_sum_eq hr1.ne]
    have e : (r ^ m - 1) / (r - 1) = (1 - r ^ m) / (1 - r) := by
      rw [← neg_sub 1 (r ^ m), ← neg_sub 1 r, neg_div_neg_eq]
    rw [e]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hr0 m]) h1r.le
  have hbound : ∀ M : ℕ, ∑ n ∈ Finset.range M, ν ^ n / (n.factorial : ℝ) ≤ S + a / (1 - r) := by
    intro M
    have h1 : ∑ n ∈ Finset.range M, ν ^ n / (n.factorial : ℝ) ≤
        ∑ n ∈ Finset.range (N + M), ν ^ n / (n.factorial : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun i _ _ => by positivity)
    have h2 := hpart M
    have h3 := mul_le_mul_of_nonneg_left (hgeom M) ha0
    have e : a * (1 / (1 - r)) = a / (1 - r) := by ring
    linarith
  exact le_of_tendsto' (exp_hasSum ν).tendsto_sum_nat hbound

/-- Algebra of the two delay-probability bounds. -/
lemma P_alg (a σ E Sm q : ℝ) (ha : 0 < a) (hσ : 1 ≤ σ) (hq : 0 < q) (hE : 0 < E) (hS : 0 ≤ Sm)
    (hSE : Sm ≤ E) (htail : E ≤ Sm + a / q) :
    a * (q * Sm + a)⁻¹ ≤ a * σ / (E * q) ∧
      (a * σ / (E * q)) / (σ + a * σ / (E * q)) ≤ a * (q * Sm + a)⁻¹ := by
  have hden : 0 < q * Sm + a := by positivity
  have hEq : 0 < E * q := mul_pos hE hq
  constructor
  · rw [← div_eq_mul_inv, div_le_div_iff₀ hden hEq]
    have h1 : E * q ≤ q * Sm + a := by
      have := mul_le_mul_of_nonneg_left htail hq.le
      rw [mul_add, mul_div_cancel₀ _ hq.ne'] at this
      linarith
    have h2 : q * Sm + a ≤ σ * (q * Sm + a) := le_mul_of_one_le_left hden.le hσ
    nlinarith
  · have hσ0 : 0 < σ := by linarith
    have e : (a * σ / (E * q)) / (σ + a * σ / (E * q)) = a / (E * q + a) := by
      field_simp
    rw [e, ← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left ha.le hden
    have := mul_le_mul_of_nonneg_left hSE hq.le
    linarith

end DimCC8b6

namespace DimCC8b6

open DimCallCenters.Rationalized DimCallCenters.QualityDriven Set

lemma servers_x (μ lam N : ℝ) (hν : 0 < lam / μ) :
    servers μ lam ((N - lam / μ) / Real.sqrt (lam / μ)) = N := by
  have hs : Real.sqrt (lam / μ) ≠ 0 := (Real.sqrt_pos.2 hν).ne'
  unfold servers
  rw [div_mul_cancel₀ _ hs]
  ring

lemma xN_pos (ν : ℝ) (hν : 0 < ν) (N : ℝ) (h : ν < N) : 0 < (N - ν) / Real.sqrt ν :=
  div_pos (by linarith) (Real.sqrt_pos.2 hν)

lemma Q_int (μ lam : ℝ) (hν : 0 < lam / μ) (N : ℕ) (hN : lam / μ < N) :
    Qlam μ lam (((N : ℝ) - lam / μ) / Real.sqrt (lam / μ)) =
      (lam / μ) ^ N / (N.factorial : ℝ) * sig N / (Real.exp (lam / μ) * (1 - lam / μ / N)) := by
  rw [Q_eq μ lam _ hν (xN_pos _ hν _ hN), servers_x μ lam N hν]
  unfold qf qg sig
  set ν := lam / μ with hνdef
  have hNp : (0 : ℝ) < N := lt_trans hν hN
  have hup : 0 < (N : ℝ) - ν := sub_pos.2 hN
  have e : (N : ℝ) - ν + N * Real.log ν - N * Real.log N + Real.log N / 2 - Real.log (N - ν) =
      (N * 1 + N * Real.log ν - N * Real.log N) - ν + Real.log N / 2 - Real.log (N - ν) := by ring
  rw [e]
  simp only [Real.exp_sub, Real.exp_add, Real.exp_nat_mul]
  rw [Real.exp_half, Real.exp_log hν, Real.exp_log hNp, Real.exp_log hup,
    Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi), div_pow]
  have hsN : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 hNp
  have hsq : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hNp.le
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have e2 : 1 - ν / N = ((N : ℝ) - ν) / N := by field_simp
  rw [e2]
  field_simp
  rw [div_pow (N : ℝ)]
  field_simp
  rw [hsq]

lemma P_Q (μ lam : ℝ) (hν : 0 < lam / μ) (N : ℕ) (hN : lam / μ < N) :
    erlangC N (lam / μ) ≤ Qlam μ lam (((N : ℝ) - lam / μ) / Real.sqrt (lam / μ)) ∧
      Qlam μ lam (((N : ℝ) - lam / μ) / Real.sqrt (lam / μ)) /
        (sig N + Qlam μ lam (((N : ℝ) - lam / μ) / Real.sqrt (lam / μ))) ≤ erlangC N (lam / μ) := by
  rw [Q_int μ lam hν N hN]
  have hNp : (0 : ℝ) < N := lt_trans hν hN
  have hN0 : N ≠ 0 := by rintro rfl; simp at hNp
  have hq : 0 < 1 - lam / μ / N := by rw [sub_pos, div_lt_one hNp]; exact hN
  exact P_alg _ _ _ _ _ (by positivity) (sig_ge_one N hN0) hq (Real.exp_pos _)
    (Finset.sum_nonneg (fun n _ => by positivity)) (Real.sum_le_exp_of_nonneg hν.le N)
    (tail _ hν.le N hN)

lemma Q_small (μ lam x : ℝ) (hν : 0 < lam / μ) (hx2 : 2 ≤ x) (hxs : x ≤ Real.sqrt (lam / μ)) :
    Qlam μ lam x ≤ Real.exp (-(x ^ 2) / 6) := by
  have hx : 0 < x := by linarith
  rw [Q_eq μ lam x hν hx]
  unfold qf
  have hpi1 : 1 ≤ Real.sqrt (2 * Real.pi) := by
    rw [Real.one_le_sqrt]; nlinarith [Real.pi_gt_three]
  set ν := lam / μ with hνdef
  set s := Real.sqrt ν with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hν
  have hss : s * s = ν := Real.mul_self_sqrt hν.le
  set N := servers μ lam x with hNdef
  have hNe : N = ν + x * s := by rw [hNdef]; unfold servers; rfl
  have hu : N - ν = x * s := by rw [hNe]; ring
  have hup : 0 < N - ν := by rw [hu]; positivity
  have hNp : 0 < N := by linarith
  have hNnu : 0 < N + ν := by linarith
  -- step A
  have hlogsplit : Real.log N - Real.log ν =
      Real.log ((N + ν) / (2 * ν)) + Real.log (2 * N / (N + ν)) := by
    rw [← Real.log_mul (by positivity) (by positivity), ← Real.log_div hNp.ne' hν.ne']
    congr 1; field_simp
  have h1 := Real.one_sub_inv_le_log_of_pos (show 0 < (N + ν) / (2 * ν) by positivity)
  have h2 := Real.one_sub_inv_le_log_of_pos (show 0 < 2 * N / (N + ν) by positivity)
  rw [inv_div] at h1 h2
  have hA : N * (2 - 2 * ν / (N + ν) - (N + ν) / (2 * N)) ≤ N * (Real.log N - Real.log ν) := by
    apply mul_le_mul_of_nonneg_left _ hNp.le
    rw [hlogsplit]
    have e : 2 - 2 * ν / (N + ν) - (N + ν) / (2 * N) =
        (1 - 2 * ν / (N + ν)) + (1 - (N + ν) / (2 * N)) := by ring
    rw [e]; linarith
  have hB : N * (2 - 2 * ν / (N + ν) - (N + ν) / (2 * N)) - (N - ν) =
      (N - ν) ^ 2 / (2 * (N + ν)) := by
    field_simp; ring
  have hC : x ^ 2 / 6 ≤ (N - ν) ^ 2 / (2 * (N + ν)) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity), hu]
    have hxs' : x * s ≤ s * s := mul_le_mul_of_nonneg_right hxs hs.le
    have : N + ν ≤ 3 * (s * s) := by rw [hNe, ← hss]; linarith
    have hx2' : 0 ≤ x ^ 2 := sq_nonneg x
    nlinarith
  have hD : Real.log N / 2 ≤ Real.log (N - ν) := by
    have hle : N ≤ (N - ν) ^ 2 := by
      rw [hu, hNe, ← hss]
      have hxs' : x * s ≤ s * s := mul_le_mul_of_nonneg_right hxs hs.le
      have : 4 ≤ x ^ 2 := by nlinarith
      nlinarith [mul_pos hs hs]
    have := Real.log_le_log hNp hle
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hqg : N - ν + N * Real.log ν - N * Real.log N + Real.log N / 2 - Real.log (N - ν) ≤
      -(x ^ 2) / 6 := by
    have : N * (Real.log N - Real.log ν) = N * Real.log N - N * Real.log ν := by ring
    have : -(x ^ 2) / 6 = -(x ^ 2 / 6) := by ring
    linarith
  unfold qg
  rw [div_le_iff₀ (by linarith)]
  calc Real.exp (N - ν + N * Real.log ν - N * Real.log N + Real.log N / 2 - Real.log (N - ν))
      ≤ Real.exp (-(x ^ 2) / 6) := Real.exp_le_exp.2 hqg
    _ ≤ Real.exp (-(x ^ 2) / 6) * Real.sqrt (2 * Real.pi) :=
        le_mul_of_one_le_right (Real.exp_pos _).le hpi1

/-- Product of nonnegative antitone convex functions is convex. -/
lemma prod_convex (f g : ℝ → ℝ) (S : Set ℝ) (hf : ConvexOn ℝ S f) (hg : ConvexOn ℝ S g)
    (hfa : AntitoneOn f S) (hga : AntitoneOn g S) (hf0 : ∀ x ∈ S, 0 ≤ f x)
    (hg0 : ∀ x ∈ S, 0 ≤ g x) : ConvexOn ℝ S (fun x => f x * g x) :=
  hf.mul hg (fun x hx => hf0 x hx) (fun x hx => hg0 x hx) (hfa.monovaryOn hga)

end DimCC8b6

namespace DimCC8b6

open Set

/-- Convex function with global minimum at `y` is antitone left of `y` and monotone right of it. -/
lemma side_le (sur : ℝ → ℝ) (hconv : ConvexOn ℝ (Ioi 0) sur) (y : ℝ) (hy0 : 0 < y)
    (hymin : ∀ y', 0 < y' → sur y ≤ sur y') (a b : ℝ) (ha : 0 < a)
    (hab : (a ≤ b ∧ b ≤ y) ∨ (y ≤ b ∧ b ≤ a)) : sur b ≤ sur a := by
  have hya := hymin a ha
  rcases hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hb : b ∈ segment ℝ a y := by rw [segment_eq_Icc (le_trans h1 h2)]; exact ⟨h1, h2⟩
    have := hconv.le_on_segment (show a ∈ Ioi (0:ℝ) from ha) (show y ∈ Ioi (0:ℝ) from hy0) hb
    rw [max_eq_left hya] at this
    exact this
  · have hb : b ∈ segment ℝ y a := by rw [segment_eq_Icc (le_trans h1 h2)]; exact ⟨h1, h2⟩
    have := hconv.le_on_segment (show y ∈ Ioi (0:ℝ) from hy0) (show a ∈ Ioi (0:ℝ) from ha) hb
    rw [max_eq_right hya] at this
    exact this

/-- The per-`λ` comparison: the rounded surrogate optimum costs between `h(N*)` and `s(x*)`. -/
lemma core (ν s : ℝ) (hν0 : 0 ≤ ν) (hs : 0 < s) (Fl G Q : ℝ → ℝ) (P : ℕ → ℝ) (hh : ℕ → ℝ)
    (hhdef : ∀ N : ℕ, hh N = Fl (((N : ℝ) - ν) / s) + P N * G (((N : ℝ) - ν) / s))
    (y m : ℝ) (hy0 : 0 < y) (hm : (m - ν) / s = y)
    (hsconv : ConvexOn ℝ (Ioi 0) (fun x => Fl x + Q x * G x))
    (hymin : ∀ y', 0 < y' → Fl y + Q y * G y ≤ Fl y' + Q y' * G y')
    (hG0 : ∀ x, 0 < x → 0 ≤ G x)
    (hPQ : ∀ N : ℕ, ν < N → P N ≤ Q (((N : ℝ) - ν) / s))
    (Nst : ℕ) (hNst : ν < Nst) (hopt : ∀ N : ℕ, ν < N → hh Nst ≤ hh N) :
    hh Nst ≤ (if (⌊m⌋₊ : ℝ) ≤ ν then hh ⌈m⌉₊ else min (hh ⌊m⌋₊) (hh ⌈m⌉₊)) ∧
    (if (⌊m⌋₊ : ℝ) ≤ ν then hh ⌈m⌉₊ else min (hh ⌊m⌋₊) (hh ⌈m⌉₊)) ≤
      Fl (((Nst : ℝ) - ν) / s) + Q (((Nst : ℝ) - ν) / s) * G (((Nst : ℝ) - ν) / s) := by
  set sur : ℝ → ℝ := fun x => Fl x + Q x * G x with hsur
  have hmν : ν < m := by
    have : 0 < (m - ν) / s := by rw [hm]; exact hy0
    have := (div_pos_iff_of_pos_right hs).1 this
    linarith
  have hxmono : ∀ a b : ℝ, a ≤ b → (a - ν) / s ≤ (b - ν) / s := fun a b hab =>
    div_le_div_of_nonneg_right (by linarith) hs.le
  have hxpos : ∀ N : ℕ, ν < N → 0 < ((N : ℝ) - ν) / s := fun N hN => div_pos (by linarith) hs
  -- h ≤ s at integers
  have hle_sur : ∀ N : ℕ, ν < N → hh N ≤ sur (((N : ℝ) - ν) / s) := by
    intro N hN
    rw [hhdef, hsur]
    have := mul_le_mul_of_nonneg_right (hPQ N hN) (hG0 _ (hxpos N hN))
    simp only; linarith
  have hsmin : ∀ y', 0 < y' → sur y ≤ sur y' := hymin
  have hc_ge : m ≤ (⌈m⌉₊ : ℝ) := Nat.le_ceil m
  have hcν : ν < (⌈m⌉₊ : ℝ) := lt_of_lt_of_le hmν hc_ge
  have hxc : y ≤ ((⌈m⌉₊ : ℝ) - ν) / s := by rw [← hm]; exact hxmono _ _ hc_ge
  -- right case: Nst ≥ ⌈m⌉
  have right : ⌈m⌉₊ ≤ Nst → hh ⌈m⌉₊ ≤ sur (((Nst : ℝ) - ν) / s) := by
    intro hle
    have hle' : (⌈m⌉₊ : ℝ) ≤ Nst := by exact_mod_cast hle
    calc hh ⌈m⌉₊ ≤ sur (((⌈m⌉₊ : ℕ) - ν) / s) := hle_sur _ hcν
      _ ≤ sur (((Nst : ℝ) - ν) / s) :=
          side_le sur hsconv y hy0 hsmin _ _ (hxpos Nst hNst)
            (Or.inr ⟨hxc, hxmono _ _ hle'⟩)
  have hceil_floor : ⌈m⌉₊ ≤ ⌊m⌋₊ + 1 := Nat.ceil_le_floor_add_one m
  split_ifs with hf
  · refine ⟨hopt _ hcν, ?_⟩
    apply right
    have : ⌊m⌋₊ < Nst := by
      have : (⌊m⌋₊ : ℝ) < Nst := lt_of_le_of_lt hf hNst
      exact_mod_cast this
    omega
  · push_neg at hf
    refine ⟨le_min (hopt _ hf) (hopt _ hcν), ?_⟩
    by_cases hcase : Nst ≤ ⌊m⌋₊
    · have hle' : (Nst : ℝ) ≤ ⌊m⌋₊ := by exact_mod_cast hcase
      have hfm : (⌊m⌋₊ : ℝ) ≤ m := Nat.floor_le (by linarith)
      have hxf : ((⌊m⌋₊ : ℝ) - ν) / s ≤ y := by rw [← hm]; exact hxmono _ _ hfm
      calc min (hh ⌊m⌋₊) (hh ⌈m⌉₊) ≤ hh ⌊m⌋₊ := min_le_left _ _
        _ ≤ sur (((⌊m⌋₊ : ℕ) - ν) / s) := hle_sur _ hf
        _ ≤ sur (((Nst : ℝ) - ν) / s) :=
            side_le sur hsconv y hy0 hsmin _ _ (hxpos Nst hNst)
              (Or.inl ⟨hxmono _ _ hle', hxf⟩)
    · push_neg at hcase
      calc min (hh ⌊m⌋₊) (hh ⌈m⌉₊) ≤ hh ⌈m⌉₊ := min_le_right _ _
        _ ≤ sur (((Nst : ℝ) - ν) / s) := right (by omega)

/-- `s(x*) ≤ (σ + Q*) h(N*)` from the lower delay bound. -/
lemma upper_ratio (Fl P G Q σ : ℝ) (hFl : 0 ≤ Fl) (hG : 0 ≤ G) (hQ : 0 ≤ Q) (hσ : 1 ≤ σ)
    (hP : Q / (σ + Q) ≤ P) : Fl + Q * G ≤ (σ + Q) * (Fl + P * G) := by
  have hsq : 0 < σ + Q := by linarith
  have h1 : Q ≤ (σ + Q) * P := by rwa [div_le_iff₀' hsq] at hP
  have h2 : Q * G ≤ (σ + Q) * P * G := mul_le_mul_of_nonneg_right h1 hG
  have h3 : Fl ≤ (σ + Q) * Fl := le_mul_of_one_le_left hFl (by linarith)
  nlinarith

/-- Localization of the integer optimum: `x* > K`. -/
lemma loc_core (ν s : ℝ) (hν : 0 < ν) (hs : 1 ≤ s) (Fl G Q : ℝ → ℝ) (P : ℕ → ℝ) (hh : ℕ → ℝ)
    (hhdef : ∀ N : ℕ, hh N = Fl (((N : ℝ) - ν) / s) + P N * G (((N : ℝ) - ν) / s))
    (K L c : ℝ) (hK : 0 < K) (hKL : K ≤ L) (hc : 0 < c)
    (hFl0 : ∀ x, 0 < x → 0 ≤ Fl x) (hFlmono : ∀ a b, 0 ≤ a → a ≤ b → Fl a ≤ Fl b)
    (hG0 : ∀ x, 0 < x → 0 < G x) (hGa : AntitoneOn G (Ioi 0)) (hQa : AntitoneOn Q (Ioi 0))
    (hQ0 : ∀ x, 0 < x → 0 ≤ Q x)
    (hPQ : ∀ N : ℕ, ν < N → P N ≤ Q (((N : ℝ) - ν) / s))
    (hQL : Q L ≤ c / 4) (hFlL : Fl (L + 1) < c / 4 * G (L + 1))
    (Nst : ℕ) (hNst : ν < Nst) (hopt : ∀ N : ℕ, ν < N → hh Nst ≤ hh N)
    (hPc : ((Nst : ℝ) - ν) / s ≤ K → c ≤ P Nst) :
    K < ((Nst : ℝ) - ν) / s := by
  have hs0 : 0 < s := by linarith
  by_contra hcon
  push_neg at hcon
  set xs := ((Nst : ℝ) - ν) / s with hxs
  have hxs0 : 0 < xs := div_pos (by linarith) hs0
  have hGK : 0 < G K := hG0 K hK
  -- lower bound at N*
  have hlow : c * G K ≤ hh Nst := by
    rw [hhdef]
    have h1 : G K ≤ G xs := hGa (show xs ∈ Ioi (0:ℝ) from hxs0) (show K ∈ Ioi (0:ℝ) from hK) hcon
    have h2 := hPc hcon
    have h3 : c * G K ≤ P Nst * G xs := mul_le_mul h2 h1 hGK.le (by linarith)
    have := hFl0 xs hxs0
    linarith
  -- comparison staffing N_L = ⌈ν + L s⌉
  set NL := ⌈ν + L * s⌉₊ with hNL
  have hL0 : 0 < L := lt_of_lt_of_le hK hKL
  have hNLge : ν + L * s ≤ (NL : ℝ) := Nat.le_ceil _
  have hNLlt : (NL : ℝ) < ν + L * s + 1 := Nat.ceil_lt_add_one (by
    have := mul_pos hL0 hs0; linarith)
  have hNLν : ν < (NL : ℝ) := by have := mul_pos hL0 hs0; linarith
  set xL := ((NL : ℝ) - ν) / s with hxL
  have hxLge : L ≤ xL := by rw [hxL, le_div_iff₀ hs0]; linarith
  have hxLle : xL ≤ L + 1 := by
    rw [hxL, div_le_iff₀ hs0]
    have : 1 ≤ 1 * s := by linarith
    nlinarith
  have hxL0 : 0 < xL := by linarith
  have hupp : hh NL < c * G K := by
    rw [hhdef]
    have h1 : Fl xL ≤ Fl (L + 1) := hFlmono _ _ hxL0.le hxLle
    have h2 : P NL ≤ Q xL := hPQ NL hNLν
    have h3 : Q xL ≤ Q L := hQa (show L ∈ Ioi (0:ℝ) from hL0) (show xL ∈ Ioi (0:ℝ) from hxL0) hxLge
    have h4 : G xL ≤ G K := hGa (show K ∈ Ioi (0:ℝ) from hK) (show xL ∈ Ioi (0:ℝ) from hxL0)
      (le_trans hKL hxLge)
    have h5 : G (L + 1) ≤ G K := hGa (show K ∈ Ioi (0:ℝ) from hK)
      (show L + 1 ∈ Ioi (0:ℝ) from by show (0:ℝ) < L + 1; linarith) (by linarith)
    have hGxL := hG0 xL hxL0
    have hQxL := hQ0 xL hxL0
    have h6 : P NL * G xL ≤ c / 4 * G K := by
      calc P NL * G xL ≤ Q xL * G xL := mul_le_mul_of_nonneg_right h2 hGxL.le
        _ ≤ Q L * G K := mul_le_mul (le_trans h3 le_rfl) h4 hGxL.le (le_trans hQxL h3)
        _ ≤ c / 4 * G K := mul_le_mul_of_nonneg_right hQL hGK.le
    have h7 : c / 4 * G (L + 1) ≤ c / 4 * G K := mul_le_mul_of_nonneg_left h5 (by linarith)
    have h8 : 0 < c * G K := mul_pos hc hGK
    linarith
  have := hopt NL hNLν
  linarith

end DimCC8b6

namespace DimCC8b6

open DimCallCenters.Rationalized DimCallCenters.QualityDriven Set

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

lemma cost_eq (M : WaitModel) (F : ℝ → ℝ) (lam : ℝ) (hlam : 0 < lam) (N : ℕ) :
    cost M F N lam - F (lam / M.μ) =
      Flam F M.μ lam (((N:ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ)) +
      erlangC N (lam / M.μ) * Glam M lam (((N:ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ)) := by
  have hν : 0 < lam / M.μ := div_pos hlam M.hμ
  unfold cost Flam Glam
  rw [servers_x M.μ lam (N:ℝ) hν]
  ring

lemma G_nonneg (M : WaitModel) (lam : ℝ) (hlam : 0 < lam) (x : ℝ) (hx : 0 < x) :
    0 ≤ Glam M lam x := by
  have hν : 0 < lam / M.μ := div_pos hlam M.hμ
  unfold Glam
  apply mul_nonneg hlam.le
  apply B058Aux.waitCost_nonneg M lam hlam
  unfold servers
  have : 0 < x * Real.sqrt (lam / M.μ) := mul_pos hx (Real.sqrt_pos.2 hν)
  linarith

lemma G_pos (M : WaitModel) (lam : ℝ) (hlam : 0 < lam) (x : ℝ) (hx : 0 < x) :
    0 < Glam M lam x := by
  have h := (LC1_glam M lam hlam).2 (show x ∈ Ioi (0:ℝ) from hx)
    (show x + 1 ∈ Ioi (0:ℝ) from by show (0:ℝ) < x + 1; linarith) (by linarith)
  have := G_nonneg M lam hlam (x + 1) (by linarith)
  linarith

lemma Q_nonneg (μ lam x : ℝ) (hν : 0 < lam / μ) (hx : 0 < x) : 0 ≤ Qlam μ lam x := by
  rw [Q_eq μ lam x hν hx]; unfold qf; positivity

/-- Per-`λ` squeeze: `1 ≤ R(λ) ≤ σ_{N*} + Q_λ(x*)`. -/
lemma pointwise (M : WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Ioi 0) F) (hFmono : StrictMonoOn F (Ioi 0))
    (lam : ℝ) (hlam : 0 < lam) (y : ℝ) (Nst : ℕ)
    (hy : 0 < y ∧ ∀ y' : ℝ, 0 < y' →
        surrogate (Flam F M.μ lam) (Qlam M.μ lam) (Glam M lam) y ≤
          surrogate (Flam F M.μ lam) (Qlam M.μ lam) (Glam M lam) y')
    (hN : lam / M.μ < Nst ∧ ∀ N : ℕ, lam / M.μ < N → cost M F Nst lam ≤ cost M F N lam) :
    1 ≤ (staffCost M F lam y - F (lam / M.μ)) / (cost M F Nst lam - F (lam / M.μ)) ∧
    (staffCost M F lam y - F (lam / M.μ)) / (cost M F Nst lam - F (lam / M.μ)) ≤
      sig Nst + Qlam M.μ lam (((Nst : ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ)) := by
  have hν : 0 < lam / M.μ := div_pos hlam M.hμ
  have hs : 0 < Real.sqrt (lam / M.μ) := Real.sqrt_pos.2 hν
  obtain ⟨hGc, hGa⟩ := LC1_glam M lam hlam
  obtain ⟨hQc, hQa⟩ := Q_convex_anti M.μ lam hν
  have hsconv : ConvexOn ℝ (Ioi 0)
      (fun x => Flam F M.μ lam x + Qlam M.μ lam x * Glam M lam x) :=
    (flam_convex F hFconv M.μ lam hν).add
      (prod_convex _ _ _ hQc hGc.convexOn hQa hGa.antitoneOn
        (fun x hx => Q_nonneg M.μ lam x hν hx) (fun x hx => G_nonneg M lam hlam x hx))
  have hm : (servers M.μ lam y - lam / M.μ) / Real.sqrt (lam / M.μ) = y := by
    have e : servers M.μ lam y - lam / M.μ = y * Real.sqrt (lam / M.μ) := by unfold servers; ring
    rw [e, mul_div_cancel_right₀ _ hs.ne']
  obtain ⟨c1, c2⟩ := core (lam / M.μ) (Real.sqrt (lam / M.μ)) hν.le hs (Flam F M.μ lam) (Glam M lam)
    (Qlam M.μ lam) (fun N => erlangC N (lam / M.μ)) (fun N => cost M F N lam - F (lam / M.μ))
    (fun N => cost_eq M F lam hlam N) y (servers M.μ lam y) hy.1 hm hsconv hy.2
    (fun x hx => G_nonneg M lam hlam x hx) (fun N hN => (P_Q M.μ lam hν N hN).1) Nst hN.1
    (fun N hN' => by linarith [hN.2 N hN'])
  have hstc : staffCost M F lam y - F (lam / M.μ) =
      (if (⌊servers M.μ lam y⌋₊ : ℝ) ≤ lam / M.μ then cost M F ⌈servers M.μ lam y⌉₊ lam - F (lam / M.μ)
        else min (cost M F ⌊servers M.μ lam y⌋₊ lam - F (lam / M.μ))
          (cost M F ⌈servers M.μ lam y⌉₊ lam - F (lam / M.μ))) := by
    unfold staffCost
    split_ifs
    · rfl
    · rw [min_sub_sub_right]
  try simp only at c1 c2
  rw [← hstc] at c1 c2
  set xs := ((Nst : ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ) with hxs
  have hxs0 : 0 < xs := div_pos (by linarith [hN.1]) hs
  have hceq := cost_eq M F lam hlam Nst
  rw [← hxs] at hceq
  have hFl := flam_pos F hFmono M.μ lam hν xs hxs0
  have hG := G_nonneg M lam hlam xs hxs0
  have hP := (P_Q M.μ lam hν Nst hN.1)
  rw [← hxs] at hP
  have hP0 : 0 ≤ erlangC Nst (lam / M.μ) := (B058Aux.erlang_pos_le Nst _ hν hN.1).1.le
  have hpos : 0 < cost M F Nst lam - F (lam / M.μ) := by
    rw [hceq]; have := mul_nonneg hP0 hG; linarith
  have hNst0 : Nst ≠ 0 := by
    have h0 : (0:ℝ) < Nst := lt_trans hν hN.1
    exact_mod_cast h0.ne'
  have hup := upper_ratio (Flam F M.μ lam xs) (erlangC Nst (lam / M.μ)) (Glam M lam xs)
    (Qlam M.μ lam xs) (sig Nst) hFl.le hG (Q_nonneg M.μ lam xs hν hxs0) (sig_ge_one Nst hNst0) hP.2
  rw [← hceq] at hup
  constructor
  · rw [one_le_div hpos]; exact c1
  · rw [div_le_iff₀ hpos]; linarith

lemma exp_small : Tendsto (fun L : ℝ => Real.exp (-(L ^ 2) / 6)) atTop (𝓝 0) := by
  apply Real.tendsto_exp_atBot.comp
  apply Tendsto.atBot_div_const (by norm_num : (0:ℝ) < 6)
  exact tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)

/-- Localization: the integer optimum satisfies `x*_λ → ∞`. -/
lemma loc (M : WaitModel) (F : ℝ → ℝ)
    (hFmono : StrictMonoOn F (Ioi 0))
    (hreg : ∀ κ : ℝ, 0 < κ →
      Tendsto (fun lam => Flam F M.μ lam κ / Glam M lam κ) atTop (𝓝 0))
    (Nstar : ℝ → ℕ)
    (hN : ∀ lam : ℝ, 0 < lam → lam / M.μ < Nstar lam ∧
      ∀ N : ℕ, lam / M.μ < N → cost M F (Nstar lam) lam ≤ cost M F N lam)
    (K : ℝ) (hK : 0 < K) :
    ∀ᶠ lam in atTop, K < ((Nstar lam : ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ) := by
  have hμ := M.hμ
  set B := 1 + Real.exp 1 * K * Real.exp (K ^ 2) with hB
  have hB0 : 0 < B := by positivity
  set c := 1 / B with hc
  have hc0 : 0 < c := by positivity
  obtain ⟨L, hL1, hL2⟩ := (((exp_small.eventually (ge_mem_nhds (show (0:ℝ) < c / 4 by positivity)))).and
    (eventually_ge_atTop (max K 2))).exists
  have hLK : K ≤ L := le_trans (le_max_left _ _) hL2
  have hL2' : 2 ≤ L := le_trans (le_max_right _ _) hL2
  have hdiv : Tendsto (fun lam : ℝ => lam / M.μ) atTop atTop := tendsto_id.atTop_div_const hμ
  filter_upwards [eventually_gt_atTop (0:ℝ), hdiv.eventually (eventually_ge_atTop ((L + 1) ^ 2)),
    (hreg (L + 1) (by linarith)).eventually (gt_mem_nhds (show (0:ℝ) < c / 4 by positivity))]
    with lam hlam hνL hratio
  have hν : 0 < lam / M.μ := div_pos hlam hμ
  have hsL : L + 1 ≤ Real.sqrt (lam / M.μ) := Real.le_sqrt_of_sq_le hνL
  have hs1 : 1 ≤ Real.sqrt (lam / M.μ) := by linarith
  have hGL := G_pos M lam hlam (L + 1) (by linarith)
  obtain ⟨hGc, hGa⟩ := LC1_glam M lam hlam
  obtain ⟨hQc, hQa⟩ := Q_convex_anti M.μ lam hν
  apply loc_core (lam / M.μ) (Real.sqrt (lam / M.μ)) hν hs1 (Flam F M.μ lam) (Glam M lam)
    (Qlam M.μ lam) (fun N => erlangC N (lam / M.μ)) (fun N => cost M F N lam - F (lam / M.μ))
    (fun N => cost_eq M F lam hlam N) K L c hK hLK hc0
    (fun x hx => flam_nonneg F hFmono M.μ lam hν x hx.le)
    (fun a b ha hab => flam_mono F hFmono M.μ lam hν a b ha hab)
    (fun x hx => G_pos M lam hlam x hx) hGa.antitoneOn hQa
    (fun x hx => Q_nonneg M.μ lam x hν hx) (fun N hN' => (P_Q M.μ lam hν N hN').1)
  · exact le_trans (Q_small M.μ lam L hν hL2' (by linarith)) hL1
  · exact (div_lt_iff₀ hGL).1 hratio
  · exact (hN lam hlam).1
  · intro N hN'
    try simp only
    linarith [(hN lam hlam).2 N hN']
  · intro hxK
    have hNν := (hN lam hlam).1
    obtain ⟨hP0, -, -⟩ := B058Aux.erlang_pos_le (Nstar lam) _ hν hNν
    have hb := B058Aux.erlang_bound (Nstar lam) _ hν hNν
    set t := ((Nstar lam : ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ) with ht
    have ht0 : 0 < t := div_pos (by linarith) (Real.sqrt_pos.2 hν)
    have hmono : Real.exp 1 * t * Real.exp (t ^ 2) ≤ Real.exp 1 * K * Real.exp (K ^ 2) := by
      have h1 : Real.exp (t ^ 2) ≤ Real.exp (K ^ 2) := Real.exp_le_exp.2 (by nlinarith)
      have h2 : Real.exp 1 * t ≤ Real.exp 1 * K := mul_le_mul_of_nonneg_left hxK (Real.exp_pos 1).le
      exact mul_le_mul h2 h1 (Real.exp_pos _).le (by positivity)
    have h3 : 1 / erlangC (Nstar lam) (lam / M.μ) ≤ B := by rw [hB]; linarith
    try simp only
    rw [hc]
    have := one_div_le_one_div_of_le (by positivity : 0 < 1 / erlangC (Nstar lam) (lam / M.μ)) h3
    rwa [one_div_one_div] at this

end DimCC8b6

open DimCC8b6 in
open DimCallCenters.QualityDriven Filter Topology in
theorem solution (M : DimCallCenters.Rationalized.WaitModel) (F : ℝ → ℝ)
    (hFconv : ConvexOn ℝ (Set.Ioi 0) F) (hFmono : StrictMonoOn F (Set.Ioi 0))
    (hGinf : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun N => DimCallCenters.Rationalized.waitCost M N lam) (𝓝[>] (lam / M.μ)) atTop)
    (hreg : ∀ κ : ℝ, 0 < κ →
      Tendsto (fun lam => DimCallCenters.Rationalized.Flam F M.μ lam κ / DimCallCenters.Rationalized.Glam M lam κ) atTop (𝓝 0))
    (y : ℝ → ℝ)
    (hy : ∀ lam : ℝ, 0 < lam → 0 < y lam ∧
      ∀ y' : ℝ, 0 < y' →
        DimCallCenters.Rationalized.surrogate (DimCallCenters.Rationalized.Flam F M.μ lam) (Qlam M.μ lam) (DimCallCenters.Rationalized.Glam M lam) (y lam) ≤
          DimCallCenters.Rationalized.surrogate (DimCallCenters.Rationalized.Flam F M.μ lam) (Qlam M.μ lam) (DimCallCenters.Rationalized.Glam M lam) y')
    (Nstar : ℝ → ℕ)
    (hN : ∀ lam : ℝ, 0 < lam → lam / M.μ < Nstar lam ∧
      ∀ N : ℕ, lam / M.μ < N → DimCallCenters.Rationalized.cost M F (Nstar lam) lam ≤ DimCallCenters.Rationalized.cost M F N lam) :
    Tendsto (fun lam => (DimCallCenters.Rationalized.staffCost M F lam (y lam) - F (lam / M.μ)) /
      (DimCallCenters.Rationalized.cost M F (Nstar lam) lam - F (lam / M.μ))) atTop (𝓝 1) := by
  have hμ := M.hμ
  have hdiv : Tendsto (fun lam : ℝ => lam / M.μ) atTop atTop := tendsto_id.atTop_div_const hμ
  -- N* → ∞, hence σ_{N*} → 1
  have hNat : Tendsto Nstar atTop atTop := by
    apply (tendsto_natCast_atTop_iff (R := ℝ)).1
    apply tendsto_atTop_mono' atTop _ hdiv
    filter_upwards [eventually_gt_atTop (0:ℝ)] with lam hlam
    exact (hN lam hlam).1.le
  have hsig : Tendsto (fun lam => sig (Nstar lam)) atTop (𝓝 1) := sig_tendsto.comp hNat
  -- Q_λ(x*) → 0
  have hQ : Tendsto (fun lam => Qlam M.μ lam (((Nstar lam : ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ)))
      atTop (𝓝 0) := by
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [eventually_gt_atTop (0:ℝ)] with lam hlam
      have hν : 0 < lam / M.μ := div_pos hlam hμ
      have hx0 : 0 < ((Nstar lam : ℝ) - lam / M.μ) / Real.sqrt (lam / M.μ) :=
        div_pos (by linarith [(hN lam hlam).1]) (Real.sqrt_pos.2 hν)
      exact lt_of_lt_of_le ha (Q_nonneg M.μ lam _ hν hx0)
    · intro b hb
      obtain ⟨K, hK1, hK2⟩ := ((exp_small.eventually (gt_mem_nhds hb)).and
        (eventually_ge_atTop (2:ℝ))).exists
      filter_upwards [eventually_gt_atTop (0:ℝ), hdiv.eventually (eventually_ge_atTop (K ^ 2)),
        loc M F hFmono hreg Nstar hN K (by linarith)] with lam hlam hνK hloc
      have hν : 0 < lam / M.μ := div_pos hlam hμ
      have hsK : K ≤ Real.sqrt (lam / M.μ) := Real.le_sqrt_of_sq_le hνK
      obtain ⟨-, hQa⟩ := Q_convex_anti M.μ lam hν
      have h1 := hQa (show K ∈ Set.Ioi (0:ℝ) from by show (0:ℝ) < K; linarith)
        (show _ ∈ Set.Ioi (0:ℝ) from by show (0:ℝ) < _; linarith) hloc.le
      have h2 := Q_small M.μ lam K hν hK2 hsK
      linarith
  have hup := hsig.add hQ
  rw [add_zero] at hup
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with lam hlam
    exact (pointwise M F hFconv hFmono lam hlam (y lam) (Nstar lam) (hy lam hlam) (hN lam hlam)).1
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with lam hlam
    exact (pointwise M F hFconv hFmono lam hlam (y lam) (Nstar lam) (hy lam hlam) (hN lam hlam)).2
