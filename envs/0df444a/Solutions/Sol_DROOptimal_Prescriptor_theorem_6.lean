-- Prove2me | solution 1 for DROOptimal.Prescriptor.theorem_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T18:01:09.845998+00:00
-- url     : https://prove2.me/submissions/2c2594ab-1385-495a-92d4-1b791bf69830

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Prescriptor_Pairs

set_option autoImplicit false

open Filter Topology

namespace DRO6Aux

lemma mul_log_div_eq (x p : ℝ) (hp : p ≠ 0) :
    x * Real.log (x / p) = x * Real.log x - x * Real.log p := by
  by_cases hx : x = 0
  · simp [hx]
  · rw [Real.log_div hx hp]; ring

lemma relEntropy_self {d : ℕ} (P : DROOptimal.Predictor.Δ d) :
    DROOptimal.Predictor.relEntropy P P = 0 := by
  unfold DROOptimal.Predictor.relEntropy
  rw [if_pos (fun i h => h)]
  have h : ∀ i, (P : Fin d → ℝ) i * Real.log ((P : Fin d → ℝ) i / (P : Fin d → ℝ) i) = 0 := by
    intro i
    by_cases hi : (P : Fin d → ℝ) i = 0
    · simp [hi]
    · simp [div_self hi]
  simp [h]

lemma relEntropy_of_pos {d : ℕ} (Q P : DROOptimal.Predictor.Δ d)
    (hP : ∀ i, 0 < (P : Fin d → ℝ) i) :
    DROOptimal.Predictor.relEntropy Q P =
      ((∑ i, (Q : Fin d → ℝ) i * Real.log ((Q : Fin d → ℝ) i / (P : Fin d → ℝ) i) : ℝ) : EReal) := by
  unfold DROOptimal.Predictor.relEntropy
  rw [if_pos (fun i h => absurd h (hP i).ne')]

lemma continuous_klsum {d : ℕ} (P : DROOptimal.Predictor.Δ d) (hP : ∀ i, 0 < (P : Fin d → ℝ) i) :
    Continuous (fun Q : DROOptimal.Predictor.Δ d =>
      ∑ i, (Q : Fin d → ℝ) i * Real.log ((Q : Fin d → ℝ) i / (P : Fin d → ℝ) i)) := by
  have h : (fun Q : DROOptimal.Predictor.Δ d =>
      ∑ i, (Q : Fin d → ℝ) i * Real.log ((Q : Fin d → ℝ) i / (P : Fin d → ℝ) i)) =
      fun Q : DROOptimal.Predictor.Δ d => ∑ i, ((Q : Fin d → ℝ) i * Real.log ((Q : Fin d → ℝ) i)
        - (Q : Fin d → ℝ) i * Real.log ((P : Fin d → ℝ) i)) := by
    funext Q
    exact Finset.sum_congr rfl (fun i _ => mul_log_div_eq _ _ (hP i).ne')
  rw [h]
  refine continuous_finsetSum _ (fun i _ => ?_)
  have hc : Continuous (fun Q : DROOptimal.Predictor.Δ d => (Q : Fin d → ℝ) i) :=
    (continuous_apply i).comp continuous_subtype_val
  exact (Real.continuous_mul_log.comp hc).sub (hc.mul continuous_const)

lemma empProb_mono {d : ℕ} (P : DROOptimal.Predictor.Δ d) (T : ℕ)
    {A B : Set (DROOptimal.Predictor.Δ d)} (hAB : A ⊆ B) :
    DROOptimal.Predictor.empProb P T A ≤ DROOptimal.Predictor.empProb P T B := by
  unfold DROOptimal.Predictor.empProb DROOptimal.Predictor.pathProb
  refine Finset.sum_le_sum (fun ω _ => ?_)
  have hnn : 0 ≤ ∏ t, (P : Fin d → ℝ) (ω t) := Finset.prod_nonneg (fun t _ => P.2.1 _)
  by_cases hA : DROOptimal.Predictor.EmpiricalIn ω A
  · have hB : DROOptimal.Predictor.EmpiricalIn ω B := by
      obtain ⟨h, hm⟩ := hA
      exact ⟨h, hAB hm⟩
    rw [if_pos hA, if_pos hB]
  · rw [if_neg hA]
    split_ifs <;> linarith

lemma term_bound (p0 p1 q t u : ℝ) (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hs : p1 = 0 → p0 = 0)
    (ht0 : 0 < t) (ht1 : t < 1) (hu1 : u < 1)
    (hq : (1 - u) * ((1 - t) * p1 + t * p0) ≤ q) :
    p0 * Real.log (p0 / q) ≤ (1 - t) * (p0 * Real.log (p0 / p1)) + p0 * (-Real.log (1 - u)) := by
  rcases hp0.eq_or_lt with h0 | h0
  · rw [← h0]; simp
  have hp1' : 0 < p1 := lt_of_le_of_ne hp1 (fun h => h0.ne' (hs h.symm))
  have h1u : 0 < 1 - u := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hpt : 0 < (1 - t) * p1 + t * p0 := by positivity
  have hconc : (1 - t) * Real.log p1 + t * Real.log p0 ≤ Real.log ((1 - t) * p1 + t * p0) := by
    have := strictConcaveOn_log_Ioi.concaveOn.2 (Set.mem_Ioi.2 hp1') (Set.mem_Ioi.2 h0)
      h1t.le ht0.le (by ring)
    simpa only [smul_eq_mul] using this
  have hpos : 0 < (1 - u) * ((1 - t) * p1 + t * p0) := mul_pos h1u hpt
  have hq0 : 0 < q := lt_of_lt_of_le hpos hq
  have hlogq : Real.log (1 - u) + Real.log ((1 - t) * p1 + t * p0) ≤ Real.log q := by
    rw [← Real.log_mul h1u.ne' hpt.ne']
    exact Real.log_le_log hpos hq
  rw [Real.log_div h0.ne' hq0.ne', Real.log_div h0.ne' hp1'.ne']
  have key : Real.log p0 - Real.log q ≤
      (1 - t) * (Real.log p0 - Real.log p1) + -Real.log (1 - u) := by linarith
  have := mul_le_mul_of_nonneg_left key h0.le
  linarith

lemma exists_pos_model {d : ℕ} (P0 P1 : DROOptimal.Predictor.Δ d) (r : ℝ) (hr : 0 < r)
    (h01 : DROOptimal.Predictor.relEntropy P0 P1 ≤ (r : EReal))
    (g : Fin d → ℝ) (a : ℝ) (ha : a < ∑ i, (P1 : Fin d → ℝ) i * g i) :
    ∃ P : DROOptimal.Predictor.Δ d, (∀ i, 0 < (P : Fin d → ℝ) i) ∧
      (∑ i, (P0 : Fin d → ℝ) i * Real.log ((P0 : Fin d → ℝ) i / (P : Fin d → ℝ) i)) < r ∧
      a < ∑ i, (P : Fin d → ℝ) i * g i := by
  unfold DROOptimal.Predictor.relEntropy at h01
  by_cases hs : ∀ i, (P1 : Fin d → ℝ) i = 0 → (P0 : Fin d → ℝ) i = 0
  swap
  · rw [if_neg hs] at h01
    exact absurd h01 (not_le.mpr (EReal.coe_lt_top r))
  rw [if_pos hs] at h01
  have hR : (∑ i, (P0 : Fin d → ℝ) i * Real.log ((P0 : Fin d → ℝ) i / (P1 : Fin d → ℝ) i)) ≤ r := by
    exact_mod_cast h01
  have hdpos : (0 : ℝ) < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      have := P0.2.2
      simp at this
    · exact_mod_cast h
  obtain ⟨c1, hc1⟩ : ∃ c, c = ∑ i, (P1 : Fin d → ℝ) i * g i := ⟨_, rfl⟩
  obtain ⟨c0, hc0⟩ : ∃ c, c = ∑ i, (P0 : Fin d → ℝ) i * g i := ⟨_, rfl⟩
  obtain ⟨cU, hcU⟩ : ∃ c, c = ∑ i, g i / (d : ℝ) := ⟨_, rfl⟩
  rw [← hc1] at ha
  obtain ⟨t, ⟨ht1, htc⟩, ht0⟩ : ∃ t : ℝ, (t < 1 ∧ a < (1 - t) * c1 + t * c0) ∧ t ∈ Set.Ioi 0 := by
    have hc : Continuous (fun t : ℝ => (1 - t) * c1 + t * c0) := by fun_prop
    have h2 : ∀ᶠ t in 𝓝 (0:ℝ), a < (1 - t) * c1 + t * c0 :=
      (hc.tendsto 0).eventually_const_lt (by simpa using ha)
    have h1 : ∀ᶠ t in 𝓝 (0:ℝ), t < 1 := eventually_lt_nhds (by norm_num)
    have h3 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 ∧ a < (1 - t) * c1 + t * c0 :=
      mem_nhdsWithin_of_mem_nhds (h1.and h2)
    exact (h3.and self_mem_nhdsWithin).exists
  have ht0' : 0 < t := ht0
  obtain ⟨u, ⟨hu1, hu2, huc⟩, hu0⟩ : ∃ u : ℝ, (u < 1 / 2 ∧ u < t * r / 2 ∧
      a < (1 - u) * ((1 - t) * c1 + t * c0) + u * cU) ∧ u ∈ Set.Ioi 0 := by
    have hc : Continuous (fun u : ℝ => (1 - u) * ((1 - t) * c1 + t * c0) + u * cU) := by fun_prop
    have h2 : ∀ᶠ u in 𝓝 (0:ℝ), a < (1 - u) * ((1 - t) * c1 + t * c0) + u * cU :=
      (hc.tendsto 0).eventually_const_lt (by simpa using htc)
    have h1 : ∀ᶠ u in 𝓝 (0:ℝ), u < 1 / 2 := eventually_lt_nhds (by norm_num)
    have h1' : ∀ᶠ u in 𝓝 (0:ℝ), u < t * r / 2 := eventually_lt_nhds (by positivity)
    have h3 : ∀ᶠ u in 𝓝[>] (0:ℝ), u < 1 / 2 ∧ u < t * r / 2 ∧
        a < (1 - u) * ((1 - t) * c1 + t * c0) + u * cU :=
      mem_nhdsWithin_of_mem_nhds (h1.and (h1'.and h2))
    exact (h3.and self_mem_nhdsWithin).exists
  have hu0' : 0 < u := hu0
  have h1u : 0 < 1 - u := by linarith
  have hlog : -Real.log (1 - u) < t * r := by
    have h1 := Real.one_sub_inv_le_log_of_pos h1u
    have h2 : (1 - u)⁻¹ ≤ 1 + 2 * u := by
      rw [inv_eq_one_div, div_le_iff₀ h1u]
      nlinarith [mul_pos hu0' (by linarith : (0:ℝ) < 1 - 2 * u)]
    linarith
  obtain ⟨ps, hps⟩ : ∃ ps : Fin d → ℝ, ps = fun i =>
      (1 - u) * ((1 - t) * (P1 : Fin d → ℝ) i + t * (P0 : Fin d → ℝ) i) + u / d := ⟨_, rfl⟩
  have hpsi : ∀ i, ps i =
      (1 - u) * ((1 - t) * (P1 : Fin d → ℝ) i + t * (P0 : Fin d → ℝ) i) + u / d := by
    intro i; rw [hps]
  have hbase : ∀ i, 0 ≤ (1 - u) * ((1 - t) * (P1 : Fin d → ℝ) i + t * (P0 : Fin d → ℝ) i) := by
    intro i
    have := P1.2.1 i
    have := P0.2.1 i
    have h1t : 0 < 1 - t := by linarith
    positivity
  have hud : 0 < u / (d : ℝ) := div_pos hu0' hdpos
  have hpos : ∀ i, 0 < ps i := by
    intro i; rw [hpsi]; linarith [hbase i]
  have hP0s : ∑ i, (P0 : Fin d → ℝ) i = 1 := P0.2.2
  have hP1s : ∑ i, (P1 : Fin d → ℝ) i = 1 := P1.2.2
  have hsum1 : ∑ i, ps i = 1 := by
    have e : ∀ i, ps i = (1 - u) * (1 - t) * (P1 : Fin d → ℝ) i
        + (1 - u) * t * (P0 : Fin d → ℝ) i + u / d := by
      intro i; rw [hpsi]; ring
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, hP1s, hP0s, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : (d : ℝ) * (u / d) = u := by
      rw [mul_comm]; exact div_mul_cancel₀ u hdpos.ne'
    rw [this]; ring
  have hmem : ps ∈ stdSimplex ℝ (Fin d) := ⟨fun i => (hpos i).le, hsum1⟩
  refine ⟨⟨ps, hmem⟩, hpos, ?_, ?_⟩
  · show (∑ i, (P0 : Fin d → ℝ) i * Real.log ((P0 : Fin d → ℝ) i / ps i)) < r
    have hb : ∑ i, (P0 : Fin d → ℝ) i * Real.log ((P0 : Fin d → ℝ) i / ps i) ≤
        ∑ i, ((1 - t) * ((P0 : Fin d → ℝ) i *
          Real.log ((P0 : Fin d → ℝ) i / (P1 : Fin d → ℝ) i)) +
          (P0 : Fin d → ℝ) i * (-Real.log (1 - u))) := by
      refine Finset.sum_le_sum (fun i _ => ?_)
      refine term_bound _ _ _ t u (P0.2.1 i) (P1.2.1 i) (hs i) ht0' ht1 (by linarith) ?_
      rw [hpsi]; linarith
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hP0s, one_mul] at hb
    have h1t : 0 ≤ 1 - t := by linarith
    have := mul_le_mul_of_nonneg_left hR h1t
    nlinarith
  · show a < ∑ i, ps i * g i
    have e : ∀ i, ps i * g i = (1 - u) * (1 - t) * ((P1 : Fin d → ℝ) i * g i)
        + (1 - u) * t * ((P0 : Fin d → ℝ) i * g i) + u * (g i / d) := by
      intro i; rw [hpsi]; ring
    rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hc1, ← hc0, ← hcU]
    linarith


open DROOptimal.Predictor

lemma nn {d : ℕ} (a : Δ d) (i : Fin d) : 0 ≤ (a : Fin d → ℝ) i := a.2.1 i

lemma mul_log_ge (x : ℝ) (hx : 0 ≤ x) : -1 ≤ x * Real.log x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h]; simp
  · have h1 := Real.one_sub_inv_le_log_of_pos h
    have h2 : x * (1 - x⁻¹) = x - 1 := by field_simp
    have h3 := mul_le_mul_of_nonneg_left h1 h.le
    linarith

lemma coord_le_one {d : ℕ} (P : Δ d) (i : Fin d) : (P : Fin d → ℝ) i ≤ 1 := by
  have hs : ∑ j, (P : Fin d → ℝ) j = 1 := P.2.2
  rw [← hs]
  exact Finset.single_le_sum (fun j _ => nn P j) (Finset.mem_univ i)

/-- Truncated relative entropy, continuous in both arguments. -/
noncomputable def Jt {d : ℕ} (δ : ℝ) (a b : Δ d) : ℝ :=
  ∑ i, ((a : Fin d → ℝ) i * Real.log ((a : Fin d → ℝ) i)
    - (a : Fin d → ℝ) i * Real.log ((b : Fin d → ℝ) i + δ))

lemma Jt_le {d : ℕ} (a b : Δ d) (r : ℝ) (h : relEntropy a b ≤ (r : EReal)) (δ : ℝ)
    (hδ : 0 < δ) : Jt δ a b ≤ r := by
  unfold relEntropy at h
  split_ifs at h with hs
  · have hR : (∑ i, (a : Fin d → ℝ) i * Real.log ((a : Fin d → ℝ) i / (b : Fin d → ℝ) i)) ≤ r := by
      exact_mod_cast h
    refine le_trans (Finset.sum_le_sum (fun i _ => ?_)) hR
    rcases (nn a i).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · have hbp : 0 < (b : Fin d → ℝ) i :=
        lt_of_le_of_ne (nn b i) (fun e => h0.ne' (hs i e.symm))
      rw [mul_log_div_eq _ _ hbp.ne']
      have hl : Real.log ((b : Fin d → ℝ) i) ≤ Real.log ((b : Fin d → ℝ) i + δ) :=
        Real.log_le_log hbp (by linarith)
      have := mul_le_mul_of_nonneg_left hl h0.le
      linarith
  · exact absurd h (not_le.mpr (EReal.coe_lt_top r))

lemma relEntropy_le_of_Jt {d : ℕ} (a b : Δ d) (r : ℝ) (h : ∀ δ : ℝ, 0 < δ → Jt δ a b ≤ r) :
    relEntropy a b ≤ (r : EReal) := by
  have hs : ∀ i, (b : Fin d → ℝ) i = 0 → (a : Fin d → ℝ) i = 0 := by
    intro i hbi
    by_contra hai
    have hapos : 0 < (a : Fin d → ℝ) i := lt_of_le_of_ne (nn a i) (Ne.symm hai)
    set K : ℝ := (|r| + d + d * Real.log 2 + 1) / (a : Fin d → ℝ) i with hK
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hKpos : 0 < K := by rw [hK]; positivity
    set δ : ℝ := Real.exp (-K) with hδ
    have hδpos : 0 < δ := Real.exp_pos _
    have hδ1 : δ ≤ 1 := by rw [hδ]; exact Real.exp_le_one_iff.2 (by linarith)
    have hlogδ : Real.log δ = -K := by rw [hδ, Real.log_exp]
    have hlow : ∀ j, (-1 - Real.log 2) + (if j = i then (a : Fin d → ℝ) i * K else 0) ≤
        (a : Fin d → ℝ) j * Real.log ((a : Fin d → ℝ) j)
          - (a : Fin d → ℝ) j * Real.log ((b : Fin d → ℝ) j + δ) := by
      intro j
      have hm := mul_log_ge _ (nn a j)
      by_cases hj : j = i
      · subst hj
        rw [if_pos rfl, hbi, zero_add, hlogδ]
        nlinarith
      · rw [if_neg hj, add_zero]
        have hb1 := coord_le_one b j
        have ha1 := coord_le_one a j
        have ha0 := nn a j
        have hbpos : 0 < (b : Fin d → ℝ) j + δ := by linarith [nn b j]
        have hL : Real.log ((b : Fin d → ℝ) j + δ) ≤ Real.log 2 :=
          Real.log_le_log hbpos (by linarith)
        have hk : (a : Fin d → ℝ) j * Real.log ((b : Fin d → ℝ) j + δ) ≤ Real.log 2 := by
          rcases le_or_gt (Real.log ((b : Fin d → ℝ) j + δ)) 0 with hn | hn
          · nlinarith
          · nlinarith
        linarith
    have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hlow j)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.sum_ite_eq'] at hsum
    simp only [Finset.mem_univ, if_true, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    have hJ := h δ hδpos
    unfold Jt at hJ
    have hK' : (a : Fin d → ℝ) i * K = |r| + d + d * Real.log 2 + 1 := by
      rw [hK]; field_simp
    have := le_abs_self r
    nlinarith
  unfold relEntropy
  rw [if_pos hs]
  have hlim : Tendsto (fun δ : ℝ => Jt δ a b) (𝓝[>] 0)
      (𝓝 (∑ i, (a : Fin d → ℝ) i * Real.log ((a : Fin d → ℝ) i / (b : Fin d → ℝ) i))) := by
    unfold Jt
    refine tendsto_finset_sum _ (fun i _ => ?_)
    rcases (nn a i).eq_or_lt with h0 | h0
    · rw [← h0]; simp
    · have hbp : 0 < (b : Fin d → ℝ) i :=
        lt_of_le_of_ne (nn b i) (fun e => h0.ne' (hs i e.symm))
      rw [mul_log_div_eq _ _ hbp.ne']
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      have hc : ContinuousAt (fun δ : ℝ => (a : Fin d → ℝ) i * Real.log ((a : Fin d → ℝ) i)
          - (a : Fin d → ℝ) i * Real.log ((b : Fin d → ℝ) i + δ)) 0 := by
        have : ContinuousAt (fun δ : ℝ => Real.log ((b : Fin d → ℝ) i + δ)) 0 :=
          (continuousAt_const.add continuousAt_id).log (by simpa using hbp.ne')
        exact continuousAt_const.sub (continuousAt_const.mul this)
      have ht := hc.tendsto
      simp only [add_zero] at ht
      exact ht
  have hev : ∀ᶠ δ in 𝓝[>] (0:ℝ), Jt δ a b ≤ r :=
    eventually_nhdsWithin_of_forall (fun δ hδ => h δ hδ)
  have := le_of_tendsto hlim hev
  exact_mod_cast this

lemma isClosed_relEntropy_le {d : ℕ} (r : ℝ) :
    IsClosed {q : Δ d × Δ d | relEntropy q.1 q.2 ≤ (r : EReal)} := by
  have e : {q : Δ d × Δ d | relEntropy q.1 q.2 ≤ (r : EReal)} =
      ⋂ δ ∈ Set.Ioi (0:ℝ), {q : Δ d × Δ d | Jt δ q.1 q.2 ≤ r} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_Ioi]
    exact ⟨fun h δ hδ => Jt_le _ _ r h δ hδ, fun h => relEntropy_le_of_Jt _ _ r h⟩
  rw [e]
  refine isClosed_biInter (fun δ hδ => isClosed_le ?_ continuous_const)
  unfold Jt
  refine continuous_finsetSum _ (fun i _ => ?_)
  have ha : Continuous (fun q : Δ d × Δ d => (q.1 : Fin d → ℝ) i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)
  have hb : Continuous (fun q : Δ d × Δ d => (q.2 : Fin d → ℝ) i) :=
    (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  refine (Real.continuous_mul_log.comp ha).sub (ha.mul ?_)
  refine (hb.add continuous_const).log (fun q => ?_)
  have h1 := nn q.2 i
  have h2 : (0:ℝ) < δ := hδ
  have h3 : 0 < (q.2 : Fin d → ℝ) i + δ := by linarith
  exact h3.ne'

lemma eq_of_relEntropy_le_zero {d : ℕ} (a b : Δ d) (h : relEntropy a b ≤ ((0:ℝ) : EReal)) :
    b = a := by
  unfold relEntropy at h
  split_ifs at h with hs
  swap
  · exact absurd h (not_le.mpr (EReal.coe_lt_top 0))
  have hR : (∑ i, (a : Fin d → ℝ) i * Real.log ((a : Fin d → ℝ) i / (b : Fin d → ℝ) i)) ≤ 0 := by
    exact_mod_cast h
  have hterm : ∀ i, 0 ≤ (a : Fin d → ℝ) i * Real.log ((a : Fin d → ℝ) i / (b : Fin d → ℝ) i)
      - ((a : Fin d → ℝ) i - (b : Fin d → ℝ) i) := by
    intro i
    rcases (nn a i).eq_or_lt with h0 | h0
    · rw [← h0]; simpa using nn b i
    · have hbp : 0 < (b : Fin d → ℝ) i :=
        lt_of_le_of_ne (nn b i) (fun e => h0.ne' (hs i e.symm))
      have hx : 0 < (b : Fin d → ℝ) i / (a : Fin d → ℝ) i := div_pos hbp h0
      have hl := Real.log_le_sub_one_of_pos hx
      have hinv : Real.log ((a : Fin d → ℝ) i / (b : Fin d → ℝ) i)
          = -Real.log ((b : Fin d → ℝ) i / (a : Fin d → ℝ) i) := by
        rw [← Real.log_inv, inv_div]
      rw [hinv]
      have e : (a : Fin d → ℝ) i * ((b : Fin d → ℝ) i / (a : Fin d → ℝ) i - 1)
          = (b : Fin d → ℝ) i - (a : Fin d → ℝ) i := by field_simp
      have := mul_le_mul_of_nonneg_left hl h0.le
      linarith
  have ha1 : ∑ i, (a : Fin d → ℝ) i = 1 := a.2.2
  have hb1 : ∑ i, (b : Fin d → ℝ) i = 1 := b.2.2
  have hsum : ∑ i, ((a : Fin d → ℝ) i * Real.log ((a : Fin d → ℝ) i / (b : Fin d → ℝ) i)
      - ((a : Fin d → ℝ) i - (b : Fin d → ℝ) i)) = 0 := by
    apply le_antisymm _ (Finset.sum_nonneg (fun i _ => hterm i))
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ha1, hb1]
    linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hterm i)).1 hsum
  apply Subtype.ext
  funext i
  show (b : Fin d → ℝ) i = (a : Fin d → ℝ) i
  have hzi := hz i (Finset.mem_univ i)
  rcases (nn a i).eq_or_lt with h0 | h0
  · rw [← h0] at hzi ⊢; simp at hzi; linarith
  · have hbp : 0 < (b : Fin d → ℝ) i :=
      lt_of_le_of_ne (nn b i) (fun e => h0.ne' (hs i e.symm))
    have hx : 0 < (b : Fin d → ℝ) i / (a : Fin d → ℝ) i := div_pos hbp h0
    by_contra hne
    have hne' : (b : Fin d → ℝ) i / (a : Fin d → ℝ) i ≠ 1 := by
      intro e; apply hne; field_simp at e; linarith
    have hl := Real.log_lt_sub_one_of_pos hx hne'
    have hinv : Real.log ((a : Fin d → ℝ) i / (b : Fin d → ℝ) i)
        = -Real.log ((b : Fin d → ℝ) i / (a : Fin d → ℝ) i) := by
      rw [← Real.log_inv, inv_div]
    rw [hinv] at hzi
    have e : (a : Fin d → ℝ) i * ((b : Fin d → ℝ) i / (a : Fin d → ℝ) i - 1)
        = (b : Fin d → ℝ) i - (a : Fin d → ℝ) i := by field_simp
    have := mul_lt_mul_of_pos_left hl h0
    linarith

/-- The sup of the linear functional over the relative-entropy ball. -/
noncomputable def F {d : ℕ} (g : Fin d → ℝ) (r : ℝ) (P' : Δ d) : ℝ :=
  sSup ((fun P : Δ d => ∑ i, (P : Fin d → ℝ) i * g i) '' {P : Δ d | relEntropy P' P ≤ (r : EReal)})

lemma lin_le {d : ℕ} (g : Fin d → ℝ) (P : Δ d) : ∑ i, (P : Fin d → ℝ) i * g i ≤ ∑ i, |g i| := by
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h0 := nn P i
  have h1 := coord_le_one P i
  have h2 := le_abs_self (g i)
  have h3 := abs_nonneg (g i)
  nlinarith

lemma F_bdd {d : ℕ} (g : Fin d → ℝ) (r : ℝ) (P' : Δ d) :
    BddAbove ((fun P : Δ d => ∑ i, (P : Fin d → ℝ) i * g i) ''
      {P : Δ d | relEntropy P' P ≤ (r : EReal)}) :=
  ⟨∑ i, |g i|, by rintro y ⟨P, _, rfl⟩; exact lin_le g P⟩

lemma F_ne {d : ℕ} (g : Fin d → ℝ) (r : ℝ) (hr : 0 ≤ r) (P' : Δ d) :
    ((fun P : Δ d => ∑ i, (P : Fin d → ℝ) i * g i) ''
      {P : Δ d | relEntropy P' P ≤ (r : EReal)}).Nonempty := by
  refine ⟨_, P', ?_, rfl⟩
  show relEntropy P' P' ≤ (r : EReal)
  rw [relEntropy_self]
  exact_mod_cast hr

lemma le_F {d : ℕ} (g : Fin d → ℝ) (r : ℝ) (P' P : Δ d) (h : relEntropy P' P ≤ (r : EReal)) :
    ∑ i, (P : Fin d → ℝ) i * g i ≤ F g r P' :=
  le_csSup (F_bdd g r P') ⟨P, h, rfl⟩

lemma F_le_F_add {d : ℕ} (g h : Fin d → ℝ) (r : ℝ) (hr : 0 ≤ r) (P' : Δ d) :
    F g r P' ≤ F h r P' + ∑ i, |g i - h i| := by
  refine csSup_le (F_ne g r hr P') ?_
  rintro y ⟨P, hP, rfl⟩
  have h1 := lin_le (fun i => g i - h i) P
  have e : ∑ i, (P : Fin d → ℝ) i * (g i - h i)
      = ∑ i, (P : Fin d → ℝ) i * g i - ∑ i, (P : Fin d → ℝ) i * h i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h2 := le_F h r P' P hP
  linarith

lemma F_continuous {d : ℕ} (g : Fin d → ℝ) (r : ℝ) (hr : 0 ≤ r) : Continuous (F g r) := by
  have : CompactSpace (Δ d) := isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin d))
  have hlinc : Continuous (fun P : Δ d => ∑ i, (P : Fin d → ℝ) i * g i) :=
    continuous_finsetSum _ (fun i _ =>
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const)
  refine continuous_iff_continuousAt.2 (fun P0 => ?_)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · rcases hr.eq_or_lt with h0 | hpos
    · have hF0 : F g r P0 ≤ ∑ i, (P0 : Fin d → ℝ) i * g i := by
        refine csSup_le (F_ne g r hr P0) ?_
        rintro y ⟨P, hP, rfl⟩
        have hP' : relEntropy P0 P ≤ ((0:ℝ) : EReal) := by rw [h0]; exact hP
        rw [eq_of_relEntropy_le_zero P0 P hP']
      have hev := (hlinc.tendsto P0).eventually_const_lt (lt_of_lt_of_le ha hF0)
      filter_upwards [hev] with Q hQ
      have hself : relEntropy Q Q ≤ (r : EReal) := by
        rw [relEntropy_self]; exact_mod_cast hr
      exact lt_of_lt_of_le hQ (le_F g r Q Q hself)
    · obtain ⟨y, ⟨P1, hP1, rfl⟩, hy⟩ := exists_lt_of_lt_csSup (F_ne g r hr P0) ha
      obtain ⟨Ps, hpos', hkl, hlin⟩ := exists_pos_model P0 P1 r hpos hP1 g a hy
      have hev := ((continuous_klsum Ps hpos').tendsto P0).eventually_lt_const hkl
      filter_upwards [hev] with Q hQ
      have hrel : relEntropy Q Ps ≤ (r : EReal) := by
        rw [relEntropy_of_pos Q Ps hpos']
        exact_mod_cast hQ.le
      exact lt_of_lt_of_le hlin (le_F g r Q Ps hrel)
  · by_contra hcon
    rw [Filter.not_eventually] at hcon
    set b' := (F g r P0 + b) / 2 with hb'
    have hS : IsClosed ({q : Δ d × Δ d | relEntropy q.1 q.2 ≤ (r : EReal)} ∩
        {q : Δ d × Δ d | b' ≤ ∑ i, (q.2 : Fin d → ℝ) i * g i}) :=
      (isClosed_relEntropy_le r).inter (isClosed_le continuous_const (hlinc.comp continuous_snd))
    have hproj := isClosedMap_fst_of_compactSpace _ hS
    have hfreq : ∃ᶠ Q in 𝓝 P0, Q ∈ Prod.fst '' ({q : Δ d × Δ d | relEntropy q.1 q.2 ≤ (r : EReal)} ∩
        {q : Δ d × Δ d | b' ≤ ∑ i, (q.2 : Fin d → ℝ) i * g i}) := by
      refine hcon.mono (fun Q hQ => ?_)
      have hQ' : b' < F g r Q := by
        have := not_lt.mp hQ
        rw [hb']; linarith
      obtain ⟨y, ⟨P, hP, rfl⟩, hy⟩ := exists_lt_of_lt_csSup (F_ne g r hr Q) hQ'
      exact ⟨(Q, P), ⟨hP, hy.le⟩, rfl⟩
    have hmem := hproj.closure_subset (mem_closure_iff_frequently.2 hfreq)
    obtain ⟨⟨Q, P⟩, ⟨hP, hbP⟩, hQ⟩ := hmem
    simp only at hQ
    subst hQ
    have := le_F g r Q P hP
    have hbP' : b' ≤ ∑ i, (P : Fin d → ℝ) i * g i := hbP
    rw [hb'] at hbP'
    linarith

lemma drPredictor_eq {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ) (r : ℝ)
    (x : ↥X) (P' : Δ d) : drPredictor γ r x P' = F (γ x) r P' := rfl

lemma isPredictor_dr {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ)
    (hγ : ∀ i, Continuous (fun x : ↥X => γ x i)) (r : ℝ) (hr : 0 ≤ r) :
    IsPredictor (drPredictor γ r) := by
  unfold IsPredictor
  refine continuous_iff_continuousAt.2 (fun q0 => ?_)
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have h1 : Tendsto (fun q : ↥X × Δ d => ∑ i, |γ q.1 i - γ q0.1 i|) (𝓝 q0) (𝓝 0) := by
    have hc : Continuous (fun q : ↥X × Δ d => ∑ i, |γ q.1 i - γ q0.1 i|) :=
      continuous_finsetSum _ (fun i _ => (((hγ i).comp continuous_fst).sub continuous_const).abs)
    simpa using hc.tendsto q0
  have h2 : Tendsto (fun q : ↥X × Δ d => dist (F (γ q0.1) r q.2) (F (γ q0.1) r q0.2))
      (𝓝 q0) (𝓝 0) := by
    have := ((F_continuous (γ q0.1) r hr).tendsto q0.2).comp (continuous_snd.tendsto q0)
    exact tendsto_iff_dist_tendsto_zero.1 this
  refine squeeze_zero (fun q => dist_nonneg) (fun q => ?_) (by simpa using h1.add h2)
  show dist (drPredictor γ r q.1 q.2) (drPredictor γ r q0.1 q0.2) ≤
    ∑ i, |γ q.1 i - γ q0.1 i| + dist (F (γ q0.1) r q.2) (F (γ q0.1) r q0.2)
  rw [drPredictor_eq, drPredictor_eq, Real.dist_eq, Real.dist_eq]
  have e1 := F_le_F_add (γ q.1) (γ q0.1) r hr q.2
  have e2 := F_le_F_add (γ q0.1) (γ q.1) r hr q.2
  have e3 : ∑ i, |γ q0.1 i - γ q.1 i| = ∑ i, |γ q.1 i - γ q0.1 i| :=
    Finset.sum_congr rfl (fun i _ => abs_sub_comm _ _)
  rw [e3] at e2
  have h4 : |F (γ q.1) r q.2 - F (γ q0.1) r q.2| ≤ ∑ i, |γ q.1 i - γ q0.1 i| :=
    abs_sub_le_iff.2 ⟨by linarith, by linarith⟩
  have h5 := abs_sub_le (F (γ q.1) r q.2) (F (γ q0.1) r q.2) (F (γ q0.1) r q0.2)
  linarith

/-! Method of types. -/

lemma sum_comp_count {d T : ℕ} (ω : Fin T → Fin d) (h : Fin d → ℝ) :
    ∑ t, h (ω t) = ∑ i, ((Finset.univ.filter (fun t => ω t = i)).card : ℝ) * h i := by
  rw [← Finset.sum_fiberwise Finset.univ ω (fun t => h (ω t))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : ∀ t ∈ Finset.univ.filter (fun t => ω t = i), h (ω t) = h i :=
    fun t ht => by rw [(Finset.mem_filter.1 ht).2]
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul]

lemma emp_nonneg {d T : ℕ} (ω : Fin T → Fin d) (i : Fin d) : 0 ≤ empiricalVec ω i := by
  unfold empiricalVec; positivity

lemma emp_pos {d T : ℕ} (ω : Fin T → Fin d) (t : Fin T) : 0 < empiricalVec ω (ω t) := by
  unfold empiricalVec
  have hT : 0 < T := t.pos
  have hc : 0 < (Finset.univ.filter (fun s => ω s = ω t)).card :=
    Finset.card_pos.2 ⟨t, by simp⟩
  exact div_pos (by exact_mod_cast hc) (by exact_mod_cast hT)

lemma emp_sum_one {d T : ℕ} (hT : 0 < T) (ω : Fin T → Fin d) : ∑ i, empiricalVec ω i = 1 := by
  have h := sum_comp_count ω (fun _ => (1:ℝ))
  simp only [mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  unfold empiricalVec
  rw [← Finset.sum_div, ← h]
  exact div_self (by exact_mod_cast hT.ne')

def countVec {d T : ℕ} (ω : Fin T → Fin d) : Fin d → Fin (T + 1) := fun i =>
  ⟨(Finset.univ.filter (fun t => ω t = i)).card,
    Nat.lt_succ_of_le ((Finset.card_filter_le _ _).trans (by simp))⟩

lemma emp_eq_of_count {d T : ℕ} (ω ω0 : Fin T → Fin d) (h : countVec ω = countVec ω0) :
    empiricalVec ω = empiricalVec ω0 := by
  funext i
  have hi : ((countVec ω i : Fin (T + 1)) : ℕ) = ((countVec ω0 i : Fin (T + 1)) : ℕ) := by rw [h]
  simp only [countVec] at hi
  unfold empiricalVec
  rw [hi]

lemma sum_prod_emp_le {d T : ℕ} (hT : 0 < T) :
    ∑ ω : Fin T → Fin d, ∏ t, empiricalVec ω (ω t) ≤ ((T : ℝ) + 1) ^ d := by
  rw [← Finset.sum_fiberwise Finset.univ countVec (fun ω => ∏ t, empiricalVec ω (ω t))]
  have hb : ∀ k : Fin d → Fin (T + 1),
      ∑ ω ∈ Finset.univ.filter (fun ω => countVec ω = k), ∏ t, empiricalVec ω (ω t) ≤ 1 := by
    intro k
    by_cases hk : ∃ ω0, countVec ω0 = k
    · obtain ⟨ω0, rfl⟩ := hk
      calc ∑ ω ∈ Finset.univ.filter (fun ω => countVec ω = countVec ω0), ∏ t, empiricalVec ω (ω t)
          = ∑ ω ∈ Finset.univ.filter (fun ω => countVec ω = countVec ω0),
              ∏ t, empiricalVec ω0 (ω t) :=
            Finset.sum_congr rfl (fun ω hω => by
              rw [emp_eq_of_count ω ω0 (Finset.mem_filter.1 hω).2])
        _ ≤ ∑ ω : Fin T → Fin d, ∏ t, empiricalVec ω0 (ω t) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun ω _ _ => Finset.prod_nonneg (fun t _ => emp_nonneg ω0 _))
        _ = ∏ _t : Fin T, ∑ i, empiricalVec ω0 i :=
            (Fintype.prod_sum (fun (_ : Fin T) (j : Fin d) => empiricalVec ω0 j)).symm
        _ = 1 := by rw [emp_sum_one hT ω0]; simp
    · have he : Finset.univ.filter (fun ω => countVec ω = k) = ∅ := by
        ext ω
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact fun h => hk ⟨ω, h⟩
      rw [he, Finset.sum_empty]
      exact zero_le_one
  calc _ ≤ ∑ _k : Fin d → Fin (T + 1), (1:ℝ) := Finset.sum_le_sum (fun k _ => hb k)
    _ = ((T : ℝ) + 1) ^ d := by simp

lemma prod_le_of_rel {d T : ℕ} (P : Δ d) (r : ℝ) (hT : 0 < T) (ω : Fin T → Fin d)
    (hmem : empiricalVec ω ∈ stdSimplex ℝ (Fin d))
    (hrel : (r : EReal) < relEntropy ⟨empiricalVec ω, hmem⟩ P) :
    ∏ t, (P : Fin d → ℝ) (ω t) ≤ Real.exp (-(r * T)) * ∏ t, empiricalVec ω (ω t) := by
  have hQnn : 0 ≤ ∏ t, empiricalVec ω (ω t) :=
    Finset.prod_nonneg (fun t _ => emp_nonneg ω _)
  unfold relEntropy at hrel
  split_ifs at hrel with hs
  · have hR : r < ∑ i, empiricalVec ω i * Real.log (empiricalVec ω i / (P : Fin d → ℝ) i) := by
      exact_mod_cast hrel
    have hPpos : ∀ t, 0 < (P : Fin d → ℝ) (ω t) := fun t =>
      lt_of_le_of_ne (nn P _) (fun e => (emp_pos ω t).ne' (hs _ e.symm))
    have hfac : ∀ t, (P : Fin d → ℝ) (ω t) = empiricalVec ω (ω t) *
        Real.exp (Real.log ((P : Fin d → ℝ) (ω t)) - Real.log (empiricalVec ω (ω t))) := by
      intro t
      rw [Real.exp_sub, Real.exp_log (hPpos t), Real.exp_log (emp_pos ω t)]
      field_simp [(emp_pos ω t).ne']
    have hTpos : (0:ℝ) < T := by exact_mod_cast hT
    have hT' : (T:ℝ) ≠ 0 := hTpos.ne'
    have key : ∑ t, (Real.log ((P : Fin d → ℝ) (ω t)) - Real.log (empiricalVec ω (ω t)))
        ≤ -(r * T) := by
      have hsc := sum_comp_count ω
        (fun i => Real.log ((P : Fin d → ℝ) i) - Real.log (empiricalVec ω i))
      rw [hsc]
      have hterm : ∀ i, ((Finset.univ.filter (fun t => ω t = i)).card : ℝ) *
          (Real.log ((P : Fin d → ℝ) i) - Real.log (empiricalVec ω i)) =
          -(T * (empiricalVec ω i * Real.log (empiricalVec ω i / (P : Fin d → ℝ) i))) := by
        intro i
        have hcnt : ((Finset.univ.filter (fun t => ω t = i)).card : ℝ) = T * empiricalVec ω i := by
          unfold empiricalVec; rw [mul_comm, div_mul_cancel₀ _ hT']
        rw [hcnt]
        by_cases hq : empiricalVec ω i = 0
        · rw [hq]; simp
        · have hp : (P : Fin d → ℝ) i ≠ 0 := fun e => hq (hs i e)
          rw [mul_log_div_eq _ _ hp]; ring
      rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_neg_distrib, ← Finset.mul_sum]
      nlinarith
    rw [Finset.prod_congr rfl (fun t _ => hfac t), Finset.prod_mul_distrib, ← Real.exp_sum,
      mul_comm (Real.exp (-(r * T)))]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 key) hQnn
  · simp only [not_forall] at hs
    obtain ⟨i, hPi, hQi⟩ := hs
    have hne : (Finset.univ.filter (fun t => ω t = i)).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      apply hQi
      show empiricalVec ω i = 0
      unfold empiricalVec
      rw [he]
      simp
    obtain ⟨t, ht⟩ := hne
    have hz : ∏ s, (P : Fin d → ℝ) (ω s) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ t) (by rw [(Finset.mem_filter.1 ht).2]; exact hPi)
    rw [hz]
    exact mul_nonneg (Real.exp_pos _).le hQnn

lemma empProb_le {d : ℕ} (P : Δ d) (r : ℝ) (T : ℕ) (hT : 0 < T) :
    empProb P T {Q | (r : EReal) < relEntropy Q P} ≤ Real.exp (-(r * T)) * ((T : ℝ) + 1) ^ d := by
  unfold empProb pathProb
  calc _ ≤ ∑ ω : Fin T → Fin d, Real.exp (-(r * T)) * ∏ t, empiricalVec ω (ω t) := by
        refine Finset.sum_le_sum (fun ω _ => ?_)
        split_ifs with hE
        · obtain ⟨hmem, hrel⟩ := hE
          exact prod_le_of_rel P r hT ω hmem hrel
        · exact mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun t _ => emp_nonneg ω _))
    _ = Real.exp (-(r * T)) * ∑ ω : Fin T → Fin d, ∏ t, empiricalVec ω (ω t) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_prod_emp_le hT) (Real.exp_pos _).le

lemma rate_of_bound {d : ℕ} (p : ℕ → ℝ) (r : ℝ)
    (hp : ∀ T : ℕ, 0 < T → p T ≤ Real.exp (-(r * T)) * ((T : ℝ) + 1) ^ d) : RateLE p r := by
  intro r' hr'
  set b := (r - r') / 2 with hb
  have hbpos : 0 < b := by rw [hb]; linarith
  have ho := (isLittleO_pow_exp_pos_mul_atTop d hbpos).bound one_pos
  have ht : Tendsto (fun T : ℕ => (T : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually ho, eventually_ge_atTop 1] with T hT hT1
  have hT0 : 0 < T := hT1
  have hT1' : (1:ℝ) ≤ T := by exact_mod_cast hT1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_pos (Real.exp_pos _), one_mul] at hT
  have h2 : Real.exp (b * ((T : ℝ) + 1)) ≤ Real.exp (2 * b * T) := Real.exp_le_exp.2 (by nlinarith)
  calc p T ≤ Real.exp (-(r * T)) * ((T : ℝ) + 1) ^ d := hp T hT0
    _ ≤ Real.exp (-(r * T)) * Real.exp (2 * b * T) :=
        mul_le_mul_of_nonneg_left (hT.trans h2) (Real.exp_pos _).le
    _ = Real.exp (-(r' * T)) := by rw [← Real.exp_add]; congr 1; rw [hb]; ring

lemma disappoint_sub {n d : ℕ} {X : Set (EuclideanSpace ℝ (Fin n))} (γ : ↥X → Fin d → ℝ) (r : ℝ)
    (xr : Δ d → ↥X) (P : Δ d) :
    DROOptimal.Prescriptor.disappointSet γ (drPredictor γ r) xr P ⊆
      {Q | (r : EReal) < relEntropy Q P} := by
  intro Q hQ
  simp only [DROOptimal.Prescriptor.disappointSet, Set.mem_setOf_eq] at hQ ⊢
  by_contra hle
  rw [not_lt] at hle
  have := le_F (γ (xr Q)) r Q P hle
  exact absurd hQ (not_lt.2 this)

end DRO6Aux

open DROOptimal.Prescriptor in
theorem solution {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 ≤ r) (xr : DROOptimal.Predictor.Δ d → ↥X) (hxr_qc : QuasiContinuous xr)
    (hxr : IsArgminSelector (DROOptimal.Predictor.drPredictor γ r) xr) :
    Feasible6 γ r (DROOptimal.Predictor.drPredictor γ r) xr := by
  refine ⟨⟨DRO6Aux.isPredictor_dr γ hγ r hr, hxr_qc, hxr⟩, fun P => ?_⟩
  refine DRO6Aux.rate_of_bound (d := d) _ r (fun T hT => ?_)
  exact (DRO6Aux.empProb_mono P T (DRO6Aux.disappoint_sub γ r xr P)).trans
    (DRO6Aux.empProb_le P r T hT)
