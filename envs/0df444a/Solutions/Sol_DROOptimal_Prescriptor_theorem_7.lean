-- Prove2me | solution 1 for DROOptimal.Prescriptor.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T18:24:56.858007+00:00
-- url     : https://prove2.me/submissions/7b8a49f2-555a-4124-bce1-563dd3086024

import Mathlib
import Definitions.Def_DROOptimal_Predictor_Setting
import Definitions.Def_DROOptimal_Prescriptor_Pairs
import Theorems.Thm_DROOptimal_Prescriptor_theorem_6
import Theorems.Thm_DROOptimal_Predictor_theorem_1_lower

set_option autoImplicit false

open Filter Topology

namespace DRO7Aux

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

end DRO7Aux

open DROOptimal.Prescriptor in
theorem solution {n d : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX : IsCompact X)
    (γ : ↥X → Fin d → ℝ) (hγ : ∀ i, Continuous (fun x : ↥X => γ x i))
    (r : ℝ) (hr : 0 < r) (xr : DROOptimal.Predictor.Δ d → ↥X) (hxr_qc : QuasiContinuous xr)
    (hxr : IsArgminSelector (DROOptimal.Predictor.drPredictor γ r) xr) :
    StronglyOptimal6 γ r (DROOptimal.Predictor.drPredictor γ r) xr := by
  refine ⟨DROOptimal.Prescriptor.theorem_6 X hX γ hγ r hr.le xr hxr_qc hxr, ?_⟩
  intro chat xhat hfeas P0
  by_contra hlt
  push Not at hlt
  have hle : DROOptimal.Predictor.drPredictor γ r (xr P0) P0 ≤
      DROOptimal.Predictor.drPredictor γ r (xhat P0) P0 := hxr P0 (xhat P0)
  have hlt2 := lt_of_lt_of_le hlt hle
  unfold DROOptimal.Predictor.drPredictor at hlt2
  have hne : ((fun ℙ => DROOptimal.Predictor.cost γ (xhat P0) ℙ) ''
      {ℙ : DROOptimal.Predictor.Δ d | DROOptimal.Predictor.relEntropy P0 ℙ ≤ (r : EReal)}).Nonempty := by
    refine ⟨_, P0, ?_, rfl⟩
    show DROOptimal.Predictor.relEntropy P0 P0 ≤ (r : EReal)
    rw [DRO7Aux.relEntropy_self]
    exact_mod_cast hr.le
  obtain ⟨_, ⟨P1, hP1, rfl⟩, hc1⟩ := exists_lt_of_lt_csSup hne hlt2
  obtain ⟨Ps, hPs, hfP0, hcPs⟩ := DRO7Aux.exists_pos_model P0 P1 r hr hP1 (γ (xhat P0))
    (chat (xhat P0) P0) (by simpa only [DROOptimal.Predictor.cost] using hc1)
  have hfc := DRO7Aux.continuous_klsum Ps hPs
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m = ((∑ i, (P0 : Fin d → ℝ) i *
      Real.log ((P0 : Fin d → ℝ) i / (Ps : Fin d → ℝ) i)) + r) / 2 := ⟨_, rfl⟩
  have hgc : Continuous (fun q : ↥X × DROOptimal.Predictor.Δ d =>
      DROOptimal.Predictor.cost γ q.1 Ps - chat q.1 q.2) := by
    have h1 : Continuous (fun q : ↥X × DROOptimal.Predictor.Δ d =>
        DROOptimal.Predictor.cost γ q.1 Ps) := by
      unfold DROOptimal.Predictor.cost
      exact continuous_finsetSum _ (fun i _ => continuous_const.mul ((hγ i).comp continuous_fst))
    exact h1.sub hfeas.1.1
  have hW : {q : ↥X × DROOptimal.Predictor.Δ d |
      0 < DROOptimal.Predictor.cost γ q.1 Ps - chat q.1 q.2} ∈ 𝓝 (xhat P0, P0) := by
    refine (isOpen_lt continuous_const hgc).mem_nhds ?_
    show 0 < DROOptimal.Predictor.cost γ (xhat P0) Ps - chat (xhat P0) P0
    unfold DROOptimal.Predictor.cost
    linarith
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 hW
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
  have hU : v ∩ {Q : DROOptimal.Predictor.Δ d | (∑ i, (Q : Fin d → ℝ) i *
      Real.log ((Q : Fin d → ℝ) i / (Ps : Fin d → ℝ) i)) < m} ∈ 𝓝 P0 :=
    Filter.inter_mem hv ((isOpen_lt hfc continuous_const).mem_nhds (by
      show (∑ i, (P0 : Fin d → ℝ) i * Real.log ((P0 : Fin d → ℝ) i / (Ps : Fin d → ℝ) i)) < m
      linarith))
  obtain ⟨V, hVo, ⟨Q1, hQ1⟩, hVU, hVd⟩ := hfeas.1.2.1 P0 (ε / 2) (by positivity) _ hU
  have hVD : V ⊆ DROOptimal.Prescriptor.disappointSet γ chat xhat Ps := by
    intro Q hQ
    have hxQ : xhat Q ∈ u := by
      apply hball
      rw [Metric.mem_ball, dist_comm]
      linarith [hVd Q hQ]
    have hmem := huv (Set.mk_mem_prod hxQ (hVU hQ).1)
    have h' : 0 < DROOptimal.Predictor.cost γ (xhat Q) Ps - chat (xhat Q) Q := hmem
    show chat (xhat Q) Q < DROOptimal.Predictor.cost γ (xhat Q) Ps
    linarith
  have hQ1m : (∑ i, (Q1 : Fin d → ℝ) i * Real.log ((Q1 : Fin d → ℝ) i / (Ps : Fin d → ℝ) i)) < m :=
    (hVU hQ1).2
  have hinf : (⨅ Q ∈ interior V, DROOptimal.Predictor.relEntropy Q Ps) < ((m : ℝ) : EReal) := by
    rw [hVo.interior_eq]
    calc (⨅ Q ∈ V, DROOptimal.Predictor.relEntropy Q Ps)
        ≤ DROOptimal.Predictor.relEntropy Q1 Ps := iInf₂_le Q1 hQ1
      _ = (((∑ i, (Q1 : Fin d → ℝ) i * Real.log ((Q1 : Fin d → ℝ) i / (Ps : Fin d → ℝ) i)) : ℝ)
            : EReal) := DRO7Aux.relEntropy_of_pos Q1 Ps hPs
      _ < ((m : ℝ) : EReal) := by exact_mod_cast hQ1m
  have hlow := DROOptimal.Predictor.theorem_1_lower Ps hPs V hVo.measurableSet m hinf
  have hup := hfeas.2 Ps ((m + r) / 2) (by linarith)
  obtain ⟨T, hT1, hTl, hTu⟩ := ((Filter.eventually_ge_atTop 1).and (hlow.and hup)).exists
  have hmono := DRO7Aux.empProb_mono Ps T hVD
  have h := (hTl.trans hmono).trans hTu
  rw [Real.exp_le_exp] at h
  have hT : (1 : ℝ) ≤ T := by exact_mod_cast hT1
  nlinarith [mul_pos (by linarith : (0 : ℝ) < (m + r) / 2 - m) (by linarith : (0 : ℝ) < T)]
