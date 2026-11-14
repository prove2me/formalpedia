-- Prove2me | solution 1 for BCFGJPSSV26.Stable.KSData.card_good
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-13T18:09:37.299193+00:00
-- url     : https://prove2.me/submissions/39aa7443-c1b2-42e7-9eca-8840a80ef252

module

public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingStep
public import Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingDensity
import all Definitions.Def_BCFGJPSSV26_Stable_Alg_ClusterSamplingDensity
public import Theorems.Thm_BCFGJPSSV26_Stable_KSData_Base_sum_wt_le

set_option maxSynthPendingDepth 3



@[expose] public section

namespace BCFGJPSSV26.Stable

open Finset

namespace KSData

variable (K : KSData)

open Classical in
/-- **Density of the sampling step.** -/
theorem card_good_tag1 {ph j : ℕ} {del : List ℕ} {D : List DumQ} {l : ℕ} {r₀ : ℚ}
    (hI : K.Inv (ph, j, del, D, 1, l, r₀)) (hph : ph ≠ 2) :
    K.X.P.q₂ * (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) ≤
      ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
        K.Good (ph, j, del, D, 1, l, r₀) u).card := by
  have hph2 : ph < 2 := lt_of_le_of_ne hI.phase_le hph
  have hb : K.Base del D := hI.base
  have hg : K.GamSub del D := hI.gam (by simp)
  have hns : ¬ K.cc ph del D := hI.sample hph2 rfl
  have hD : (toRaw K.X.I).ValidDums D := fun d hd ↦ by
    obtain ⟨i, hi, he⟩ := (hI.leaders d hd).resolve_right fun h ↦ absurd h.1 (by simp)
    have := (hb.del_sub i hi).1
    rw [he, Raw.n_toRaw, Raw.m_toRaw]
    omega
  have hopt : 0 < K.X.opt := K.H.opt_pos
  have he := K.H.eps_pos
  have hcc : K.X.ε ^ 3 * K.X.opt ≤ ∑ c ∈ K.GoodL ph del D, K.wt ph del D c := by
    unfold cc at hns
    exact not_lt.1 hns
  have hpos : 0 < ∑ c ∈ K.GoodL ph del D, K.wt ph del D c :=
    lt_of_lt_of_le (by positivity) hcc
  have hne : K.cand del ≠ [] := by
    intro hc
    have he : K.LSp del = ∅ := by
      ext c
      rw [LSp, hc]
      simp [Instance.centers]
    exact hns (K.cc_of_empty (subset_empty.1 (he ▸ K.GoodL_subset hg)))
  have hA : ∀ c ∈ K.GoodL ph del D, c.1 ∈ K.cand del := fun c hc ↦
    Instance.mem_centers.1 (K.GoodL_subset hg hc)
  have h := card_sample_ge (b := K.X.b) (K.cand_nodup del) (fun i hi ↦ K.cand_lt hi)
    (K.wq ph del D) (K.wt ph del D) (fun c _ ↦ K.wq_eq hD hne c)
    (fun c _ ↦ K.wt_nonneg ph del D c) (K.GoodL ph del D) hA hpos
  rw [← K.ksWeights_eq] at h
  have hW : ∑ c ∈ (univ.filter fun c : Fin K.X.I.m ↦ c.1 ∈ K.cand del), K.wt ph del D c ≤
      6 * K.X.opt := hb.sum_wt_le hD hg ph
  have hWpos : 0 < ∑ c ∈ (univ.filter fun c : Fin K.X.I.m ↦ c.1 ∈ K.cand del),
      K.wt ph del D c :=
    lt_of_lt_of_le hpos (sum_le_sum_of_subset_of_nonneg (fun c hc ↦ mem_filter.2
      ⟨mem_univ _, hA c hc⟩) fun c _ _ ↦ K.wt_nonneg ph del D c)
  -- the good centers are at most `m`
  have hAcard : ((K.GoodL ph del D).card : ℝ) ≤ K.X.I.m := by
    have h1 : (K.GoodL ph del D).card ≤ K.X.S.card :=
      card_le_card ((K.GoodL_subset hg).trans (K.LSp_subset del))
    have h2 : K.X.S.card ≤ K.X.I.m := K.H.alo.1 ▸ K.H.k_le_m
    exact_mod_cast h1.trans h2
  -- the sampled center is good
  have hsub : ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦
      ∃ c ∈ K.GoodL ph del D, c.1 = (K.cand del).getD (wsample K.X.b
        (ksWeights (toRaw K.X.I) K.LS K.Λ₁ ph del D (K.cand del)) u.1) 0) ⊆
      (univ.filter fun u ↦ K.Good (ph, j, del, D, 1, l, r₀) u) := by
    intro u hu
    rw [mem_filter] at hu ⊢
    obtain ⟨c, hc, hce⟩ := hu.2
    refine ⟨mem_univ _, (K.good_tag1 hph).2 ?_⟩
    change K.fac ((K.cand del).getD (wsample K.X.b (ksWeights (toRaw K.X.I) K.LS K.Λ₁ ph del D
      (K.cand del)) u.1) 0) ∈ _
    rw [← hce, K.fac_fin]
    exact hc
  refine le_trans ?_ (le_trans h (by exact_mod_cast card_le_card hsub))
  -- arithmetic: `2^b ε³/6 - m ≥ 2^b ε³/12 = q₂ 2^b`
  rw [K.card_fin_b]
  set W := ∑ c ∈ (univ.filter fun c : Fin K.X.I.m ↦ c.1 ∈ K.cand del), K.wt ph del D c
  set A := ∑ c ∈ K.GoodL ph del D, K.wt ph del D c
  have hK : (12 : ℝ) * (K.X.P.N : ℝ) ^ 3 * K.X.I.m ≤ 2 ^ K.X.b := by
    exact_mod_cast K.twoPow_b_ge
  have hN := K.N_pos'
  have heps : K.X.ε = 1 / (K.X.P.N : ℝ) := rfl
  have hK0 : (0 : ℝ) < 2 ^ K.X.b := by positivity
  have h1 : (2 : ℝ) ^ K.X.b * (K.X.ε ^ 3 / 6) ≤ 2 ^ K.X.b * A / W := by
    rw [le_div_iff₀ hWpos]
    have : K.X.ε ^ 3 / 6 * W ≤ A := by
      have : K.X.ε ^ 3 / 6 * W ≤ K.X.ε ^ 3 / 6 * (6 * K.X.opt) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
      linarith
    nlinarith
  have h2 : (K.X.I.m : ℝ) ≤ 2 ^ K.X.b * (K.X.ε ^ 3 / 12) := by
    rw [heps]
    have : (2 : ℝ) ^ K.X.b * ((1 / (K.X.P.N : ℝ)) ^ 3 / 12) =
        2 ^ K.X.b / (12 * (K.X.P.N : ℝ) ^ 3) := by
      field_simp
    rw [this, le_div_iff₀ (by positivity)]
    linarith
  rw [q₂_eq]
  have h3 : 1 / (12 * (K.X.P.N : ℝ) ^ 3) * 2 ^ K.X.b = 2 ^ K.X.b * (K.X.ε ^ 3 / 12) := by
    rw [heps]
    field_simp
  rw [h3]
  linarith

open Classical in
/-- **Density**: from every invariant state, at least `q₂ 2^b` chunks are good. -/
theorem card_good {st : KSState} (hI : K.Inv st) :
    K.X.P.q₂ * (Fintype.card (Fin (2 ^ K.X.b)) : ℝ) ≤
      ((univ : Finset (Fin (2 ^ K.X.b))).filter fun u : Fin (2 ^ K.X.b) ↦ K.Good st u).card := by
  obtain ⟨ph, j, del, D, tag, l, r₀⟩ := st
  by_cases hph : ph = 2
  · refine K.card_all _ fun u ↦ ?_
    rw [Good, KSState.phase_mk, if_pos hph]
    trivial
  have ht : tag ≤ 5 := hI.tag_le
  interval_cases tag
  · by_cases hjs : j = K.X.s
    · exact K.card_all _ fun u ↦ (K.good_tag0 hph).2 (.inl hjs)
    · exact le_trans (K.card_bit_iff (K.cc ph del D))
        (K.card_mono (Q := fun u ↦ K.Good (ph, j, del, D, 0, l, r₀) u)
          fun u hu ↦ (K.good_tag0 hph).2 (.inr hu))
  · exact K.card_good_tag1 hI hph
  · exact le_trans (K.card_bit_iff (K.fac l ∉ K.X.GamOf (K.OB D)))
      (K.card_mono (Q := fun u ↦ K.Good (ph, j, del, D, 2, l, r₀) u)
        fun u hu ↦ (K.good_tag2 hph).2 hu)
  · exact le_trans (K.card_bit_iff (∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c ∧
        K.X.ε ^ 2 * K.X.per c ≤ ((toRaw K.X.I).fdist (K.X.I.n + l) (K.nearOther del l) : ℝ)))
      (K.card_mono (Q := fun u ↦ K.Good (ph, j, del, D, 3, l, r₀) u)
        fun u hu ↦ (K.good_tag3 hph).2 hu)
  · exact K.card_good_tag4 hI hph
  · exact le_trans (K.card_bit_iff (¬ ∃ c ∈ K.OB D, K.fac l ∈ K.X.GamE c))
      (K.card_mono (Q := fun u ↦ K.Good (ph, j, del, D, 5, l, r₀) u)
        fun u hu ↦ (K.good_tag5 hph).2 hu)

end KSData

end BCFGJPSSV26.Stable

end

public section

theorem solution : type_of% @BCFGJPSSV26.Stable.KSData.card_good := @BCFGJPSSV26.Stable.KSData.card_good
