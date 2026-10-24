-- Prove2me | solution 1 for DirectedSearch.Approx.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:24:28.319083+00:00
-- url     : https://prove2.me/submissions/778c9f83-2ab5-413d-ae8d-cb2de3894f08

import Mathlib
import Definitions.Def_DirectedSearch_Approx_Setting

set_option linter.unusedSectionVars false

namespace DSA49

open DirectedSearch.Approx

variable {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]

lemma sum_single (m : M) (hM : ∀ m' : M, m' = m) (g : M → ℝ) : ∑ m', g m' = g m := by
  rw [Finset.sum_eq_single m (fun b _ hb => absurd (hM b) hb)
    (fun h => absurd (Finset.mem_univ m) h)]

lemma lp_compact (mk : Market M W) : IsCompact {β : M → W → ℝ | LPFeasible mk β} := by
  set S : Set (M → W → ℝ) := {β | LPFeasible mk β} with hS
  have hcl : IsClosed S := by
    have : S = (⋂ m, ⋂ w, {β : M → W → ℝ | 0 ≤ β m w}) ∩
        ((⋂ m, {β : M → W → ℝ | ∑ w, β m w ≤ mk.αM m}) ∩
          (⋂ w, {β : M → W → ℝ | ∑ m, β m w ≤ mk.αW w})) := by
      ext β; simp [hS, LPFeasible]
    rw [this]
    refine (isClosed_iInter fun m => isClosed_iInter fun w => ?_).inter
      ((isClosed_iInter fun m => ?_).inter (isClosed_iInter fun w => ?_))
    · exact isClosed_le continuous_const ((continuous_apply w).comp (continuous_apply m))
    · exact isClosed_le (continuous_finset_sum _ fun w _ =>
        (continuous_apply w).comp (continuous_apply m)) continuous_const
    · exact isClosed_le (continuous_finset_sum _ fun m _ =>
        (continuous_apply w).comp (continuous_apply m)) continuous_const
  have hsub : S ⊆ Set.pi Set.univ (fun m => Set.pi Set.univ (fun _ : W => Set.Icc 0 (mk.αM m))) := by
    intro β hβ m _ w _
    refine ⟨hβ.1 m w, ?_⟩
    calc β m w ≤ ∑ w', β m w' :=
          Finset.single_le_sum (fun w' _ => hβ.1 m w') (Finset.mem_univ w)
      _ ≤ mk.αM m := hβ.2.1 m
  exact (isCompact_univ_pi fun m => isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset
      hcl hsub

lemma lpObj_cont (mk : Market M W) : Continuous (lpObj mk) := by
  unfold lpObj
  exact continuous_const.mul (continuous_finset_sum _ fun m _ => continuous_finset_sum _
    fun w _ => continuous_const.mul ((continuous_apply w).comp (continuous_apply m)))

end DSA49

open DirectedSearch.Approx DSA49 in
theorem solution {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (m : M) (hM : ∀ m' : M, m' = m) :
    ∃ βstar : M → W → ℝ, LPFeasible mk βstar ∧
      (∀ β, LPFeasible mk β → lpObj mk β ≤ lpObj mk βstar) ∧
      ∃ (n : ℕ) (ws : Fin n → W), Function.Injective ws ∧
        (∀ i j : Fin n, i ≤ j → rho mk m (ws j) ≤ rho mk m (ws i)) ∧
        (∀ i : Fin n, i.val + 1 < n → βstar m (ws i) = mk.αW (ws i)) ∧
        (∀ w, w ∉ Set.range ws → βstar m w = 0) := by
  -- sorted enumeration of `W` by decreasing `ρ`
  set N := Fintype.card W with hN
  set e0 : Fin N ≃ W := (Fintype.equivFin W).symm with he0
  set g : Fin N → ℝ := fun k => - rho mk m (e0 k) with hg
  set e : Fin N ≃ W := (Tuple.sort g).trans e0 with he
  have hanti : ∀ i j : Fin N, i ≤ j → rho mk m (e j) ≤ rho mk m (e i) := by
    intro i j hij
    have := Tuple.monotone_sort g hij
    simp only [Function.comp, hg] at this
    simp only [he, Equiv.trans_apply]
    linarith
  -- an LP optimum
  have hK := lp_compact mk
  have hne : {β : M → W → ℝ | LPFeasible mk β}.Nonempty :=
    ⟨0, fun m w => le_rfl, fun m => by simp [(hmk.alphaM_pos m).le],
      fun w => by simp [(hmk.alphaW_pos w).le]⟩
  obtain ⟨β1, hβ1, hmax1⟩ := hK.exists_isMaxOn hne (lpObj_cont mk).continuousOn
  set v := lpObj mk β1
  set S := {β : M → W → ℝ | LPFeasible mk β} ∩ {β | v ≤ lpObj mk β} with hS
  have hSc : IsCompact S := hK.inter_right (isClosed_le continuous_const (lpObj_cont mk))
  have hSne : S.Nonempty := ⟨β1, hβ1, show v ≤ lpObj mk β1 from le_rfl⟩
  -- among optima, maximise a strictly decreasing weighting of the sorted entries
  set Φ : (M → W → ℝ) → ℝ := fun β => ∑ k : Fin N, ((N : ℝ) - k) * β m (e k) with hΦ
  have hΦc : Continuous Φ := continuous_finset_sum _ fun k _ =>
    continuous_const.mul ((continuous_apply (e k)).comp (continuous_apply m))
  obtain ⟨β, ⟨hβF, hβv⟩, hβmax⟩ := hSc.exists_isMaxOn hSne hΦc.continuousOn
  have hopt : ∀ β', LPFeasible mk β' → lpObj mk β' ≤ lpObj mk β :=
    fun β' h => (hmax1 h).trans hβv
  have hβ0 : ∀ w, 0 ≤ β m w := fun w => hβF.1 m w
  have hβcol : ∀ w, β m w ≤ mk.αW w := fun w => by
    have := hβF.2.2 w; rwa [sum_single m hM (fun m' => β m' w)] at this
  -- exchange property
  have hexch : ∀ i j : Fin N, i < j → β m (e i) = mk.αW (e i) ∨ β m (e j) = 0 := by
    intro i j hij
    by_contra hcon
    push Not at hcon
    obtain ⟨h1, h2⟩ := hcon
    have hlt1 : β m (e i) < mk.αW (e i) := lt_of_le_of_ne (hβcol _) h1
    have hlt2 : 0 < β m (e j) := lt_of_le_of_ne (hβ0 _) (Ne.symm h2)
    have hneq : e i ≠ e j := fun h => (ne_of_lt hij) (e.injective h)
    set ε := min (mk.αW (e i) - β m (e i)) (β m (e j)) with hε
    have hε0 : 0 < ε := lt_min (by linarith) hlt2
    have hε1 : ε ≤ mk.αW (e i) - β m (e i) := min_le_left _ _
    have hε2 : ε ≤ β m (e j) := min_le_right _ _
    set dv : W → ℝ := fun w => (if w = e i then ε else 0) - (if w = e j then ε else 0) with hdv
    set β' : M → W → ℝ := fun m' w => β m' w + dv w with hβ'
    have hdvsum : ∑ w, dv w = 0 := by
      simp only [hdv, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        sub_self]
    have hdvi : dv (e i) = ε := by simp [hdv, hneq]
    have hdvj : dv (e j) = -ε := by simp [hdv, Ne.symm hneq]
    have hdvo : ∀ w, w ≠ e i → w ≠ e j → dv w = 0 := fun w h1 h2 => by simp [hdv, h1, h2]
    have hF' : LPFeasible mk β' := by
      refine ⟨fun m' w => ?_, fun m' => ?_, fun w => ?_⟩
      · rw [hM m']
        simp only [hβ']
        by_cases hw1 : w = e i
        · rw [hw1, hdvi]; linarith [hβ0 (e i)]
        · by_cases hw2 : w = e j
          · rw [hw2, hdvj]; linarith
          · rw [hdvo w hw1 hw2]; linarith [hβ0 w]
      · simp only [hβ']
        rw [Finset.sum_add_distrib, hdvsum, add_zero]; exact hβF.2.1 m'
      · simp only [hβ']
        rw [sum_single m hM (fun m' => β m' w + dv w)]
        by_cases hw1 : w = e i
        · rw [hw1, hdvi]; linarith
        · by_cases hw2 : w = e j
          · rw [hw2, hdvj]; linarith [hβcol (e j)]
          · rw [hdvo w hw1 hw2]; linarith [hβcol w]
    have hobj : lpObj mk β' = lpObj mk β + 2 * (ε * rho mk m (e i) - ε * rho mk m (e j)) := by
      unfold lpObj
      rw [sum_single m hM, sum_single m hM]
      simp only [hβ', mul_add, Finset.sum_add_distrib]
      have : ∑ w, rho mk m w * dv w = ε * rho mk m (e i) - ε * rho mk m (e j) := by
        simp only [hdv, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        ring
      rw [this]
    have hρij := hanti i j hij.le
    have hβ'S : β' ∈ S := ⟨hF', by
      show v ≤ lpObj mk β'
      have hv' : v ≤ lpObj mk β := hβv
      rw [hobj]
      have : 0 ≤ ε * rho mk m (e i) - ε * rho mk m (e j) := by nlinarith
      linarith⟩
    have hΦ' : Φ β' = Φ β + ε * ((N : ℝ) - i) - ε * ((N : ℝ) - j) := by
      simp only [hΦ, hβ', mul_add, Finset.sum_add_distrib]
      have : ∑ k : Fin N, ((N : ℝ) - k) * dv (e k) = ε * ((N : ℝ) - i) - ε * ((N : ℝ) - j) := by
        have hk : ∀ k : Fin N, dv (e k) = (if k = i then ε else 0) - (if k = j then ε else 0) := by
          intro k; simp only [hdv, e.injective.eq_iff]
        simp only [hk, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq',
          Finset.mem_univ, if_true]
        ring
      rw [this]; ring
    have := hβmax hβ'S
    change Φ β' ≤ Φ β at this
    rw [hΦ'] at this
    have hij' : (i : ℝ) < j := by exact_mod_cast hij
    nlinarith
  refine ⟨β, hβF, hopt, ?_⟩
  -- the greedy prefix
  set P := Finset.univ.filter (fun k : Fin N => 0 < β m (e k)) with hP
  by_cases hPe : P.Nonempty
  · set jm := P.max' hPe with hjm
    have hjmP : 0 < β m (e jm) := by
      exact (Finset.mem_filter.mp (P.max'_mem hPe)).2
    have hjmax : ∀ k : Fin N, 0 < β m (e k) → k ≤ jm := fun k hk =>
      P.le_max' k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩)
    refine ⟨jm.val + 1, fun i => e ⟨i.val, by omega⟩, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      have := e.injective hab
      ext; simpa using congrArg Fin.val this
    · intro i j hij
      exact hanti _ _ (by rw [Fin.le_def] at hij ⊢; exact hij)
    · intro i hi
      rcases hexch ⟨i.val, by omega⟩ jm (by rw [Fin.lt_def]; simp only; omega) with h | h
      · exact h
      · exact absurd h hjmP.ne'
    · intro w hw
      obtain ⟨k, rfl⟩ := e.surjective w
      by_contra hne
      have hpos : 0 < β m (e k) := lt_of_le_of_ne (hβ0 _) (Ne.symm hne)
      have hk := hjmax k hpos
      exact hw ⟨⟨k.val, by rw [Fin.le_def] at hk; omega⟩, rfl⟩
  · refine ⟨0, Fin.elim0, fun a => a.elim0, fun i => i.elim0, fun i => i.elim0, ?_⟩
    intro w _
    obtain ⟨k, rfl⟩ := e.surjective w
    by_contra hne
    have hpos : 0 < β m (e k) := lt_of_le_of_ne (hβ0 _) (Ne.symm hne)
    exact hPe ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpos⟩⟩
