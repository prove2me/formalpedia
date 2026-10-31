-- Prove2me | solution 1 for FairRentFPTAS.Approx.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-30T12:31:02.165562+00:00
-- url     : https://prove2.me/submissions/71c6cf0a-cc3a-44c9-87a9-a2b6aebc0676

import Mathlib
import Definitions.Def_FairRentFPTAS_Approx_Model

open FairRentFPTAS.Approx

namespace FRFL3Aux

/-- `drop` vanishes at a point below every start of a sorted list. -/
lemma drop_eq_zero (x : ℝ) : ∀ (l : List (ℝ × ℝ)), (l.map Prod.fst).Pairwise (· < ·) →
    (∀ e ∈ l, x ≤ e.1) → PLFun.drop l x = 0 := by
  intro l
  induction l with
  | nil => intro _ _; simp [PLFun.drop]
  | cons e t ih =>
    intro hs hx
    cases t with
    | nil =>
      have := hx e (by simp)
      simp [PLFun.drop, max_eq_right this]
    | cons e' t' =>
      have hs' : ((e' :: t').map Prod.fst).Pairwise (· < ·) := (List.pairwise_cons.mp hs).2
      have hee' : e.1 < e'.1 := (List.pairwise_cons.mp hs).1 e'.1 (by simp)
      have := hx e (by simp)
      simp only [PLFun.drop]
      rw [ih hs' (fun y hy => hx y (List.mem_cons_of_mem _ hy)), max_eq_right this,
        min_eq_left hee'.le]
      ring

lemma starts_nonneg (f : PLFun) (hf : f.WF) : ∀ e ∈ f.pieces, 0 ≤ e.1 := by
  obtain ⟨hne, hhead, hsort, _⟩ := hf
  cases h : f.pieces with
  | nil => exact absurd h hne
  | cons e t =>
    rw [h] at hhead hsort
    simp at hhead
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · rw [hhead]
    · have := (List.pairwise_cons.mp (by simpa using hsort)).1 y.1 (List.mem_map_of_mem hy)
      rw [hhead] at this; exact this.le

lemma eval_zero (f : PLFun) (hf : f.WF) : f.eval 0 = f.base := by
  unfold PLFun.eval
  simp only [lt_irrefl, if_false]
  rw [drop_eq_zero 0 _ hf.2.2.1 (starts_nonneg f hf)]; ring

lemma firstSlope_pos (f : PLFun) (hf : f.WF) : 0 < f.firstSlope := by
  unfold PLFun.firstSlope
  cases h : f.pieces with
  | nil => exact absurd h hf.1
  | cons e t =>
    simp only [List.headD_cons]
    exact hf.2.2.2 e (by rw [h]; simp)

lemma M_pos {n : ℕ} (hn : 1 ≤ n) (J : Instance n) (hJ : Standing J) (M : ℝ)
    (hM : IsThreshold J M) : 0 < M := by
  have a0 : Fin n := ⟨0, by omega⟩
  have h := hM a0 a0 a0
  rw [eval_zero _ (hJ a0 a0)] at h
  by_contra hle
  push_neg at hle
  rcases hle.lt_or_eq with hlt | heq
  · unfold PLFun.eval at h
    rw [if_pos hlt] at h
    have := firstSlope_pos _ (hJ a0 a0)
    nlinarith
  · subst heq
    rw [eval_zero _ (hJ a0 a0)] at h
    exact lt_irrefl _ h

lemma drop_continuous : ∀ l : List (ℝ × ℝ), Continuous (fun x => PLFun.drop l x) := by
  intro l
  induction l with
  | nil => simp only [PLFun.drop]; exact continuous_const
  | cons e t ih =>
    cases t with
    | nil =>
      simp only [PLFun.drop]
      fun_prop
    | cons e' t' =>
      simp only [PLFun.drop]
      have : Continuous fun x : ℝ => e.2 * (min (max x e.1) e'.1 - e.1) := by fun_prop
      exact this.add ih

lemma isClosed_L {n : ℕ} (L : WithBot ℝ) (r : Fin n) :
    IsClosed {x : Fin n → ℝ | L ≤ ((x r : ℝ) : WithBot ℝ)} := by
  cases L with
  | bot => simp
  | coe l =>
    simp only [WithBot.coe_le_coe]
    exact isClosed_le continuous_const (continuous_apply r)

lemma isClosed_U {n : ℕ} (U : WithTop ℝ) (r : Fin n) :
    IsClosed {x : Fin n → ℝ | ((x r : ℝ) : WithTop ℝ) ≤ U} := by
  cases U with
  | top => simp
  | coe u =>
    simp only [WithTop.coe_le_coe]
    exact isClosed_le (continuous_apply r) continuous_const

/-- existence of an LP optimum once a feasible point exists. -/
lemma lp_opt_exists {n : ℕ} (J : Instance n) (L : Fin n → WithBot ℝ) (U : Fin n → WithTop ℝ)
    (σ : Equiv.Perm (Fin n)) (x0 : Fin n → ℝ) (h0 : LPFeasible J L U σ x0) :
    ∃ x, IsLPOpt J L U σ x := by
  classical
  set K := ∑ r, x0 r
  let G : Set (Fin n → ℝ) := {x | (∀ r, L r ≤ ((x r : ℝ) : WithBot ℝ)) ∧
    (∀ r, ((x r : ℝ) : WithTop ℝ) ≤ U r) ∧
    (∀ a r, (J.v a r).base - PLFun.drop (J.v a r).pieces (x r) ≤
      (J.v a (σ a)).base - PLFun.drop (J.v a (σ a)).pieces (x (σ a))) ∧ ∀ r, 0 ≤ x r}
  have hFG : ∀ x, LPFeasible J L U σ x ↔ x ∈ G := by
    intro x
    unfold LPFeasible IsEF
    simp only [G, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, ?_, h4⟩
      intro a r
      have := h3 a r
      unfold PLFun.eval at this
      rwa [if_neg (not_lt.mpr (h4 r)), if_neg (not_lt.mpr (h4 (σ a)))] at this
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨h1, h2, ?_, h4⟩
      intro a r
      have := h3 a r
      unfold PLFun.eval
      rwa [if_neg (not_lt.mpr (h4 r)), if_neg (not_lt.mpr (h4 (σ a)))]
  have hGc : IsClosed G := by
    have e : G = (⋂ r, {x : Fin n → ℝ | L r ≤ ((x r : ℝ) : WithBot ℝ)}) ∩
        ((⋂ r, {x : Fin n → ℝ | ((x r : ℝ) : WithTop ℝ) ≤ U r}) ∩
        ((⋂ a, ⋂ r, {x : Fin n → ℝ | (J.v a r).base - PLFun.drop (J.v a r).pieces (x r) ≤
          (J.v a (σ a)).base - PLFun.drop (J.v a (σ a)).pieces (x (σ a))}) ∩
        (⋂ r, {x : Fin n → ℝ | 0 ≤ x r}))) := by
      ext x; simp [G]
    rw [e]
    refine (isClosed_iInter fun r => isClosed_L _ r).inter
      ((isClosed_iInter fun r => isClosed_U _ r).inter
        ((isClosed_iInter fun a => isClosed_iInter fun r => ?_).inter
          (isClosed_iInter fun r => isClosed_le continuous_const (continuous_apply r))))
    apply isClosed_le
    · exact continuous_const.sub ((drop_continuous _).comp (continuous_apply r))
    · exact continuous_const.sub ((drop_continuous _).comp (continuous_apply (σ a)))
  let C : Set (Fin n → ℝ) := G ∩ {x | ∑ r, x r ≤ K}
  have hCc : IsClosed C := hGc.inter (isClosed_le (continuous_finset_sum _
    (fun r _ => continuous_apply r)) continuous_const)
  have hCsub : C ⊆ Set.pi Set.univ (fun _ => Set.Icc 0 K) := by
    intro x hx r _
    obtain ⟨hxG, hxK⟩ := hx
    have hnn := hxG.2.2.2
    refine ⟨hnn r, le_trans ?_ hxK⟩
    exact Finset.single_le_sum (f := x) (fun r _ => hnn r) (Finset.mem_univ r)
  have hCcomp : IsCompact C :=
    IsCompact.of_isClosed_subset (isCompact_univ_pi (fun _ => isCompact_Icc)) hCc hCsub
  have hCne : C.Nonempty := ⟨x0, (hFG x0).mp h0, show ∑ r, x0 r ≤ K from le_rfl⟩
  obtain ⟨xs, hxs, hmin⟩ := hCcomp.exists_isMinOn hCne
    (continuous_finset_sum _ (fun r _ => continuous_apply r)).continuousOn
  refine ⟨xs, (hFG xs).mpr hxs.1, ?_⟩
  intro y hy
  by_cases hyK : ∑ r, y r ≤ K
  · exact hmin ⟨(hFG y).mp hy, hyK⟩
  · push_neg at hyK
    exact le_trans hxs.2 hyK.le

end FRFL3Aux

open FRFL3Aux in
theorem solution {n : ℕ} (J : Instance n) (M : ℝ) (hJ : Standing J) (hM : IsThreshold J M)
    (T : ℕ) (π : ℕ → Equiv.Perm (Fin n)) (p : ℕ → Fin n → ℝ) (hrun : IsRun J M T π p) :
    ∀ i ≤ T, IsEF (hatInst M J) (π i) (p i) ∧
      (∃ σ, IsMaxWeightPM (hatInst M J) (p i) σ) ∧
      ∀ σ, IsMaxWeightPM (hatInst M J) (p i) σ →
        ∃ q, IsLPOpt (hatInst M J) (domL (hatInst M J) (p i)) (domU (hatInst M J) (p i)) σ q := by
  classical
  intro i hiT
  set Ĵ := hatInst M J
  obtain ⟨hEF0, hM0', hstep⟩ := hrun
  -- envy-freeness and nonnegativity of the iterate
  have hEFnn : IsEF Ĵ (π i) (p i) ∧ ∀ r, 0 ≤ p i r := by
    cases i with
    | zero =>
      refine ⟨hEF0, fun r => ?_⟩
      have hn : 1 ≤ n := by have := r.2; omega
      exact le_trans (M_pos hn J hJ M hM).le (hM0' r)
    | succ k =>
      obtain ⟨_, _, ⟨⟨_, _, hEF, hnn⟩, _⟩⟩ := hstep k (by omega)
      exact ⟨hEF, hnn⟩
  obtain ⟨hEF, hnn⟩ := hEFnn
  refine ⟨hEF, ?_, ?_⟩
  · -- a maximum-weight perfect matching of first-choice edges exists
    set S := (Finset.univ : Finset (Equiv.Perm (Fin n))).filter
      (fun τ => ∀ a, FirstChoice Ĵ (p i) a (τ a))
    have hS : (π i) ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      intro a r'
      exact hEF a r'
    obtain ⟨σ, hσS, hσmax⟩ := Finset.exists_max_image S (fun τ => weight Ĵ (p i) τ) ⟨_, hS⟩
    refine ⟨σ, (Finset.mem_filter.mp hσS).2, ?_⟩
    intro τ hτ
    exact hσmax τ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩)
  · intro σ hσ
    apply lp_opt_exists Ĵ _ _ σ (p i)
    refine ⟨?_, ?_, ?_, hnn⟩
    · intro r
      unfold domL
      apply Finset.max_le
      intro b hb
      exact WithBot.coe_le_coe.mpr (Finset.mem_filter.mp hb).2.le
    · intro r
      unfold domU
      apply Finset.le_min
      intro b hb
      exact WithTop.coe_le_coe.mpr (Finset.mem_filter.mp hb).2
    · intro a r
      exact hσ.1 a r
