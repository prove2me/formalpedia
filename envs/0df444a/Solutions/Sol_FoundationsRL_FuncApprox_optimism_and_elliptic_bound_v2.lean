-- Prove2me | solution 1 for FoundationsRL.FuncApprox.optimism_and_elliptic_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-16T00:14:24.065574+00:00
-- url     : https://prove2.me/submissions/b5b868a0-eda1-473d-b842-be5f4a16dd0d

import Mathlib
import Definitions.Def_FoundationsRL_RLBasics_Core
import Definitions.Def_FoundationsRL_RLBasics_UCBVI
import Definitions.Def_FoundationsRL_FuncApprox_Core
import Definitions.Def_FoundationsRL_FuncApprox_BiLinUCB

set_option autoImplicit false

namespace FoundationsRL.FuncApprox

open FoundationsRL.RLBasics

theorem ca4_greedy_max
    {S A : Type} [Fintype S] [Fintype A] [Nonempty A]
    {Qc : Type} [Fintype Qc] [Nonempty Qc]
    (qeval : Qc → ℕ → S → A → ℝ) (Qf : Qc) (h : ℕ) (s : S) (a : A) :
    qeval Qf h s a ≤ qeval Qf h s (greedyPolicy qeval Qf h s) := by
  unfold greedyPolicy
  have hne : (Finset.univ : Finset A).toList.argmax (qeval Qf h s) ≠ none := by
    intro hn
    rw [List.argmax_eq_none] at hn
    have : a ∈ (Finset.univ : Finset A).toList := by simp
    rw [hn] at this
    simp at this
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hne
  rw [hm]
  simp only [Option.getD_some]
  exact List.le_of_mem_argmax (by simp) hm

theorem ca4_best_spec
    {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    {H : ℕ} (M : EpisodicMDP S A H) {Qc : Type} [Fintype Qc] [Nonempty Qc]
    (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
    (hist : List (Trajectory S A H)) (n : ℕ) (β : ℝ) (k : ℕ)
    (hq0mem : q0 ∈ confSet M qeval hist n β k) :
    bestQ M qeval hist n β k ∈ confSet M qeval hist n β k ∧
      ∀ Q ∈ confSet M qeval hist n β k,
        initValue M qeval Q ≤ initValue M qeval (bestQ M qeval hist n β k) := by
  have hne : (confSet M qeval hist n β k).toList.argmax (initValue M qeval) ≠ none := by
    intro hn
    rw [List.argmax_eq_none] at hn
    have : q0 ∈ (confSet M qeval hist n β k).toList := by simpa using hq0mem
    rw [hn] at this
    simp at this
  obtain ⟨m, hm⟩ := Option.ne_none_iff_exists'.mp hne
  have hb : bestQ M qeval hist n β k = m := by
    unfold bestQ
    rw [hm]; rfl
  rw [hb]
  refine ⟨?_, ?_⟩
  · have := List.argmax_mem hm
    simpa using this
  · intro Q hQ
    exact List.le_of_mem_argmax (by simpa using hQ) hm

theorem ca4_init_q0
    {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    {H : ℕ} (M : EpisodicMDP S A H) {Qc : Type} [Fintype Qc] [Nonempty Qc]
    (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
    (hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0) :
    initValue M qeval q0 = ∑ s : S, M.d1 s * Vstar M 0 s := by
  unfold initValue
  refine Finset.sum_congr rfl (fun s _ => ?_)
  congr 1
  by_cases hH : 0 < H
  · have hmax := ca4_greedy_max qeval q0 0 s
    rw [hq0] at hmax ⊢
    simp only [if_pos hH] at hmax ⊢
    unfold Vstar
    refine le_antisymm ?_ ?_
    · exact le_ciSup (Set.finite_range _).bddAbove _
    · exact ciSup_le (fun a => hmax a)
  · have h0 : H = 0 := by omega
    subst h0
    rw [hq0]
    simp [Vstar, Qstar, Q]

end FoundationsRL.FuncApprox

open FoundationsRL.RLBasics FoundationsRL.FuncApprox in
theorem solution
    {S A : Type} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] [DecidableEq A]
    {H : ℕ} (M : EpisodicMDP S A H) {Qc : Type} [Fintype Qc] [Nonempty Qc]
    (qeval : Qc → ℕ → S → A → ℝ) (q0 : Qc)
    (_hq0 : qeval q0 = fun h s a => if h < H then Qstar M h s a else 0)
    (d : ℕ) (X : Policy S A H → ℕ → Fin d → ℝ) (W : (ℕ → S → A → ℝ) → ℕ → Fin d → ℝ)
    (_hfact : ∀ π, IsPolicy H π → ∀ Qf : Qc, ∀ h : ℕ, h < H →
        bellmanResidual M π h (qeval Qf) = ∑ j : Fin d, X π h j * W (qeval Qf) h j)
    (hist : List (Trajectory S A H)) (n : ℕ) (β C : ℝ) (k : ℕ)
    (_hconf : ∀ Qf ∈ confSet M qeval hist n β k, ∀ h : Fin H,
        ∑ i ∈ Finset.range k,
          (bellmanResidual M (iterPolicy M qeval hist n β i) h.1 (qeval Qf)) ^ 2 ≤ C * β)
    (_hq0mem : q0 ∈ confSet M qeval hist n β k) :
    (∀ Qf ∈ confSet M qeval hist n β k, ∀ h : Fin H,
        elliptNormSq
          ((List.range k).map (fun i => X (iterPolicy M qeval hist n β i) h.1))
          (W (qeval Qf) h.1) ≤ C * β)
    ∧ initValue M qeval (bestQ M qeval hist n β k) ≥ ∑ s : S, M.d1 s * Vstar M 0 s := by
  refine ⟨?_, ?_⟩
  · intro Qf hQ h
    have hpol : ∀ i, IsPolicy H (iterPolicy M qeval hist n β i) := by
      intro i h' _ s
      unfold iterPolicy detPolicy
      refine ⟨fun a => by split_ifs <;> norm_num, ?_⟩
      simp
    have heq : elliptNormSq
          ((List.range k).map (fun i => X (iterPolicy M qeval hist n β i) h.1))
          (W (qeval Qf) h.1) =
        ∑ i ∈ Finset.range k,
          (bellmanResidual M (iterPolicy M qeval hist n β i) h.1 (qeval Qf)) ^ 2 := by
      unfold elliptNormSq
      have hl : ∀ g : ℕ → ℝ, ((List.range k).map g).sum = ∑ i ∈ Finset.range k, g i :=
        fun g => rfl
      rw [List.map_map, hl]
      refine Finset.sum_congr rfl (fun i hi => ?_)
      have hi' : i < k := Finset.mem_range.mp hi
      simp only [Function.comp]
      rw [_hfact _ (hpol i) Qf h.1 h.2]
    rw [heq]
    exact _hconf Qf hQ h
  · obtain ⟨_, hmax⟩ := ca4_best_spec M qeval q0 hist n β k _hq0mem
    rw [← ca4_init_q0 M qeval q0 _hq0]
    exact hmax q0 _hq0mem

