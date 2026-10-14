-- Prove2me | solution 1 for BertsekasShreve.Generalized.prop6_3a_uniform_optimal_iff_attained
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:50:35.974921+00:00
-- url     : https://prove2.me/submissions/ce06139f-8e6f-49ee-b5d6-f38fdd73cddf

import Mathlib
import Definitions.Def_BertsekasShreve_Generalized_Model
import Definitions.Def_BertsekasShreve_Generalized_Assumptions
import Definitions.Def_BertsekasShreve_Generalized_Optimality



namespace BertsekasShreve.Generalized

open Filter Topology

namespace P63Aux

variable {S C : Type*} (P : Model S C)

theorem comp_succ (π : P.Policy) (n : ℕ) (J : S → EReal) :
    P.comp π (n + 1) J = P.Tmu (π 0).1 (P.comp (P.shift π 1) n J) := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
    show P.comp π (n + 1) (P.Tmu (π (n + 1)).1 J) = _
    rw [ih]
    show _ = P.Tmu (π 0).1 (P.comp (P.shift π 1) n (P.Tmu (P.shift π 1 n).1 J))
    simp only [Model.shift, Nat.add_comm 1 n]

theorem shift_shift (π : P.Policy) (i j : ℕ) : P.shift (P.shift π i) j = P.shift π (i + j) := by
  funext k; simp [Model.shift, Nat.add_assoc]

theorem JN_shift_succ (π : P.Policy) (i n : ℕ) :
    P.JN (n + 1) (P.shift π i) = P.Tmu (π i).1 (P.JN n (P.shift π (i + 1))) := by
  unfold Model.JN; rw [comp_succ, shift_shift]; rfl

theorem comp_mem (hA3 : P.A3) (π : P.Policy) (n : ℕ) (J : S → EReal) (hJ : J ∈ P.Ftil) :
    P.comp π n J ∈ P.Ftil := by
  induction n generalizing π with
  | zero => exact hJ
  | succ n ih =>
    rw [comp_succ]
    exact ((hA3 _ (ih _)).1 _ (π 0).2)

theorem JN_mem (hA3 : P.A3) (π : P.Policy) (n : ℕ) : P.JN n π ∈ P.Ftil :=
  comp_mem P hA3 π n P.J0 (P.Fstar_subset P.J0_mem)

theorem iterT_mem (hA2 : P.A2) (n : ℕ) : P.T^[n] P.J0 ∈ P.Fstar := by
  induction n with
  | zero => exact P.J0_mem
  | succ n ih => rw [Function.iterate_succ_apply']; exact (hA2 _ ih).1

theorem Tmu_mono (μ : P.Sel) {J J' : S → EReal} (hJ : J ∈ P.Ftil) (hJ' : J' ∈ P.Ftil)
    (h : J ≤ J') : P.Tmu μ.1 J ≤ P.Tmu μ.1 J' :=
  fun x => P.mono x _ (P.Mtil_subset _ μ.2 x) J hJ J' hJ' h

theorem T_le_Tmu (μ : P.Sel) (J : S → EReal) : P.T J ≤ P.Tmu μ.1 J :=
  fun x => biInf_le (fun u => P.H x u J) (P.Mtil_subset _ μ.2 x)

theorem T_mono {J J' : S → EReal} (hJ : J ∈ P.Ftil) (hJ' : J' ∈ P.Ftil) (h : J ≤ J') :
    P.T J ≤ P.T J' := by
  intro x
  exact iInf₂_mono fun u hu => P.mono x u hu J hJ J' hJ' h

theorem iterT_le_JN (hA2 : P.A2) (hA3 : P.A3) (π : P.Policy) (n : ℕ) :
    P.T^[n] P.J0 ≤ P.JN n π := by
  induction n generalizing π with
  | zero => exact le_rfl
  | succ n ih =>
    unfold Model.JN at *
    rw [comp_succ, Function.iterate_succ_apply']
    exact (T_mono P (P.Fstar_subset (iterT_mem P hA2 n)) (comp_mem P hA3 _ _ _
      (P.Fstar_subset P.J0_mem)) (ih _)).trans (T_le_Tmu P _ _)

theorem iterT_le_JNstar (hA2 : P.A2) (hA3 : P.A3) (n : ℕ) : P.T^[n] P.J0 ≤ P.JNstar n :=
  fun x => le_iInf fun π => iterT_le_JN P hA2 hA3 π n x

def cons (μ : P.Sel) (π : P.Policy) : P.Policy := fun n => Nat.casesOn n μ fun k => π k

theorem JNstar_succ_le_T_JN (hA1 : P.A1) (n : ℕ) (π : P.Policy) :
    P.JNstar (n + 1) ≤ P.T (P.JN n π) := by
  intro x
  refine le_iInf₂ fun u hu => ?_
  obtain ⟨μ, hμ, hμx⟩ := hA1 x u hu
  have h1 : P.JNstar (n + 1) x ≤ P.JN (n + 1) (cons P ⟨μ, hμ⟩ π) x :=
    iInf_le _ _
  have h2 : P.JN (n + 1) (cons P ⟨μ, hμ⟩ π) = P.Tmu μ (P.JN n π) := by
    have hs : P.shift (cons P ⟨μ, hμ⟩ π) 1 = π := by
      funext k; simp [Model.shift, cons, Nat.add_comm 1 k]
    unfold Model.JN; rw [comp_succ, hs]; rfl
  rw [h2] at h1
  simpa [Model.Tmu, hμx] using h1

theorem iterT_eq_of_attained (N : ℕ) (π : P.Policy)
    (h : ∀ k, k < N → P.Tmu (π k).1 (P.T^[N - k - 1] P.J0) = P.T^[N - k] P.J0) :
    ∀ j, j ≤ N → P.JN j (P.shift π (N - j)) = P.T^[j] P.J0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [JN_shift_succ, show N - (j + 1) + 1 = N - j by omega, ih (by omega)]
    have := h (N - (j + 1)) (by omega)
    rwa [show N - (N - (j + 1)) - 1 = j by omega, show N - (N - (j + 1)) = j + 1 by omega] at this

theorem uo_iff_core (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (N : ℕ) (π : P.Policy) :
    P.IsUniformlyNStageOptimal N π ↔
      ∀ k, k < N → P.Tmu (π k).1 (P.T^[N - k - 1] P.J0) = P.T^[N - k] P.J0 := by
  constructor
  · intro hU
    have key : ∀ j, j ≤ N → P.JN j (P.shift π (N - j)) = P.T^[j] P.J0 := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        have hopt := hU (N - (j + 1)) (by omega)
        rw [show N - (N - (j + 1)) = j + 1 by omega] at hopt
        have e1 : P.JN (j + 1) (P.shift π (N - (j + 1))) =
            P.Tmu (π (N - (j + 1))).1 (P.T^[j] P.J0) := by
          rw [JN_shift_succ, show N - (j + 1) + 1 = N - j by omega, ih (by omega)]
        apply le_antisymm
        · calc P.JN (j + 1) (P.shift π (N - (j + 1))) = P.JNstar (j + 1) := hopt
            _ ≤ P.T (P.JN j (P.shift π (N - j))) := JNstar_succ_le_T_JN P hA1 j _
            _ = P.T^[j + 1] P.J0 := by rw [ih (by omega), Function.iterate_succ_apply']
        · rw [e1, Function.iterate_succ_apply']; exact T_le_Tmu P _ _
    intro k hk
    have e := key (N - k) (by omega)
    rw [show N - (N - k) = k by omega, show N - k = (N - k - 1) + 1 by omega,
      JN_shift_succ, show k + 1 = N - (N - k - 1) by omega, key _ (by omega)] at e
    rw [show N - k = (N - k - 1) + 1 by omega]
    exact e
  · intro h i hi
    have e := iterT_eq_of_attained P N π h (N - i) (by omega)
    rw [show N - (N - i) = i by omega] at e
    unfold Model.IsNStageOptimal
    rw [e]
    apply le_antisymm (iterT_le_JNstar P hA2 hA3 _)
    intro x
    exact (iInf_le _ (P.shift π i)).trans (le_of_eq (congrFun e x))

end P63Aux

theorem p63a_core {S C : Type*} (P : Model S C)
    (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hES : P.ExactSelection)
    (N : ℕ) (hN : 0 < N) :
    (∃ π : P.Policy, P.IsUniformlyNStageOptimal N π) ↔
      ∀ x, ∀ k, k < N → ∃ u ∈ P.U x, P.H x u (P.T^[k] P.J0) = P.T^[k + 1] P.J0 x := by
  constructor
  · rintro ⟨π, hπ⟩ x k hk
    have := ((P63Aux.uo_iff_core P hA1 hA2 hA3 N π).1 hπ) (N - 1 - k) (by omega)
    rw [show N - (N - 1 - k) - 1 = k by omega, show N - (N - 1 - k) = k + 1 by omega] at this
    exact ⟨(π (N - 1 - k)).1 x, P.Mtil_subset _ (π (N - 1 - k)).2 x, congrFun this x⟩
  · intro h
    classical
    have hsel0 : ∀ k, k < N → ∃ μ : P.Sel, P.Tmu μ.1 (P.T^[k] P.J0) = P.T^[k + 1] P.J0 := by
      intro k hk
      obtain ⟨μ, hμ, he⟩ := hES _ (P63Aux.iterT_mem P hA2 k) (fun x => by
        obtain ⟨u, hu, hh⟩ := h x k hk
        refine ⟨u, hu, ?_⟩
        rw [hh, Function.iterate_succ_apply'])
      refine ⟨⟨μ, hμ⟩, ?_⟩
      rw [Function.iterate_succ_apply']; exact he
    obtain ⟨μ0, -⟩ := hsel0 0 hN
    have hsel : ∀ k, ∃ μ : P.Sel, k < N → P.Tmu μ.1 (P.T^[k] P.J0) = P.T^[k + 1] P.J0 := by
      intro k
      by_cases hk : k < N
      · obtain ⟨μ, hμ⟩ := hsel0 k hk
        exact ⟨μ, fun _ => hμ⟩
      · exact ⟨μ0, fun h' => absurd h' hk⟩
    choose μ hμ using hsel
    refine ⟨fun i => μ (N - 1 - i), (P63Aux.uo_iff_core P hA1 hA2 hA3 N _).2 fun k hk => ?_⟩
    have := hμ (N - 1 - k) (by omega)
    rw [show N - 1 - k = N - k - 1 by omega, show N - k - 1 + 1 = N - k by omega] at this
    simpa [show N - 1 - k = N - k - 1 by omega] using this

end BertsekasShreve.Generalized

open BertsekasShreve.Generalized


theorem solution {S C : Type*} (P : Model S C)
    (hA1 : P.A1) (hA2 : P.A2) (hA3 : P.A3) (hA4 : P.A4) (hES : P.ExactSelection)
    (N : ℕ) (hN : 0 < N) :
    (∃ π : P.Policy, P.IsUniformlyNStageOptimal N π) ↔
      ∀ x, ∀ k, k < N → ∃ u ∈ P.U x, P.H x u (P.T^[k] P.J0) = P.T^[k + 1] P.J0 x := by
  exact p63a_core P hA1 hA2 hA3 hA4 hES N hN
