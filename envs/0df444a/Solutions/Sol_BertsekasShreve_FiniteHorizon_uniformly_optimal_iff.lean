-- Prove2me | solution 1 for BertsekasShreve.FiniteHorizon.uniformly_optimal_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T22:21:18.512375+00:00
-- url     : https://prove2.me/submissions/9dbc7854-4b42-4347-8de3-4b12818df930

import Mathlib
import Definitions.Def_BertsekasShreve_FiniteHorizon_Model
import Definitions.Def_BertsekasShreve_FiniteHorizon_Problem



namespace BertsekasShreve.FiniteHorizon

open Model

namespace UOAux

variable {S C : Type*} (m : Model S C)

theorem comp_succ (π : m.Policy) (n : ℕ) (J : S → EReal) :
    m.comp π (n + 1) J = m.Tmu (π 0) (m.comp (π.shift 1) n J) := by
  induction n generalizing J with
  | zero => rfl
  | succ n ih =>
    show m.comp π (n + 1) (m.Tmu (π (n + 1)) J) = _
    rw [ih]
    show _ = m.Tmu (π 0) (m.comp (π.shift 1) n (m.Tmu (π.shift 1 n) J))
    simp only [Policy.shift, Nat.add_comm 1 n]

theorem shift_shift (π : m.Policy) (i j : ℕ) : (π.shift i).shift j = π.shift (i + j) := by
  funext k; simp [Policy.shift, Nat.add_assoc]

theorem costN_shift_succ (J₀ : S → EReal) (π : m.Policy) (i n : ℕ) :
    m.costN J₀ (n + 1) (π.shift i) = m.Tmu (π i) (m.costN J₀ n (π.shift (i + 1))) := by
  unfold costN; rw [comp_succ, shift_shift]; rfl

theorem Tmu_mono (μ : m.Selector) {J J' : S → EReal} (h : J ≤ J') : m.Tmu μ J ≤ m.Tmu μ J' :=
  fun x => m.mono x _ (μ.2 x) J J' h

theorem T_le_Tmu (μ : m.Selector) (J : S → EReal) : m.T J ≤ m.Tmu μ J :=
  fun x => biInf_le (fun u => m.H x u J) (μ.2 x)

theorem T_mono {J J' : S → EReal} (h : J ≤ J') : m.T J ≤ m.T J' := by
  intro x
  exact iInf₂_mono fun u hu => m.mono x u hu J J' h

theorem iterT_le_comp (π : m.Policy) (n : ℕ) (J : S → EReal) : m.T^[n] J ≤ m.comp π n J := by
  induction n generalizing π with
  | zero => exact le_rfl
  | succ n ih =>
    rw [comp_succ, Function.iterate_succ_apply']
    exact (T_mono m (ih _)).trans (T_le_Tmu m _ _)

theorem iterT_le_optCostN (J₀ : S → EReal) (n : ℕ) : m.T^[n] J₀ ≤ m.optCostN J₀ n :=
  fun x => le_iInf fun π => iterT_le_comp m π n J₀ x

/-- a selector taking value `u` at `x`. -/
noncomputable def selAt (x : S) (u : C) (hu : u ∈ m.U x) : m.Selector := by
  classical
  exact ⟨fun y => if y = x then u else (m.U_nonempty y).some, fun y => by
    by_cases h : y = x
    · subst h; simpa using hu
    · simpa [h] using (m.U_nonempty y).some_mem⟩

theorem selAt_apply (x : S) (u : C) (hu : u ∈ m.U x) : (selAt m x u hu).1 x = u := by
  simp [selAt]

def cons (μ : m.Selector) (π : m.Policy) : m.Policy := fun n => Nat.casesOn n μ fun k => π k

theorem optCostN_succ_le_T_costN (J₀ : S → EReal) (n : ℕ) (π : m.Policy) :
    m.optCostN J₀ (n + 1) ≤ m.T (m.costN J₀ n π) := by
  intro x
  refine le_iInf₂ fun u hu => ?_
  have h1 : m.optCostN J₀ (n + 1) x ≤ m.costN J₀ (n + 1) (cons m (selAt m x u hu) π) x :=
    iInf_le _ _
  have h2 : m.costN J₀ (n + 1) (cons m (selAt m x u hu) π) =
      m.Tmu (selAt m x u hu) (m.costN J₀ n π) := by
    have hs : (cons m (selAt m x u hu) π).shift 1 = π := by
      funext k; simp [Policy.shift, cons, Nat.add_comm 1 k]
    unfold costN; rw [comp_succ, hs]; rfl
  rw [h2] at h1
  simpa [Tmu, selAt_apply] using h1

theorem iterT_eq_of_attained (J₀ : S → EReal) (N : ℕ) (π : m.Policy)
    (h : ∀ k, k < N → m.Tmu (π k) (m.T^[N - k - 1] J₀) = m.T^[N - k] J₀) :
    ∀ j, j ≤ N → m.costN J₀ j (π.shift (N - j)) = m.T^[j] J₀ := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ j ih =>
    intro hj
    rw [costN_shift_succ, show N - (j + 1) + 1 = N - j by omega, ih (by omega)]
    have := h (N - (j + 1)) (by omega)
    rwa [show N - (N - (j + 1)) - 1 = j by omega, show N - (N - (j + 1)) = j + 1 by omega] at this

theorem uo_iff_core (J₀ : S → EReal) (N : ℕ) (π : m.Policy) :
    m.IsUniformlyNStageOptimal J₀ N π ↔
      ∀ k, k < N → m.Tmu (π k) (m.T^[N - k - 1] J₀) = m.T^[N - k] J₀ := by
  constructor
  · intro hU
    -- show by induction on j ≤ N that costN j (shift (N-j)) = T^j J₀
    have key : ∀ j, j ≤ N → m.costN J₀ j (π.shift (N - j)) = m.T^[j] J₀ := by
      intro j
      induction j with
      | zero => intro _; rfl
      | succ j ih =>
        intro hj
        have hopt := hU (N - (j + 1)) (by omega)
        rw [show N - (N - (j + 1)) = j + 1 by omega] at hopt
        have e1 : m.costN J₀ (j + 1) (π.shift (N - (j + 1))) =
            m.Tmu (π (N - (j + 1))) (m.T^[j] J₀) := by
          rw [costN_shift_succ, show N - (j + 1) + 1 = N - j by omega, ih (by omega)]
        apply le_antisymm
        · calc m.costN J₀ (j + 1) (π.shift (N - (j + 1))) = m.optCostN J₀ (j + 1) := hopt
            _ ≤ m.T (m.costN J₀ j (π.shift (N - j))) := optCostN_succ_le_T_costN m J₀ j _
            _ = m.T^[j + 1] J₀ := by rw [ih (by omega), Function.iterate_succ_apply']
        · rw [e1, Function.iterate_succ_apply']; exact T_le_Tmu m _ _
    intro k hk
    have e := key (N - k) (by omega)
    rw [show N - (N - k) = k by omega, show N - k = (N - k - 1) + 1 by omega,
      costN_shift_succ, show k + 1 = N - (N - k - 1) by omega, key _ (by omega)] at e
    rw [show N - k = (N - k - 1) + 1 by omega]
    exact e
  · intro h i hi
    have e := iterT_eq_of_attained m J₀ N π h (N - i) (by omega)
    rw [show N - (N - i) = i by omega] at e
    unfold IsNStageOptimal
    rw [e]
    apply le_antisymm (iterT_le_optCostN m J₀ _)
    intro x
    exact (iInf_le _ (π.shift i)).trans (le_of_eq (congrFun e x))

theorem exists_uo_iff_core (J₀ : S → EReal) (N : ℕ) :
    ((∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π) ↔
      ∀ x, ∀ k, k < N → ∃ u ∈ m.U x, m.H x u (m.T^[k] J₀) = m.T^[k + 1] J₀ x) ∧
    ((∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π) →
      m.optCostN J₀ N = m.T^[N] J₀) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨π, hπ⟩ x k hk
    have := ((uo_iff_core m J₀ N π).1 hπ) (N - 1 - k) (by omega)
    rw [show N - (N - 1 - k) - 1 = k by omega, show N - (N - 1 - k) = k + 1 by omega] at this
    exact ⟨(π (N - 1 - k)).1 x, (π (N - 1 - k)).2 x, congrFun this x⟩
  · intro h
    classical
    have hsel : ∀ k, ∃ μ : m.Selector, k < N → m.Tmu μ (m.T^[k] J₀) = m.T^[k + 1] J₀ := by
      intro k
      by_cases hk : k < N
      · choose u hu heq using fun x => h x k hk
        exact ⟨⟨u, hu⟩, fun _ => funext heq⟩
      · exact ⟨⟨fun y => (m.U_nonempty y).some, fun y => (m.U_nonempty y).some_mem⟩,
          fun h' => absurd h' hk⟩
    choose μ hμ using hsel
    refine ⟨fun i => μ (N - 1 - i), (uo_iff_core m J₀ N _).2 fun k hk => ?_⟩
    have := hμ (N - 1 - k) (by omega)
    rw [show N - 1 - k = N - k - 1 by omega, show N - k - 1 + 1 = N - k by omega] at this
    simpa [show N - 1 - k = N - k - 1 by omega] using this
  · rintro ⟨π, hπ⟩
    have e := iterT_eq_of_attained m J₀ N π ((uo_iff_core m J₀ N π).1 hπ) N le_rfl
    apply le_antisymm _ (iterT_le_optCostN m J₀ _)
    intro x
    exact (iInf_le _ (π.shift (N - N))).trans (le_of_eq (congrFun e x))

end UOAux

theorem uniformly_optimal_iff_core {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) (π : m.Policy) :
    m.IsUniformlyNStageOptimal J₀ N π ↔
      ∀ k, k < N → m.Tmu (π k) (m.T^[N - k - 1] J₀) = m.T^[N - k] J₀ :=
  UOAux.uo_iff_core m J₀ N π

theorem exists_uniformly_optimal_iff_attained_core {S C : Type*} (m : Model S C)
    (J₀ : S → EReal) (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) :
    ((∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π) ↔
      ∀ x, ∀ k, k < N → ∃ u ∈ m.U x, m.H x u (m.T^[k] J₀) = m.T^[k + 1] J₀ x) ∧
    ((∃ π : m.Policy, m.IsUniformlyNStageOptimal J₀ N π) →
      m.optCostN J₀ N = m.T^[N] J₀) :=
  UOAux.exists_uo_iff_core m J₀ N

end BertsekasShreve.FiniteHorizon

open BertsekasShreve.FiniteHorizon
open Model

theorem solution {S C : Type*} (m : Model S C) (J₀ : S → EReal)
    (hJ₀ : ∀ x, J₀ x ≠ ⊥) (N : ℕ) (hN : 1 ≤ N) (π : m.Policy) :
    m.IsUniformlyNStageOptimal J₀ N π ↔
      ∀ k, k < N → m.Tmu (π k) (m.T^[N - k - 1] J₀) = m.T^[N - k] J₀ := by
  exact uniformly_optimal_iff_core m J₀ hJ₀ N hN π
