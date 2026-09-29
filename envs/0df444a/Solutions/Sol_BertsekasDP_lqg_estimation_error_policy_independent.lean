-- Prove2me | solution 1 for BertsekasDP.lqg_estimation_error_policy_independent
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-08T04:03:28.761061+00:00
-- url     : https://prove2.me/submissions/db3758bb-e749-42cc-ad89-8acd0c306fcf

import Mathlib
import Definitions.Def_BertsekasLQGModel

open Matrix Finset

namespace LQGaux

variable {n m q : ℕ} {Ω₀ ΩW ΩV : Type} [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]

lemma append_singleton_inj {α : Type*} {L L' : List α} {a a' : α}
    (h : L ++ [a] = L' ++ [a']) : L = L' ∧ a = a' := by
  have h1 : (L ++ [a]).reverse = (L' ++ [a']).reverse := by rw [h]
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.cons.injEq] at h1
  refine ⟨?_, h1.1⟩
  simpa using congrArg List.reverse h1.2

section

variable (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV)

lemma traj_zero_fst (π : List (Fin q → ℝ) → Fin m → ℝ) (ω : BertsekasLQGSample M) :
    (BertsekasLQGTraj M π 0 ω).1 = M.x0 ω.1 := rfl

lemma traj_zero_snd (π : List (Fin q → ℝ) → Fin m → ℝ) (ω : BertsekasLQGSample M) :
    (BertsekasLQGTraj M π 0 ω).2 =
      [M.C 0 *ᵥ M.x0 ω.1 + (if h : 0 < M.N then M.v 0 (ω.2.2 ⟨0, h⟩) else 0)] := rfl

lemma traj_succ_fst (π : List (Fin q → ℝ) → Fin m → ℝ) (k : ℕ)
    (ω : BertsekasLQGSample M) :
    (BertsekasLQGTraj M π (k + 1) ω).1 =
      M.A k *ᵥ (BertsekasLQGTraj M π k ω).1 +
        M.B k *ᵥ π (BertsekasLQGTraj M π k ω).2 +
        (if h : k < M.N then M.w k (ω.2.1 ⟨k, h⟩) else 0) := rfl

lemma traj_succ_snd (π : List (Fin q → ℝ) → Fin m → ℝ) (k : ℕ)
    (ω : BertsekasLQGSample M) :
    (BertsekasLQGTraj M π (k + 1) ω).2 =
      (BertsekasLQGTraj M π k ω).2 ++
        [M.C (k + 1) *ᵥ (BertsekasLQGTraj M π (k + 1) ω).1 +
          (if h : k + 1 < M.N then M.v (k + 1) (ω.2.2 ⟨k + 1, h⟩) else 0)] := rfl

/-- The state offset produced by the controls, one stage at a time. -/
lemma offset_succ (π : List (Fin q → ℝ) → Fin m → ℝ) (k : ℕ)
    (ω : BertsekasLQGSample M) :
    (BertsekasLQGTraj M π (k + 1) ω).1 - (BertsekasLQGTraj M 0 (k + 1) ω).1 =
      M.A k *ᵥ ((BertsekasLQGTraj M π k ω).1 - (BertsekasLQGTraj M 0 k ω).1) +
        M.B k *ᵥ π (BertsekasLQGTraj M π k ω).2 := by
  rw [traj_succ_fst, traj_succ_fst, Matrix.mulVec_sub]
  simp only [Pi.zero_apply, Matrix.mulVec_zero]
  abel

/-- The heart of Lemma 5.2.1: the information vector under `π` and the information
vector under the zero policy determine each other, and on the event where the
zero-policy information agrees, the state offset agrees too. -/
lemma key (π : List (Fin q → ℝ) → Fin m → ℝ) :
    ∀ (k : ℕ) (ω ω' : BertsekasLQGSample M),
      ((BertsekasLQGTraj M 0 k ω).2 = (BertsekasLQGTraj M 0 k ω').2 →
          (BertsekasLQGTraj M π k ω).2 = (BertsekasLQGTraj M π k ω').2 ∧
          (BertsekasLQGTraj M π k ω).1 - (BertsekasLQGTraj M 0 k ω).1 =
            (BertsekasLQGTraj M π k ω').1 - (BertsekasLQGTraj M 0 k ω').1) ∧
      ((BertsekasLQGTraj M π k ω).2 = (BertsekasLQGTraj M π k ω').2 →
          (BertsekasLQGTraj M 0 k ω).2 = (BertsekasLQGTraj M 0 k ω').2) := by
  intro k
  induction k with
  | zero =>
      intro ω ω'
      rw [traj_zero_snd, traj_zero_snd, traj_zero_snd, traj_zero_snd,
        traj_zero_fst, traj_zero_fst, traj_zero_fst, traj_zero_fst]
      exact ⟨fun h => ⟨h, by rw [sub_self, sub_self]⟩, fun h => h⟩
  | succ k ih =>
      intro ω ω'
      constructor
      · intro h0
        rw [traj_succ_snd, traj_succ_snd] at h0
        obtain ⟨h0hist, h0z⟩ := append_singleton_inj h0
        obtain ⟨hπhist, hoff⟩ := (ih ω ω').1 h0hist
        have hoff' : (BertsekasLQGTraj M π (k + 1) ω).1 -
            (BertsekasLQGTraj M 0 (k + 1) ω).1 =
              (BertsekasLQGTraj M π (k + 1) ω').1 -
                (BertsekasLQGTraj M 0 (k + 1) ω').1 := by
          rw [offset_succ, offset_succ, hoff, hπhist]
        refine ⟨?_, hoff'⟩
        rw [traj_succ_snd, traj_succ_snd, hπhist]
        congr 1
        have hx : (BertsekasLQGTraj M π (k + 1) ω).1 =
            (BertsekasLQGTraj M 0 (k + 1) ω).1 +
              ((BertsekasLQGTraj M π (k + 1) ω).1 -
                (BertsekasLQGTraj M 0 (k + 1) ω).1) := by abel
        have hx' : (BertsekasLQGTraj M π (k + 1) ω').1 =
            (BertsekasLQGTraj M 0 (k + 1) ω').1 +
              ((BertsekasLQGTraj M π (k + 1) ω').1 -
                (BertsekasLQGTraj M 0 (k + 1) ω').1) := by abel
        rw [List.cons.injEq]
        refine ⟨?_, rfl⟩
        rw [hx, hx', Matrix.mulVec_add, Matrix.mulVec_add, hoff']
        have : M.C (k + 1) *ᵥ (BertsekasLQGTraj M 0 (k + 1) ω).1 +
              (if h : k + 1 < M.N then M.v (k + 1) (ω.2.2 ⟨k + 1, h⟩) else 0) =
            M.C (k + 1) *ᵥ (BertsekasLQGTraj M 0 (k + 1) ω').1 +
              (if h : k + 1 < M.N then M.v (k + 1) (ω'.2.2 ⟨k + 1, h⟩) else 0) := by
          exact h0z
        rw [show M.C (k + 1) *ᵥ (BertsekasLQGTraj M 0 (k + 1) ω).1 +
              M.C (k + 1) *ᵥ ((BertsekasLQGTraj M π (k + 1) ω').1 -
                (BertsekasLQGTraj M 0 (k + 1) ω').1) +
              (if h : k + 1 < M.N then M.v (k + 1) (ω.2.2 ⟨k + 1, h⟩) else 0)
            = (M.C (k + 1) *ᵥ (BertsekasLQGTraj M 0 (k + 1) ω).1 +
                (if h : k + 1 < M.N then M.v (k + 1) (ω.2.2 ⟨k + 1, h⟩) else 0)) +
              M.C (k + 1) *ᵥ ((BertsekasLQGTraj M π (k + 1) ω').1 -
                (BertsekasLQGTraj M 0 (k + 1) ω').1) from by abel,
          this]
        abel
      · intro hπ
        rw [traj_succ_snd, traj_succ_snd] at hπ
        obtain ⟨hπhist, hπz⟩ := append_singleton_inj hπ
        have h0hist := (ih ω ω').2 hπhist
        obtain ⟨_, hoff⟩ := (ih ω ω').1 h0hist
        have hoff' : (BertsekasLQGTraj M π (k + 1) ω).1 -
            (BertsekasLQGTraj M 0 (k + 1) ω).1 =
              (BertsekasLQGTraj M π (k + 1) ω').1 -
                (BertsekasLQGTraj M 0 (k + 1) ω').1 := by
          rw [offset_succ, offset_succ, hoff, hπhist]
        rw [traj_succ_snd, traj_succ_snd, h0hist]
        congr 1
        rw [List.cons.injEq]
        refine ⟨?_, rfl⟩
        have hz : M.C (k + 1) *ᵥ (BertsekasLQGTraj M π (k + 1) ω).1 +
              (if h : k + 1 < M.N then M.v (k + 1) (ω.2.2 ⟨k + 1, h⟩) else 0) =
            M.C (k + 1) *ᵥ (BertsekasLQGTraj M π (k + 1) ω').1 +
              (if h : k + 1 < M.N then M.v (k + 1) (ω'.2.2 ⟨k + 1, h⟩) else 0) := hπz
        have e1 : (BertsekasLQGTraj M π (k + 1) ω).1 =
            (BertsekasLQGTraj M 0 (k + 1) ω).1 +
              ((BertsekasLQGTraj M π (k + 1) ω').1 -
                (BertsekasLQGTraj M 0 (k + 1) ω').1) := by
          rw [← hoff']; abel
        have e2 : (BertsekasLQGTraj M π (k + 1) ω').1 =
            (BertsekasLQGTraj M 0 (k + 1) ω').1 +
              ((BertsekasLQGTraj M π (k + 1) ω').1 -
                (BertsekasLQGTraj M 0 (k + 1) ω').1) := by abel
        have h1 : (BertsekasLQGTraj M 0 (k + 1) ω).1 - (BertsekasLQGTraj M 0 (k + 1) ω').1
            = (BertsekasLQGTraj M π (k + 1) ω).1 - (BertsekasLQGTraj M π (k + 1) ω').1 := by
          have h := sub_eq_sub_iff_sub_eq_sub.mp hoff'
          exact h.symm
        have h2 : M.C (k + 1) *ᵥ (BertsekasLQGTraj M 0 (k + 1) ω).1
              - M.C (k + 1) *ᵥ (BertsekasLQGTraj M 0 (k + 1) ω').1
            = M.C (k + 1) *ᵥ (BertsekasLQGTraj M π (k + 1) ω).1
              - M.C (k + 1) *ᵥ (BertsekasLQGTraj M π (k + 1) ω').1 := by
          rw [← Matrix.mulVec_sub, ← Matrix.mulVec_sub, h1]
        have key2 :
            (M.C (k + 1) *ᵥ (BertsekasLQGTraj M 0 (k + 1) ω).1 +
                (if h : k + 1 < M.N then M.v (k + 1) (ω.2.2 ⟨k + 1, h⟩) else 0))
              - (M.C (k + 1) *ᵥ (BertsekasLQGTraj M 0 (k + 1) ω').1 +
                (if h : k + 1 < M.N then M.v (k + 1) (ω'.2.2 ⟨k + 1, h⟩) else 0))
            = (M.C (k + 1) *ᵥ (BertsekasLQGTraj M π (k + 1) ω).1 +
                (if h : k + 1 < M.N then M.v (k + 1) (ω.2.2 ⟨k + 1, h⟩) else 0))
              - (M.C (k + 1) *ᵥ (BertsekasLQGTraj M π (k + 1) ω').1 +
                (if h : k + 1 < M.N then M.v (k + 1) (ω'.2.2 ⟨k + 1, h⟩) else 0)) := by
          rw [show ∀ x y u v : Fin q → ℝ, (x + u) - (y + v) = (x - y) + (u - v) from
            fun x y u v => by abel, show ∀ x y u v : Fin q → ℝ,
            (x + u) - (y + v) = (x - y) + (u - v) from fun x y u v => by abel, h2]
        rw [hz, sub_self] at key2
        exact sub_eq_zero.mp key2

end

end LQGaux

namespace LQGaux

open Classical in
lemma condexp_shift {Ω : Type} [Fintype Ω] {d : ℕ} (p : Ω → ℝ) (E E' : Ω → Prop)
    (X Y : Ω → Fin d → ℝ) (c : Fin d → ℝ)
    (hEE : ∀ a, E a ↔ E' a)
    (hXY : ∀ a, E a → X a = Y a + c)
    (hne : ∑ a ∈ Finset.univ.filter E, p a ≠ 0) :
    BertsekasCondExpVec p E X = BertsekasCondExpVec p E' Y + c := by
  unfold BertsekasCondExpVec
  have hset : (Finset.univ.filter E) = (Finset.univ.filter E') :=
    Finset.filter_congr fun x _ => hEE x
  rw [← hset]
  have h1 : ∑ a ∈ Finset.univ.filter E, p a • X a
      = (∑ a ∈ Finset.univ.filter E, p a • Y a)
        + (∑ a ∈ Finset.univ.filter E, p a) • c := by
    rw [Finset.sum_smul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [hXY a (Finset.mem_filter.mp ha).2, smul_add]
  rw [h1, smul_add, smul_smul, inv_mul_cancel₀ hne, one_smul]

variable {n m q : ℕ} {Ω₀ ΩW ΩV : Type} [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]

lemma prob_nonneg (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV) (ω : BertsekasLQGSample M) :
    0 ≤ BertsekasLQGProb M ω :=
  mul_nonneg (mul_nonneg (M.hp0_nonneg _)
      (Finset.prod_nonneg fun k _ => M.hpW_nonneg _ _))
    (Finset.prod_nonneg fun k _ => M.hpV_nonneg _ _)

open Classical in
/-- Every policy has the same estimation error as the zero policy. -/
lemma main (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV)
    (π : List (Fin q → ℝ) → Fin m → ℝ) (k : ℕ)
    (ω : BertsekasLQGSample M) (hω : BertsekasLQGProb M ω ≠ 0) :
    (BertsekasLQGTraj M π k ω).1 - BertsekasLQGEstimate M π k ω =
      (BertsekasLQGTraj M 0 k ω).1 - BertsekasLQGEstimate M 0 k ω := by
  have hE : ∀ a : BertsekasLQGSample M,
      ((BertsekasLQGTraj M π k a).2 = (BertsekasLQGTraj M π k ω).2)
        ↔ ((BertsekasLQGTraj M 0 k a).2 = (BertsekasLQGTraj M 0 k ω).2) :=
    fun a => ⟨(key M π k a ω).2, fun h => ((key M π k a ω).1 h).1⟩
  have hshift : BertsekasLQGEstimate M π k ω
      = BertsekasLQGEstimate M 0 k ω
        + ((BertsekasLQGTraj M π k ω).1 - (BertsekasLQGTraj M 0 k ω).1) := by
    refine condexp_shift _ _ _ _ _ _ hE (fun a ha => ?_) ?_
    · have := ((key M π k a ω).1 ((hE a).1 ha)).2
      rw [← this]
      abel
    · refine ne_of_gt (Finset.sum_pos' (fun a _ => prob_nonneg M a) ⟨ω, ?_, ?_⟩)
      · simp
      · exact lt_of_le_of_ne (prob_nonneg M ω) (Ne.symm hω)
  rw [hshift]
  abel

end LQGaux

theorem solution {n m q : ℕ}
    {Ω₀ ΩW ΩV : Type} [Fintype Ω₀] [Fintype ΩW] [Fintype ΩV]
    (M : BertsekasLQGModel n m q Ω₀ ΩW ΩV)
    (π π' : List (Fin q → ℝ) → Fin m → ℝ) (k : ℕ) (hk : k ≤ M.N)
    (ω : BertsekasLQGSample M) (hω : BertsekasLQGProb M ω ≠ 0) :
    (BertsekasLQGTraj M π k ω).1 - BertsekasLQGEstimate M π k ω =
      (BertsekasLQGTraj M π' k ω).1 - BertsekasLQGEstimate M π' k ω := by
  rw [LQGaux.main M π k ω hω, LQGaux.main M π' k ω hω]
