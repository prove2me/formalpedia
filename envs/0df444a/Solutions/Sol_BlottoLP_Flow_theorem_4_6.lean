-- Prove2me | solution 1 for BlottoLP.Flow.theorem_4_6
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:00:10.908489+00:00
-- url     : https://prove2.me/submissions/c9912ad0-a3f1-4c28-9488-19e10fe50373

import Mathlib
import Definitions.Def_BlottoLP_Flow_Model
import Definitions.Def_BlottoLP_Flow_LinearFormulation
import Theorems.Thm_BlottoLP_Flow_linear_program_1

namespace BlottoLP.Flow.GoalAux

open Finset Matrix BlottoLP.Flow

/-- Every linear functional on `(ι → ℝ) × (κ → ℝ)` is a dot product. -/
theorem lin_expand {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (f : ((ι → ℝ) × (κ → ℝ)) →ₗ[ℝ] ℝ) (x : ι → ℝ) (y : κ → ℝ) :
    f (x, y) = ∑ m, f (Pi.single m 1, 0) * x m + ∑ m, f (0, Pi.single m 1) * y m := by
  have h1 : (x, y) = ((x, 0) : (ι → ℝ) × (κ → ℝ)) + (0, y) := by simp
  rw [h1, map_add]
  congr 1
  · have := LinearMap.pi_apply_eq_sum_univ (f.comp (LinearMap.inl ℝ _ _)) x
    simp only [LinearMap.comp_apply, LinearMap.inl_apply] at this
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_eq_mul, mul_comm]
    have hs : (fun j => if m = j then (1:ℝ) else 0) = Pi.single m 1 := by
      ext j; by_cases h : m = j <;> simp [Pi.single_apply, h, eq_comm]
    rw [hs]
  · have := LinearMap.pi_apply_eq_sum_univ (f.comp (LinearMap.inr ℝ _ _)) y
    simp only [LinearMap.comp_apply, LinearMap.inr_apply] at this
    rw [this]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_eq_mul, mul_comm]
    have hs : (fun j => if m = j then (1:ℝ) else 0) = Pi.single m 1 := by
      ext j; by_cases h : m = j <;> simp [Pi.single_apply, h, eq_comm]
    rw [hs]

/-- A set cut out (after projecting away auxiliary variables) by finitely many affine
equations and inequalities has a linear formulation of the corresponding size. -/
theorem hasLF_of_system {ι κ E L : Type} [Fintype ι] [Fintype κ] [Fintype E] [Fintype L]
    [DecidableEq ι] [DecidableEq κ]
    (P : Set (ι → ℝ)) (fe : E → ((ι → ℝ) × (κ → ℝ)) →ₗ[ℝ] ℝ) (ce : E → ℝ)
    (fl : L → ((ι → ℝ) × (κ → ℝ)) →ₗ[ℝ] ℝ) (cl : L → ℝ) (m n : ℕ)
    (hm : Fintype.card E + Fintype.card L ≤ m) (hn : Fintype.card ι + Fintype.card κ ≤ n)
    (hP : ∀ x, x ∈ P ↔ ∃ y : κ → ℝ, (∀ i, fe i (x, y) = ce i) ∧ (∀ j, fl j (x, y) ≤ cl j)) :
    HasLinearFormulation P m n := by
  classical
  let eK := Fintype.equivFin κ
  let eE := Fintype.equivFin E
  let eL := Fintype.equivFin L
  refine ⟨Fintype.card κ, Fintype.card E, Fintype.card L,
    fun i m => fe (eE.symm i) (Pi.single m 1, 0),
    fun i m => fe (eE.symm i) (0, Pi.single (eK.symm m) 1), fun i => ce (eE.symm i),
    fun i m => fl (eL.symm i) (Pi.single m 1, 0),
    fun i m => fl (eL.symm i) (0, Pi.single (eK.symm m) 1), fun i => cl (eL.symm i),
    hm, hn, ?_⟩
  intro x
  have hE : ∀ (f : ((ι → ℝ) × (κ → ℝ)) →ₗ[ℝ] ℝ) (y : κ → ℝ),
      f (x, y) = ∑ m, f (Pi.single m 1, 0) * x m +
        ∑ m : Fin (Fintype.card κ), f (0, Pi.single (eK.symm m) 1) * y (eK.symm m) := by
    intro f y
    rw [lin_expand f x y]
    congr 1
    exact (Equiv.sum_comp eK.symm (fun m => f (0, Pi.single m 1) * y m)).symm
  rw [hP]
  constructor
  · rintro ⟨y, h1, h2⟩
    refine ⟨y ∘ eK.symm, ?_, ?_⟩
    · ext i
      simp only [Pi.add_apply, mulVec, dotProduct, Function.comp_apply]
      rw [← h1 (eE.symm i), hE]
    · intro i
      simp only [Pi.add_apply, mulVec, dotProduct, Function.comp_apply]
      rw [← hE]
      exact h2 _
  · rintro ⟨y, h1, h2⟩
    refine ⟨y ∘ eK, ?_, ?_⟩
    · intro i
      have := congrFun h1 (eE i)
      simp only [Pi.add_apply, mulVec, dotProduct, Equiv.symm_apply_apply] at this
      rw [hE]
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
      exact this
    · intro j
      have := h2 (eL j)
      simp only [Pi.add_apply, mulVec, dotProduct, Equiv.symm_apply_apply] at this
      rw [hE]
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
      exact this


section System

variable (I : Instance)

abbrev Iota := Fin I.K × Fin (I.A + 1)
abbrev Kap := Edge I.K I.A ⊕ (Fin (I.K + 1) × Fin (I.B + 1))
abbrev V := (Iota I → ℝ) × (Kap I → ℝ)

def LX (i : Iota I) : V I →ₗ[ℝ] ℝ := (LinearMap.proj i).comp (LinearMap.fst ℝ _ _)
def LF (e : Edge I.K I.A) : V I →ₗ[ℝ] ℝ :=
  (LinearMap.proj (Sum.inl e : Kap I)).comp (LinearMap.snd ℝ _ _)
def LD (k : Fin (I.K + 1)) (i : Fin (I.B + 1)) : V I →ₗ[ℝ] ℝ :=
  (LinearMap.proj (Sum.inr (k, i) : Kap I)).comp (LinearMap.snd ℝ _ _)

@[simp] theorem LX_apply (i : Iota I) (v : V I) : LX I i v = v.1 i := rfl
@[simp] theorem LF_apply (e : Edge I.K I.A) (v : V I) : LF I e v = v.2 (Sum.inl e) := rfl
@[simp] theorem LD_apply (k : Fin (I.K + 1)) (i : Fin (I.B + 1)) (v : V I) :
    LD I k i v = v.2 (Sum.inr (k, i)) := rfl

def Fof (y : Kap I → ℝ) : Edge I.K I.A → ℝ := fun e => y (Sum.inl e)
def Dof (y : Kap I → ℝ) : Fin (I.K + 1) → Fin (I.B + 1) → ℝ := fun k i => y (Sum.inr (k, i))

def inflowL (k : Fin I.K) (l : Fin (I.A + 1)) : V I →ₗ[ℝ] ℝ :=
  ∑ e ∈ univ.filter (fun e : Edge I.K I.A => e.1.1 = k ∧ e.1.2.2 = l), LF I e
def outflowL (k : Fin I.K) (l : Fin (I.A + 1)) : V I →ₗ[ℝ] ℝ :=
  ∑ e ∈ univ.filter (fun e : Edge I.K I.A => e.1.1 = k ∧ e.1.2.1 = l), LF I e
def margL (p : Iota I) : V I →ₗ[ℝ] ℝ :=
  ∑ e ∈ univ.filter (fun e : Edge I.K I.A =>
    e.1.1 = p.1 ∧ (e.1.2.2 : ℕ) = e.1.2.1 + p.2), LF I e - LX I p
def WL (k : Fin I.K) (t : Fin (I.B + 1)) : V I →ₗ[ℝ] ℝ :=
  ∑ l : Fin (I.A + 1), (- I.U k l t) • LX I (k, l)

theorem inflowL_apply (k l) (x : Iota I → ℝ) (y : Kap I → ℝ) :
    inflowL I k l (x, y) = inflow (Fof I y) k l := by
  simp [inflowL, inflow, Fof, LinearMap.sum_apply]
theorem outflowL_apply (k l) (x : Iota I → ℝ) (y : Kap I → ℝ) :
    outflowL I k l (x, y) = outflow (Fof I y) k l := by
  simp [outflowL, outflow, Fof, LinearMap.sum_apply]
theorem margL_apply (p) (x : Iota I → ℝ) (y : Kap I → ℝ) :
    margL I p (x, y) = flowMarginal (Fof I y) p - x p := by
  simp [margL, flowMarginal, Fof, LinearMap.sum_apply]
theorem WL_apply (k t) (x : Iota I → ℝ) (y : Kap I → ℝ) :
    WL I k t (x, y) = weightB I x k t := by
  simp [WL, weightB, LinearMap.sum_apply, mul_comm]

abbrev EqIdx := (Fin I.K × Fin (I.A + 1)) ⊕ (Fin I.K × Fin (I.A + 1)) ⊕ Fin I.K ⊕ Fin I.K ⊕
  (Fin I.K × Fin (I.A + 1)) ⊕ Unit
abbrev LeIdx := Edge I.K I.A ⊕ (Fin I.K × Fin (I.B + 1) × Fin (I.B + 1)) ⊕ Unit

def f1 (p : Fin I.K × Fin (I.A + 1)) : V I →ₗ[ℝ] ℝ :=
  if h : (p.1 : ℕ) + 1 < I.K then inflowL I p.1 p.2 - outflowL I ⟨p.1 + 1, h⟩ p.2 else 0
def f2 (p : Fin I.K × Fin (I.A + 1)) : V I →ₗ[ℝ] ℝ :=
  if (p.1 : ℕ) = 0 ∧ 0 < p.2 then outflowL I p.1 p.2 else 0
def f3 (k : Fin I.K) : V I →ₗ[ℝ] ℝ := if (k : ℕ) = 0 then outflowL I k 0 else 0
def c3 (k : Fin I.K) : ℝ := if (k : ℕ) = 0 then 1 else 0
def f4 (k : Fin I.K) : V I →ₗ[ℝ] ℝ :=
  if (k : ℕ) + 1 = I.K then inflowL I k (Fin.last _) else 0
def c4 (k : Fin I.K) : ℝ := if (k : ℕ) + 1 = I.K then 1 else 0

def g2 (p : Fin I.K × Fin (I.B + 1) × Fin (I.B + 1)) : V I →ₗ[ℝ] ℝ :=
  if h : p.2.2 ≤ p.2.1 then
    LD I p.1.castSucc p.2.2 + WL I p.1 ⟨p.2.1 - p.2.2, lt_of_le_of_lt (Nat.sub_le _ _) p.2.1.isLt⟩
      - LD I p.1.succ p.2.1
  else 0

def fe : EqIdx I → V I →ₗ[ℝ] ℝ :=
  Sum.elim (f1 I) (Sum.elim (f2 I) (Sum.elim (f3 I) (Sum.elim (f4 I)
    (Sum.elim (margL I) (fun _ => LD I 0 0)))))
def ce : EqIdx I → ℝ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (c3 I) (Sum.elim (c4 I)
    (Sum.elim (fun _ => 0) (fun _ => 0)))))
def fl : LeIdx I → V I →ₗ[ℝ] ℝ :=
  Sum.elim (fun e => - LF I e) (Sum.elim (g2 I) (fun _ => LD I (Fin.last _) (Fin.last _)))
def cl (v : ℝ) : LeIdx I → ℝ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => -v))

theorem f1_iff (x : Iota I → ℝ) (y : Kap I → ℝ) :
    (∀ p, f1 I p (x, y) = 0) ↔
      ∀ (k k' : Fin I.K), (k' : ℕ) = k + 1 → ∀ l, inflow (Fof I y) k l = outflow (Fof I y) k' l := by
  constructor
  · intro h k k' hk l
    have hlt : (k : ℕ) + 1 < I.K := hk ▸ k'.isLt
    have h1 := h (k, l)
    have hk' : k' = ⟨k + 1, hlt⟩ := Fin.ext hk
    subst hk'
    simp only [f1, dif_pos hlt, LinearMap.sub_apply, inflowL_apply, outflowL_apply] at h1
    linarith
  · rintro h ⟨k, l⟩
    unfold f1
    split_ifs with hlt
    · simp only [LinearMap.sub_apply, inflowL_apply, outflowL_apply]
      rw [h k ⟨k + 1, hlt⟩ rfl l]; ring
    · simp

theorem f2_iff (x : Iota I → ℝ) (y : Kap I → ℝ) :
    (∀ p, f2 I p (x, y) = 0) ↔
      ∀ k : Fin I.K, (k : ℕ) = 0 → ∀ l : Fin (I.A + 1), 0 < l → outflow (Fof I y) k l = 0 := by
  constructor
  · intro h k hk l hl
    have h1 := h (k, l)
    simp only [f2, if_pos (And.intro hk hl), outflowL_apply] at h1
    exact h1
  · rintro h ⟨k, l⟩
    unfold f2
    split_ifs with hc
    · rw [outflowL_apply]; exact h k hc.1 l hc.2
    · simp

theorem f3_iff (x : Iota I → ℝ) (y : Kap I → ℝ) :
    (∀ k, f3 I k (x, y) = c3 I k) ↔
      ∀ k : Fin I.K, (k : ℕ) = 0 → outflow (Fof I y) k 0 = 1 := by
  constructor
  · intro h k hk
    have h1 := h k
    simp only [f3, c3, if_pos hk, outflowL_apply] at h1
    exact h1
  · intro h k
    unfold f3 c3
    split_ifs with hc
    · rw [outflowL_apply]; exact h k hc
    · simp

theorem f4_iff (x : Iota I → ℝ) (y : Kap I → ℝ) :
    (∀ k, f4 I k (x, y) = c4 I k) ↔
      ∀ k : Fin I.K, (k : ℕ) + 1 = I.K → inflow (Fof I y) k (Fin.last I.A) = 1 := by
  constructor
  · intro h k hk
    have h1 := h k
    simp only [f4, c4, if_pos hk, inflowL_apply] at h1
    exact h1
  · intro h k
    unfold f4 c4
    split_ifs with hc
    · rw [inflowL_apply]; exact h k hc
    · simp

theorem f5_iff (x : Iota I → ℝ) (y : Kap I → ℝ) :
    (∀ p, margL I p (x, y) = 0) ↔ flowMarginal (Fof I y) = x := by
  constructor
  · intro h
    funext p
    have h1 := h p
    rw [margL_apply] at h1
    linarith
  · intro h p
    rw [margL_apply, h, sub_self]

theorem g2_iff (x : Iota I → ℝ) (y : Kap I → ℝ) :
    (∀ p, g2 I p (x, y) ≤ 0) ↔
      ∀ (k : Fin I.K) (i j t : Fin (I.B + 1)), (j : ℕ) + t = i →
        Dof I y k.castSucc j + weightB I x k t ≤ Dof I y k.succ i := by
  constructor
  · intro h k i j t hjt
    have hji : j ≤ i := by rw [Fin.le_def]; omega
    have h1 := h (k, i, j)
    have ht : t = ⟨(i : ℕ) - j, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩ := by
      ext; simp; omega
    subst ht
    simp only [g2, dif_pos hji, LinearMap.sub_apply, LinearMap.add_apply, LD_apply,
      WL_apply] at h1
    simp only [Dof]
    linarith
  · rintro h ⟨k, i, j⟩
    unfold g2
    dsimp only
    split_ifs with hji
    · simp only [LinearMap.sub_apply, LinearMap.add_apply, LD_apply, WL_apply]
      have := h k i j ⟨(i : ℕ) - j, lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
        (by simp; rw [Fin.le_def] at hji; omega)
      simp only [Dof] at this
      linarith
    · simp

theorem system_iff (v : ℝ) (x : Iota I → ℝ) (y : Kap I → ℝ) :
    ((∀ i, fe I i (x, y) = ce I i) ∧ (∀ j, fl I j (x, y) ≤ cl I v j)) ↔
      (IsUnitFlow (Fof I y) ∧ flowMarginal (Fof I y) = x ∧ IsDPBound (weightB I x) (Dof I y) ∧
        Dof I y (Fin.last I.K) (Fin.last I.B) ≤ -v) := by
  simp only [Sum.forall, fe, ce, fl, cl, Sum.elim_inl, Sum.elim_inr]
  rw [f1_iff, f2_iff, f3_iff, f4_iff, f5_iff, g2_iff]
  simp only [LinearMap.neg_apply, LF_apply, LD_apply, IsUnitFlow, IsDPBound, Dof, Fof]
  constructor
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, h7, h8, h9⟩
    exact ⟨⟨fun e => by linarith [h7 e], h1, h2, h3, h4⟩, h5, ⟨h6 (), h8⟩, h9 ()⟩
  · rintro ⟨⟨h7, h1, h2, h3, h4⟩, h5, ⟨h6, h8⟩, h9⟩
    exact ⟨⟨h1, h2, h3, h4, h5, fun _ => h6⟩, fun e => by linarith [h7 e], h8, fun _ => h9⟩

end System

end BlottoLP.Flow.GoalAux

open BlottoLP.Flow BlottoLP.Flow.GoalAux in
theorem solution :
    ∃ c : ℕ, ∀ (I : Instance) (N : ℕ), 1 ≤ I.K → 1 ≤ N → I.A ≤ N → I.B ≤ N →
      HasLinearFormulation (PA I) (c * N ^ 2 * I.K) (c * N ^ 2 * I.K) := by
  refine ⟨40, fun I N hK hN hA hB => ?_⟩
  classical
  have hE : Fintype.card (Edge I.K I.A) ≤ I.K * ((I.A + 1) * (I.A + 1)) := by
    refine (Fintype.card_subtype_le _).trans ?_
    simp
  have hA2 : I.A + 1 ≤ 2 * N := by omega
  have hB2 : I.B + 1 ≤ 2 * N := by omega
  have hK2 : I.K + 1 ≤ 2 * I.K := by omega
  have t1 : I.K * (I.A + 1) ≤ I.K * (2 * N) := Nat.mul_le_mul_left _ hA2
  have t2 : I.K * ((I.A + 1) * (I.A + 1)) ≤ I.K * ((2 * N) * (2 * N)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hA2 hA2)
  have t3 : (I.K + 1) * (I.B + 1) ≤ (2 * I.K) * (2 * N) := Nat.mul_le_mul hK2 hB2
  have t4 : I.K * ((I.B + 1) * (I.B + 1)) ≤ I.K * ((2 * N) * (2 * N)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul hB2 hB2)
  have hNN : N ≤ N ^ 2 := by nlinarith
  have t5 : I.K * N ≤ I.K * N ^ 2 := Nat.mul_le_mul_left _ hNN
  have t6 : 1 ≤ I.K * N ^ 2 := Nat.mul_le_mul hK (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by omega)))
  have t7 : I.K ≤ I.K * N ^ 2 := Nat.le_mul_of_pos_right _ (by positivity)
  by_cases hne : ∃ σ₀ τ₀, IsNashEq (payoff I) σ₀ τ₀
  · obtain ⟨σ₀, τ₀, h⟩ := hne
    refine hasLF_of_system (κ := Kap I) (PA I) (fe I) (ce I) (fl I)
      (cl I (expPayoff I σ₀ τ₀)) _ _ ?_ ?_ ?_
    · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit]
      ring_nf at t1 t2 t3 t4 t5 t6 t7 hE ⊢
      linarith
    · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
      ring_nf at t1 t2 t3 t4 t5 t6 t7 hE ⊢
      linarith
    · intro x
      rw [linear_program_1 I σ₀ τ₀ h x]
      constructor
      · rintro ⟨F, D, hF, hm, hD, hl⟩
        exact ⟨Sum.elim F (fun p => D p.1 p.2), (system_iff I _ x _).2 ⟨hF, hm, hD, hl⟩⟩
      · rintro ⟨y, hy⟩
        exact ⟨Fof I y, Dof I y, (system_iff I _ x y).1 hy⟩
  · refine hasLF_of_system (κ := Empty) (E := Empty) (L := Unit) (PA I) (fun _ => 0)
      (fun _ => 0) (fun _ => 0) (fun _ => -1) _ _ ?_ ?_ ?_
    · simp only [Fintype.card_unit, Fintype.card_empty]
      ring_nf at t6 ⊢
      linarith
    · simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_empty]
      ring_nf at t1 t5 ⊢
      linarith
    · intro x
      constructor
      · rintro ⟨σ, ⟨τ, h⟩, _⟩
        exact absurd ⟨σ, τ, h⟩ hne
      · rintro ⟨y, _, h⟩
        have := h ()
        simp at this
        linarith
