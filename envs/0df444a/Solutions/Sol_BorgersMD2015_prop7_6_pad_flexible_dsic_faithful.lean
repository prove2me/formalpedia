-- Prove2me | solution 1 for BorgersMD2015.prop7_6_pad_flexible_dsic_faithful
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-28T03:18:08.615416+00:00
-- url     : https://prove2.me/submissions/7e0c89dc-c13e-49d8-aa29-01551c89b750

import Mathlib
import Definitions.Def_MechanismDesign_VCG_Model

open MechanismDesign.VCG

namespace BGDis

abbrev Θ : Fin 2 → Type := fun _ => Fin 3 → ℝ

def u : ∀ i : Fin 2, Fin 3 → Θ i → ℝ := fun _ a θ => θ a

def key (θ : ∀ i, Θ i) (a : Fin 3) : Lex (ℝ × ℝ) := toLex (θ 0 a, -θ 1 a)

lemma ex (θ : ∀ i, Θ i) : ∃ a ∈ (Finset.univ : Finset (Fin 3)), ∀ b ∈ (Finset.univ : Finset (Fin 3)), key θ b ≤ key θ a :=
  Finset.exists_max_image _ _ Finset.univ_nonempty

noncomputable def q (θ : ∀ i, Θ i) : Fin 3 := Classical.choose (ex θ)

lemma q_spec (θ : ∀ i, Θ i) (b : Fin 3) : key θ b ≤ key θ (q θ) :=
  (Classical.choose_spec (ex θ)).2 b (Finset.mem_univ _)

lemma key_le_iff (θ : ∀ i, Θ i) (a b : Fin 3) :
    key θ b ≤ key θ a ↔ θ 0 b < θ 0 a ∨ (θ 0 b = θ 0 a ∧ -θ 1 b ≤ -θ 1 a) := by
  unfold key; exact Prod.Lex.toLex_le_toLex

lemma q_eq_of_strict (θ : ∀ i, Θ i) (a : Fin 3) (h : ∀ b, b ≠ a → key θ b < key θ a) : q θ = a := by
  by_contra hne
  exact absurd (q_spec θ a) (not_le.mpr (h _ hne))

lemma pad : PAD u q := by
  intro θ θ' a hq hdiff
  apply q_eq_of_strict
  intro b hb
  have h0 := hdiff 0 b hb
  simp only [u] at h0
  have hle : θ 0 b ≤ θ 0 a := by
    have := q_spec θ b
    rw [hq, key_le_iff] at this
    rcases this with h | ⟨h, _⟩ <;> linarith
  have : θ' 0 b < θ' 0 a := by linarith
  unfold key
  exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl this)


def single (a : Fin 3) : ∀ i, Θ i := fun i => if i = 0 then Pi.single a 1 else 0

lemma q_single (a : Fin 3) : q (single a) = a := by
  apply q_eq_of_strict
  intro b hb
  unfold key single
  apply Prod.Lex.toLex_lt_toLex.mpr
  left
  simp [Pi.single_apply, hb]

lemma flex : Flexible q := by
  have : Set.range q = Set.univ := Set.eq_univ_of_forall fun a => ⟨single a, q_single a⟩
  unfold Flexible; rw [this, Set.encard_univ]; simp

def ty (v : Fin 3 → ℝ) : ∀ i, Θ i := fun i => if i = 0 then 0 else v

def vy : Fin 3 → ℝ := ![1, 0, 1]
def vx : Fin 3 → ℝ := ![-1, 0, 1]

lemma upd (v w : Fin 3 → ℝ) : Function.update (ty v) 1 w = ty w := by
  funext i; fin_cases i <;> simp [ty]

lemma q_vy : q (ty vy) = 1 := by
  apply q_eq_of_strict
  intro b hb
  unfold key ty vy
  apply Prod.Lex.toLex_lt_toLex.mpr
  right
  fin_cases b <;> simp_all

lemma q_vx : q (ty vx) = 0 := by
  apply q_eq_of_strict
  intro b hb
  unfold key ty vx
  apply Prod.Lex.toLex_lt_toLex.mpr
  right
  fin_cases b <;> simp_all <;> norm_num

lemma not_dsic (t : Fin 2 → (∀ i, Θ i) → ℝ) : ¬ DSIC u ({ q := q, t := t } : DirectMechanism Θ (Fin 3)) := by
  intro h
  have h1 := h (ty vy) 1 vx
  have h2 := h (ty vx) 1 vy
  simp only [upd, q_vy, q_vx, u, ty] at h1 h2
  simp [vx, vy] at h1 h2
  linarith

end BGDis

theorem solution : ¬ (∀ {ι A : Type} [Fintype ι] [DecidableEq ι]
    [Finite A] {Θ : ι → Type} (u : ∀ i, A → Θ i → ℝ)
    (hrich : ∀ (i : ι) (ν : A → ℝ), ∃ θi : Θ i, ∀ a, u i a θi = ν a)
    (q : (∀ i, Θ i) → A) (hflex : Flexible q) (hpad : PAD u q),
    ∃ t : ι → (∀ i, Θ i) → ℝ, DSIC u ({ q := q, t := t } : DirectMechanism Θ A)) := by
  intro H
  obtain ⟨t, ht⟩ := @H (Fin 2) (Fin 3) _ _ _ BGDis.Θ BGDis.u (fun i ν => ⟨ν, fun a => rfl⟩) BGDis.q BGDis.flex BGDis.pad
  exact BGDis.not_dsic t ht

