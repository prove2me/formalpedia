-- Prove2me | solution 1 for BuyXFree.Threshold.case_c_stationary
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:27:39.902221+00:00
-- url     : https://prove2.me/submissions/6d0eef37-7fd2-4708-9bcb-71de17f30c24

import Mathlib
import Definitions.Def_BuyXFree_Threshold_Model
import Definitions.Def_MarkovChain

namespace Aux_BuyXFree_case_c
open BuyXFree.Threshold Matrix

def prev (X : ℕ) (j : Fin (X + 1)) : Fin (X + 1) :=
  if j.val = 0 then ⟨X, by omega⟩ else ⟨j.val - 1, by omega⟩

theorem next_iff (X : ℕ) (i j : Fin (X + 1)) : j = nextState X i ↔ i = prev X j := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  unfold nextState prev
  by_cases h1 : i < X
  · rw [dif_pos h1]
    by_cases h2 : j = 0
    · rw [if_pos h2, Fin.ext_iff, Fin.ext_iff]; simp only; omega
    · rw [if_neg h2, Fin.ext_iff, Fin.ext_iff]; simp only; omega
  · rw [dif_neg h1]
    by_cases h2 : j = 0
    · rw [if_pos h2, Fin.ext_iff, Fin.ext_iff, Fin.val_zero]; simp only; omega
    · rw [if_neg h2, Fin.ext_iff, Fin.ext_iff, Fin.val_zero]; simp only; omega

theorem vecMul_trans (P : Params) (p : ℝ) (X : ℕ) (J : ℕ → ℝ) (π : Fin (X + 1) → ℝ)
    (j : Fin (X + 1)) :
    (π ᵥ* BuyXFree.Threshold.trans P p X J) j = π (prev X j) * moveProb P p X J (prev X j) +
      π j * (1 - moveProb P p X J j) := by
  simp only [vecMul, dotProduct, BuyXFree.Threshold.trans, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  congr 1
  · rw [Finset.sum_congr rfl fun i _ => by rw [if_congr (next_iff X i j) rfl rfl]]
    rw [Finset.sum_ite_eq']
    simp
  · rw [Finset.sum_ite_eq]
    simp

theorem sum_split (X τ : ℕ) (hτ : τ ≤ X + 1) (a b : ℝ) :
    ∑ i : Fin (X + 1), (if i.val < τ then a else b) = τ * a + ((X : ℝ) + 1 - τ) * b := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if k < τ then a else b) (X + 1),
    ← Finset.sum_range_add_sum_Ico _ hτ]
  rw [Finset.sum_congr rfl fun k hk => if_pos (Finset.mem_range.mp hk),
    Finset.sum_congr rfl fun k hk => if_neg (not_lt.mpr (Finset.mem_Ico.mp hk).1)]
  simp only [Finset.sum_const, Finset.card_range, Nat.card_Ico, nsmul_eq_mul]
  rw [Nat.cast_sub hτ]
  push_cast
  ring

end Aux_BuyXFree_case_c

open BuyXFree.Threshold Matrix Aux_BuyXFree_case_c in
theorem solution (P : Params) (hP : P.Standing) (p : ℝ) (X : ℕ) (hX : 1 ≤ X)
    (J : ℕ → ℝ) (hC : CaseC P p X J) :
    MarkovChain.IsStationary (BuyXFree.Threshold.trans P p X J)
        (fun i => (if i.val < X then 1 else P.q) / ((X : ℝ) + P.q)) ∧
      (0 < P.lam → 0 < P.q → ∀ μ : Fin (X + 1) → ℝ, MarkovChain.IsStationary (BuyXFree.Threshold.trans P p X J) μ →
        μ = fun i => (if i.val < X then 1 else P.q) / ((X : ℝ) + P.q)) ∧
      (fun i : Fin (X + 1) => (if i.val < X then 1 else P.q) / ((X : ℝ) + P.q)) ⬝ᵥ
          buyProb P p X J =
        P.lam * P.q * X / ((X : ℝ) + P.q) := by
  obtain ⟨hl0, hl1, hq0, hq1, -, -, -, -, -⟩ := hP
  obtain ⟨hBx, hRL, hRH⟩ := hC
  set Dn : ℝ := (X : ℝ) + P.q with hDn
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hD : 0 < Dn := by rw [hDn]; linarith
  set mp := moveProb P p X J with hmpdef
  have hmp : ∀ i : Fin (X + 1), mp i = if i.val < X then P.lam * P.q else P.lam := by
    intro i
    simp only [hmpdef, moveProb]
    by_cases hiX : i.val < X
    · rw [if_pos hiX]
      obtain ⟨hL, hH⟩ := hBx i.val hiX
      rw [if_pos hL, if_neg hH, if_pos hiX]; ring
    · rw [if_neg hiX, if_pos hRL, if_pos hRH, if_neg hiX]; ring
  set π : Fin (X + 1) → ℝ := fun i => (if i.val < X then 1 else P.q) / Dn with hπ
  have hπm : ∀ i, π i * mp i = P.lam * P.q / Dn := by
    intro i
    simp only [hπ, hmp i]
    split_ifs <;> field_simp <;> ring
  have hsumπ : ∑ i, π i = 1 := by
    simp only [hπ]
    rw [← Finset.sum_div, sum_split X X (by omega) 1 P.q, div_eq_one_iff_eq hD.ne', hDn]
    ring
  have hstat : MarkovChain.IsStationary (BuyXFree.Threshold.trans P p X J) π := by
    refine ⟨⟨fun i => ?_, hsumπ⟩, ?_⟩
    · simp only [hπ]; split_ifs <;> positivity
    · funext j
      rw [vecMul_trans, ← hmpdef, hπm, mul_sub, mul_one, hπm]
      ring
  refine ⟨hstat, ?_, ?_⟩
  · intro hl hq μ hμ
    have hmpos : ∀ i : Fin (X + 1), 0 < mp i := by
      intro i; rw [hmp i]; split_ifs
      · exact mul_pos hl hq
      · exact hl
    have hbal : ∀ j, μ j * mp j = μ (prev X j) * mp (prev X j) := by
      intro j
      have := congrFun hμ.2 j
      rw [vecMul_trans, ← hmpdef] at this
      linarith
    set g := fun i => μ i * mp i with hg
    have hconst : ∀ k (hk : k < X + 1), g ⟨k, hk⟩ = g 0 := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        have hp : prev X ⟨k + 1, hk⟩ = ⟨k, by omega⟩ := by
          unfold prev; simp
        have := hbal ⟨k + 1, hk⟩
        rw [hp] at this
        simp only [hg]
        rw [this]
        exact ih (by omega)
    have hgall : ∀ i, μ i * mp i = g 0 := fun i => hconst i.val i.isLt
    have hμi : ∀ i, μ i = g 0 / mp i := fun i => by
      rw [← hgall i]; field_simp [(hmpos i).ne']
    have hsum1 := hμ.1.2
    simp only [hμi] at hsum1
    have hinv : ∀ i : Fin (X + 1), g 0 / mp i =
        (if i.val < X then g 0 / (P.lam * P.q) else g 0 / P.lam) := by
      intro i; rw [hmp i]; split_ifs <;> rfl
    simp only [hinv] at hsum1
    rw [sum_split X X (by omega)] at hsum1
    have hlq : 0 < P.lam * P.q := mul_pos hl hq
    have e : (X : ℝ) * (g 0 / (P.lam * P.q)) + ((X : ℝ) + 1 - X) * (g 0 / P.lam) =
        g 0 * Dn / (P.lam * P.q) := by
      rw [hDn]; field_simp; ring
    rw [e, div_eq_one_iff_eq hlq.ne'] at hsum1
    have hg0 : g 0 = P.lam * P.q / Dn := by
      rw [eq_div_iff hD.ne']; exact hsum1
    funext i
    rw [hμi i, hg0, hmp i]
    simp only [hπ]
    split_ifs <;> field_simp <;> ring
  · simp only [dotProduct, buyProb]
    have : ∀ i : Fin (X + 1), π i * (if i.val < X then mp i else 0) =
        if i.val < X then P.lam * P.q / Dn else 0 := by
      intro i; split_ifs
      · exact hπm i
      · ring
    simp only [← hπ, ← hmpdef, this]
    rw [Fin.sum_univ_eq_sum_range (fun k => if k < X then P.lam * P.q / Dn else 0) (X + 1)]
    rw [Finset.sum_range_succ, if_neg (lt_irrefl X), add_zero]
    rw [Finset.sum_congr rfl fun k hk => if_pos (Finset.mem_range.mp hk)]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
