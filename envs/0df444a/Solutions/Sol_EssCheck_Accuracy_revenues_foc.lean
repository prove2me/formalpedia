-- Prove2me | solution 1 for EssCheck.Accuracy.revenues_foc
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T03:23:47.444358+00:00
-- url     : https://prove2.me/submissions/73ff4a07-d4b5-4fba-8ee8-27daad5914cb

import Mathlib
import Definitions.Def_EssCheck_Accuracy_Model

namespace Aux_Ess_revfoc
open EssCheck.Accuracy

theorem zAt_h {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) (h : IsHybrid M β xh i) :
    zAt M β xh i = zt M i := by
  unfold zAt zOf
  exact if_pos h

theorem zAt_nh {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) (h : ¬ IsHybrid M β xh i) :
    zAt M β xh i = 0 := by
  unfold zAt zOf
  exact if_neg h

theorem yAt_nh {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) (h : ¬ IsHybrid M β xh i) :
    yAt M β xh i = 1 := by
  unfold yAt yOf
  exact if_neg h

theorem mem_hyb {n : ℕ} (M : Model n) (β xh : ℝ) (i : Fin n) :
    i ∈ hybridSet M β xh ↔ IsHybrid M β xh i := by
  unfold hybridSet
  simp

end Aux_Ess_revfoc

open EssCheck.Accuracy Aux_Ess_revfoc in
theorem solution {n : ℕ} (M : Model n) (hS : M.Standing)
    (β xh : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hx0 : 0 < xh) (hx1 : xh < 1) :
    (∀ i, (IsHybrid M β xh i →
      revH M β xh i = M.αbar * M.v i - zt M i * M.l i) ∧
      (¬ IsHybrid M β xh i → revH M β xh i = M.αbar * M.v i)) ∧
    (∀ i, (IsHybrid M β xh i → revL M β xh i = M.l i) ∧
      (¬ IsHybrid M β xh i → revL M β xh i = M.αbar * M.v i)) ∧
    piH M β xh - piL M β xh = privateWedge M (hybridSet M β xh) β := by
  obtain ⟨hpH, hpL, hp0, hαpos, hα1, hl, hlv, -⟩ := hS
  have hv : ∀ i, 0 < M.v i := by
    intro i
    by_contra hc
    push_neg at hc
    have := hlv i
    have := hl i
    nlinarith
  have hH : ∀ i, (IsHybrid M β xh i →
      revH M β xh i = M.αbar * M.v i - zt M i * M.l i) ∧
      (¬ IsHybrid M β xh i → revH M β xh i = M.αbar * M.v i) := by
    intro i
    constructor
    · intro h
      unfold revH payU
      rw [zAt_h M β xh i h]
      ring
    · intro h
      unfold revH payU
      rw [zAt_nh M β xh i h]
      ring
  have hL : ∀ i, (IsHybrid M β xh i → revL M β xh i = M.l i) ∧
      (¬ IsHybrid M β xh i → revL M β xh i = M.αbar * M.v i) := by
    intro i
    have hvi := hv i
    have hli := hl i
    constructor
    · intro h
      unfold revL payU
      rw [zAt_h M β xh i h]
      generalize yAt M β xh i = y
      unfold zt
      have h1 : M.αbar * M.v i + M.l i ≠ 0 := by positivity
      have h2 : M.v i ≠ 0 := hvi.ne'
      field_simp
      ring
    · intro h
      unfold revL payU
      rw [zAt_nh M β xh i h, yAt_nh M β xh i h]
      ring
  refine ⟨hH, hL, ?_⟩
  set T := hybridSet M β xh with hT
  have hsub : T ⊆ Finset.univ := Finset.subset_univ _
  unfold piH piL privateWedge
  rw [← Finset.sum_sdiff hsub (f := fun i => M.pH i * revH M β xh i),
    ← Finset.sum_sdiff hsub (f := fun i => M.p0 i * revL M β xh i)]
  have a1 : ∑ i ∈ T, M.pH i * revH M β xh i = ∑ i ∈ T, M.pH i * (M.αbar * M.v i - zt M i * M.l i) :=
    Finset.sum_congr rfl (fun i hi => by rw [(hH i).1 ((mem_hyb M β xh i).mp hi)])
  have a2 : ∑ i ∈ Finset.univ \ T, M.pH i * revH M β xh i =
      ∑ i ∈ Finset.univ \ T, M.pH i * (M.αbar * M.v i) :=
    Finset.sum_congr rfl (fun i hi => by
      rw [(hH i).2 (fun h => (Finset.mem_sdiff.mp hi).2 ((mem_hyb M β xh i).mpr h))])
  have a3 : ∑ i ∈ T, M.p0 i * revL M β xh i = ∑ i ∈ T, M.p0 i * M.l i :=
    Finset.sum_congr rfl (fun i hi => by rw [(hL i).1 ((mem_hyb M β xh i).mp hi)])
  have a4 : ∑ i ∈ Finset.univ \ T, M.p0 i * revL M β xh i =
      ∑ i ∈ Finset.univ \ T, M.p0 i * (M.αbar * M.v i) :=
    Finset.sum_congr rfl (fun i hi => by
      rw [(hL i).2 (fun h => (Finset.mem_sdiff.mp hi).2 ((mem_hyb M β xh i).mpr h))])
  rw [a1, a2, a3, a4]
  ring
