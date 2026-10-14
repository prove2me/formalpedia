-- Prove2me | solution 1 for Disjunctive.VPolyhedral.v_polyhedral_validity_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:48:42.269987+00:00
-- url     : https://prove2.me/submissions/794edf09-7c09-40ae-a874-42dfee428d9b

import Mathlib
import Definitions.Def_Disjunctive_VPolyhedral_Basic



namespace Disjunctive.VPolyhedral

theorem vval_core {n : ℕ} {Q : Type*} [Fintype Q] (Vidx Ridx : Q → Type*)
    [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)] [∀ h, Nonempty (Vidx h)]
    (vpt : ∀ h, Vidx h → Fin n → ℝ)
    (rvec : ∀ h, Ridx h → Fin n → ℝ) (alpha : Fin n → ℝ) (beta : ℝ) :
    (∀ x ∈ DisjSet Vidx Ridx vpt rvec, beta ≤ dotProduct alpha x) ↔
      IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta := by
  classical
  constructor
  · intro H
    have mem : ∀ h (p : Vidx h) (r : Ridx h) (t : ℝ), 0 ≤ t →
        vpt h p + t • rvec h r ∈ DisjSet Vidx Ridx vpt rvec := by
      intro h p r t ht
      refine Set.mem_iUnion.2 ⟨h, Pi.single p 1, Pi.single r t, ?_, ?_, ?_, ?_⟩
      · intro i; by_cases hi : i = p
        · subst hi; simp
        · simp [Pi.single_apply, hi]
      · simp
      · intro i; by_cases hi : i = r
        · subst hi; simp [ht]
        · simp [Pi.single_apply, hi]
      · simp [Pi.single_apply, ite_smul]
    refine ⟨fun h p => ?_, fun h r => ?_⟩
    · have hm : vpt h p ∈ DisjSet Vidx Ridx vpt rvec := by
        refine Set.mem_iUnion.2 ⟨h, Pi.single p 1, fun _ => 0, ?_, ?_, ?_, ?_⟩
        · intro i; by_cases hi : i = p
          · subst hi; simp
          · simp [Pi.single_apply, hi]
        · simp
        · intro i; exact le_rfl
        · simp [Pi.single_apply, ite_smul]
      exact H _ hm
    · by_contra hneg
      push_neg at hneg
      obtain p := Classical.arbitrary (Vidx h)
      set t := (dotProduct alpha (vpt h p) - beta + 1) / (-dotProduct alpha (rvec h r)) with ht
      have hpos : 0 < -dotProduct alpha (rvec h r) := by linarith
      have h0 := H _ (mem h p r (max t 0) (le_max_right _ _))
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at h0
      have h1 : t * (-dotProduct alpha (rvec h r)) = dotProduct alpha (vpt h p) - beta + 1 := by
        rw [ht, div_mul_cancel₀ _ hpos.ne']
      have h2 : t ≤ max t 0 := le_max_left _ _
      nlinarith
  · rintro ⟨hv, hr⟩ x hx
    obtain ⟨h, lam, mu, hl, hs, hm, rfl⟩ := Set.mem_iUnion.1 hx
    rw [dotProduct_add, dotProduct_sum, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
    have a1 : beta ≤ ∑ i, lam i * dotProduct alpha (vpt h i) := by
      calc beta = ∑ i, lam i * beta := by rw [← Finset.sum_mul, hs, one_mul]
        _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hv h i) (hl i)
    have a2 : 0 ≤ ∑ i, mu i * dotProduct alpha (rvec h i) :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (hr h i)
    linarith

end Disjunctive.VPolyhedral

open Disjunctive.VPolyhedral


theorem solution {n : ℕ} {Q : Type*} [Fintype Q] (Vidx Ridx : Q → Type*)
    [∀ h, Fintype (Vidx h)] [∀ h, Fintype (Ridx h)] [∀ h, Nonempty (Vidx h)]
    (vpt : ∀ h, Vidx h → Fin n → ℝ)
    (rvec : ∀ h, Ridx h → Fin n → ℝ) (alpha : Fin n → ℝ) (beta : ℝ) :
    (∀ x ∈ DisjSet Vidx Ridx vpt rvec, beta ≤ dotProduct alpha x) ↔
      IsVPolyhedralValid Vidx Ridx vpt rvec alpha beta := by
  exact vval_core Vidx Ridx vpt rvec alpha beta
