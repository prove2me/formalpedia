-- Prove2me | solution 1 for Disjunctive.LiftProject.cglp_lifting_from_restricted_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:22:27.678068+00:00
-- url     : https://prove2.me/submissions/e93223fe-2a91-4867-8a20-0ea363f1b2b2

import Mathlib
import Definitions.Def_Disjunctive_LiftProject_Basic
import Definitions.Def_Disjunctive_LiftProject_BoundRows



namespace Disjunctive.LiftProject

lemma cglpL_extSum {n : ℕ} {M : Type*} [Fintype M] (A : Matrix M (Fin n) ℝ)
    (w : M ⊕ Fin n → ℝ) (i : Fin n) :
    ∑ s, w s * AtilExt A s i = ∑ ρ, w (Sum.inl ρ) * A ρ i + w (Sum.inr i) := by
  rw [Fintype.sum_sum_type]
  have h1 : ∀ ρ, AtilExt A (Sum.inl ρ) i = A ρ i := fun _ => rfl
  have h2 : ∀ k, AtilExt A (Sum.inr k) i = if k = i then 1 else 0 := fun _ => rfl
  simp only [h1, h2, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma cglpL_extSumB {n : ℕ} {M : Type*} [Fintype M] (b : M → ℝ)
    (w : M ⊕ Fin n → ℝ) :
    ∑ s, w s * BtilExt (n := n) b s = ∑ ρ, w (Sum.inl ρ) * b ρ := by
  rw [Fintype.sum_sum_type]
  simp [BtilExt]

lemma cglpL_restrict {M : Type*} [Fintype M] [DecidableEq M] (MR : Finset M) (f : M → ℝ) :
    ∑ ρ, (if ρ ∈ MR then f ρ else 0) = ∑ ρ ∈ MR, f ρ := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

lemma cglpL_resSum {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M] (MR : Finset M)
    (R : Finset (Fin n)) (L : Fin n → M) (hL : ∀ k ∈ R, L k ∈ MR) (σ : M) (hσ : σ ∈ MR)
    (w : M → ℝ) (r : Fin n → ℝ) (c : ℝ) (f : M → ℝ) :
    ∑ ρ ∈ MR, (w ρ + ∑ k ∈ R, r k * (if L k = ρ then 1 else 0) +
        c * (if σ = ρ then 1 else 0)) * f ρ =
      ∑ ρ ∈ MR, w ρ * f ρ + ∑ k ∈ R, r k * f (L k) + c * f σ := by
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  · congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k hk => ?_
    simp [mul_ite, ite_mul, Finset.sum_ite_eq, hL k hk]
  · simp [mul_ite, ite_mul, Finset.sum_ite_eq, hσ]

theorem cglp_core {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (Nprime : Finset (Fin n))
    (hP : HasBoundRows Atil btil Nprime) (MR : Finset M) (R : Finset (Fin n)) (j : Fin n)
    (hj : j ∈ Nprime) (hjR : j ∈ R)
    (hMR : ∀ ρ ∉ MR, ∃ h ∉ R, (Atil ρ = Pi.single h 1 ∧ btil ρ = 0) ∨
      (Atil ρ = -Pi.single h 1 ∧ btil ρ = -1))
    (xbar : Fin n → ℝ) (hxbar : ∀ i ∉ R, xbar i = 0)
    (αR : Fin n → ℝ) (uR vR : M → ℝ) (u0R v0R βR : ℝ)
    (hfeas : IsCGLPRFeasible Atil btil MR R j αR uR u0R vR v0R βR) (hnorm : βR = 1 ∨ βR = -1)
    (hopt : ∀ (α' : Fin n → ℝ) (u' v' : M → ℝ) (u0' v0' β' : ℝ),
      IsCGLPRFeasible Atil btil MR R j α' u' u0' v' v0' β' → (β' = 1 ∨ β' = -1) →
        dotProduct αR xbar - βR ≤ dotProduct α' xbar - β') :
    ∃ (α : Fin n → ℝ) (u v : M ⊕ Fin n → ℝ),
      (∀ ρ : M, u (Sum.inl ρ) = (if ρ ∈ MR then uR ρ else 0) ∧
        v (Sum.inl ρ) = (if ρ ∈ MR then vR ρ else 0)) ∧
      (∀ i ∉ R, u (Sum.inr i) =
          (if Alpha1 Atil uR MR i < Alpha2 Atil vR MR i
            then Alpha2 Atil vR MR i - Alpha1 Atil uR MR i else 0) ∧
        v (Sum.inr i) =
          (if Alpha2 Atil vR MR i < Alpha1 Atil uR MR i
            then Alpha1 Atil uR MR i - Alpha2 Atil vR MR i else 0)) ∧
      (∀ i ∈ R, u (Sum.inr i) = 0 ∧ v (Sum.inr i) = 0) ∧
      (∀ i ∈ R, α i = αR i) ∧
      (∀ i ∉ R, α i = Alpha1 Atil uR MR i + u (Sum.inr i)) ∧
      IsCGLPFeasible (AtilExt Atil) (BtilExt btil) j α u u0R v v0R βR ∧
      ∀ (α' : Fin n → ℝ) (u' v' : M ⊕ Fin n → ℝ) (u0' v0' β' : ℝ),
        IsCGLPFeasible (AtilExt Atil) (BtilExt btil) j α' u' u0' v' v0' β' →
          (β' = 1 ∨ β' = -1) →
          dotProduct α xbar - βR ≤ dotProduct α' xbar - β' := by
  -- rows outside MR
  have hout : ∀ ρ ∉ MR, ∀ i ∈ R, Atil ρ i = 0 := by
    intro ρ hρ i hi
    obtain ⟨h, hh, hc | hc⟩ := hMR ρ hρ
    · rw [hc.1, Pi.single_apply, if_neg (by rintro rfl; exact hh hi)]
    · rw [hc.1, Pi.neg_apply, Pi.single_apply, if_neg (by rintro rfl; exact hh hi), neg_zero]
  have hbout : ∀ ρ ∉ MR, btil ρ ≤ 0 := by
    intro ρ hρ
    obtain ⟨h, hh, hc | hc⟩ := hMR ρ hρ
    · rw [hc.2]
    · rw [hc.2]; norm_num
  -- lower rows
  choose L hLA hLb using hP.1
  obtain ⟨σ, hσA, hσb⟩ := hP.2 j hj
  have hLin : ∀ k ∈ R, L k ∈ MR := by
    intro k hk
    by_contra hc
    have := hout (L k) hc k hk
    rw [hLA k] at this
    simp at this
  have hσin : σ ∈ MR := by
    by_contra hc
    have := hout σ hc j hjR
    rw [hσA] at this
    simp at this
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ := hfeas
  -- inside-MR sums
  have hsumM : ∀ (w : M → ℝ) (i : Fin n), i ∈ R →
      ∑ ρ, w ρ * Atil ρ i = ∑ ρ ∈ MR, w ρ * Atil ρ i := by
    intro w i hi
    rw [← cglpL_restrict MR]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    split_ifs with h
    · rfl
    · rw [hout ρ h i hi, mul_zero]
  -- objective equality
  have hobj : ∀ α : Fin n → ℝ, (∀ i ∈ R, α i = αR i) →
      dotProduct α xbar = dotProduct αR xbar := by
    intro α hα
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ R
    · rw [hα i hi]
    · rw [hxbar i hi, mul_zero, mul_zero]
  set A1 := fun i => Alpha1 Atil uR MR i with hA1
  set A2 := fun i => Alpha2 Atil vR MR i with hA2
  let uI : Fin n → ℝ := fun i => if i ∈ R then 0 else
    (if A1 i < A2 i then A2 i - A1 i else 0)
  let vI : Fin n → ℝ := fun i => if i ∈ R then 0 else
    (if A2 i < A1 i then A1 i - A2 i else 0)
  let u : M ⊕ Fin n → ℝ := Sum.elim (fun ρ => if ρ ∈ MR then uR ρ else 0) uI
  let v : M ⊕ Fin n → ℝ := Sum.elim (fun ρ => if ρ ∈ MR then vR ρ else 0) vI
  let α : Fin n → ℝ := fun i => if i ∈ R then αR i else A1 i + uI i
  have hαR : ∀ i ∈ R, α i = αR i := fun i hi => by simp [α, hi]
  refine ⟨α, u, v, fun ρ => ⟨rfl, rfl⟩, fun i hi => ?_, fun i hi => ?_, hαR,
    fun i hi => ?_, ?_, ?_⟩
  · simp [u, v, uI, vI, hi, A1, A2]
  · simp [u, v, uI, vI, hi]
  · simp [α, u, hi, A1]
  · -- feasibility
    have hu_sum : ∀ i, ∑ ρ, u (Sum.inl ρ) * Atil ρ i = A1 i := by
      intro i
      simp only [u, Sum.elim_inl, ite_mul, zero_mul, cglpL_restrict, hA1, Alpha1]
    have hv_sum : ∀ i, ∑ ρ, v (Sum.inl ρ) * Atil ρ i = A2 i := by
      intro i
      simp only [v, Sum.elim_inl, ite_mul, zero_mul, cglpL_restrict, hA2, Alpha2]
    refine ⟨fun i => ?_, fun i => ?_, ?_, ?_, ?_, ?_⟩
    · rw [cglpL_extSum, hu_sum]
      by_cases hi : i ∈ R
      · have := hf1 i hi
        simp only [α, u, uI, hi, if_true, Sum.elim_inr]
        simp only [hA1, Alpha1]
        linarith
      · have hij : i ≠ j := fun h => hi (h ▸ hjR)
        simp only [α, u, hi, if_false, Sum.elim_inr, hij]
        ring
    · rw [cglpL_extSum, hv_sum]
      by_cases hi : i ∈ R
      · have := hf2 i hi
        simp only [α, v, vI, hi, if_true, Sum.elim_inr]
        simp only [hA2, Alpha2]
        linarith
      · have hij : i ≠ j := fun h => hi (h ▸ hjR)
        simp only [α, v, uI, vI, hi, if_false, Sum.elim_inr, hij]
        split_ifs with h1 h2 h2 <;> first | linarith | ring
    · rw [cglpL_extSumB]
      simp only [u, Sum.elim_inl, ite_mul, zero_mul, cglpL_restrict]
      linarith
    · rw [cglpL_extSumB]
      simp only [v, Sum.elim_inl, ite_mul, zero_mul, cglpL_restrict]
      linarith
    · intro s
      rcases s with ρ | i
      · simp only [u, Sum.elim_inl, Pi.zero_apply]
        split_ifs
        · exact hf5 ρ
        · exact le_rfl
      · simp only [u, uI, Sum.elim_inr, Pi.zero_apply]
        split_ifs <;> linarith
    · intro s
      rcases s with ρ | i
      · simp only [v, Sum.elim_inl, Pi.zero_apply]
        split_ifs
        · exact hf6 ρ
        · exact le_rfl
      · simp only [v, vI, Sum.elim_inr, Pi.zero_apply]
        split_ifs <;> linarith
  · -- optimality
    intro α' u' v' u0' v0' β' hf hβ
    obtain ⟨g1, g2, g3, g4, g5, g6⟩ := hf
    rw [hobj α hαR]
    set U : ℝ := -∑ ρ, (if ρ ∈ MR then 0 else u' (Sum.inl ρ) * btil ρ) with hU
    set V : ℝ := -∑ ρ, (if ρ ∈ MR then 0 else v' (Sum.inl ρ) * btil ρ) with hV
    have hsplit : ∀ w : M → ℝ, ∑ ρ, w ρ * btil ρ =
        ∑ ρ ∈ MR, w ρ * btil ρ + ∑ ρ, (if ρ ∈ MR then 0 else w ρ * btil ρ) := by
      intro w
      rw [← cglpL_restrict MR, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      split_ifs <;> simp
    have hU0 : 0 ≤ U := by
      rw [hU, neg_nonneg]
      refine Finset.sum_nonpos fun ρ _ => ?_
      split_ifs with h
      · exact le_rfl
      · exact mul_nonpos_of_nonneg_of_nonpos (g5 (Sum.inl ρ)) (hbout ρ h)
    have hV0 : 0 ≤ V := by
      rw [hV, neg_nonneg]
      refine Finset.sum_nonpos fun ρ _ => ?_
      split_ifs with h
      · exact le_rfl
      · exact mul_nonpos_of_nonneg_of_nonpos (g6 (Sum.inl ρ)) (hbout ρ h)
    let u'' : M → ℝ := fun ρ => u' (Sum.inl ρ) +
      ∑ k ∈ R, u' (Sum.inr k) * (if L k = ρ then 1 else 0) + U * (if σ = ρ then 1 else 0)
    let v'' : M → ℝ := fun ρ => v' (Sum.inl ρ) +
      ∑ k ∈ R, v' (Sum.inr k) * (if L k = ρ then 1 else 0) +
        V * (if L j = ρ then 1 else 0)
    have hLsum : ∀ (r : Fin n → ℝ) (i : Fin n), i ∈ R →
        ∑ k ∈ R, r k * Atil (L k) i = r i := by
      intro r i hi
      simp [hLA, Pi.single_apply, mul_ite, Finset.sum_ite_eq, hi]
    have hLsumB : ∀ (r : Fin n → ℝ), ∑ k ∈ R, r k * btil (L k) = 0 := by
      intro r
      simp [hLb]
    have hfeasR : IsCGLPRFeasible Atil btil MR R j α' u'' (u0' - U) v'' (v0' - V) β' := by
      refine ⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_, ?_, ?_⟩
      · have e := g1 i
        rw [cglpL_extSum, hsumM _ i hi] at e
        have := cglpL_resSum MR R L hLin σ hσin (fun ρ => u' (Sum.inl ρ))
          (fun k => u' (Sum.inr k)) U (fun ρ => Atil ρ i)
        simp only [u''] at this ⊢
        rw [this, hLsum (fun k => u' (Sum.inr k)) i hi, hσA]
        simp only [Pi.neg_apply, Pi.single_apply]
        by_cases hij : i = j
        · subst hij; simp only [if_true] at e ⊢; linarith
        · simp only [hij, if_false] at e ⊢; linarith
      · have e := g2 i
        rw [cglpL_extSum, hsumM _ i hi] at e
        have := cglpL_resSum MR R L hLin (L j) (hLin j hjR) (fun ρ => v' (Sum.inl ρ))
          (fun k => v' (Sum.inr k)) V (fun ρ => Atil ρ i)
        simp only [v''] at this ⊢
        rw [this, hLsum (fun k => v' (Sum.inr k)) i hi, hLA j]
        simp only [Pi.single_apply]
        by_cases hij : i = j
        · subst hij; simp only [if_true] at e ⊢; linarith
        · simp only [hij, if_false] at e ⊢; linarith
      · have := cglpL_resSum MR R L hLin σ hσin (fun ρ => u' (Sum.inl ρ))
          (fun k => u' (Sum.inr k)) U btil
        simp only [u''] at this ⊢
        rw [this, hLsumB, hσb]
        have e := hsplit (fun ρ => u' (Sum.inl ρ))
        rw [cglpL_extSumB] at g3
        linarith
      · have := cglpL_resSum MR R L hLin (L j) (hLin j hjR) (fun ρ => v' (Sum.inl ρ))
          (fun k => v' (Sum.inr k)) V btil
        simp only [v''] at this ⊢
        rw [this, hLsumB, hLb]
        have e := hsplit (fun ρ => v' (Sum.inl ρ))
        rw [cglpL_extSumB] at g4
        linarith
      · intro ρ
        simp only [u'', Pi.zero_apply]
        have h1 := g5 (Sum.inl ρ)
        have h2 : 0 ≤ ∑ k ∈ R, u' (Sum.inr k) * (if L k = ρ then (1:ℝ) else 0) :=
          Finset.sum_nonneg fun k _ => mul_nonneg (g5 (Sum.inr k)) (by split_ifs <;> norm_num)
        have h3 : 0 ≤ U * (if σ = ρ then (1:ℝ) else 0) :=
          mul_nonneg hU0 (by split_ifs <;> norm_num)
        simp only [Pi.zero_apply] at h1
        linarith
      · intro ρ
        simp only [v'', Pi.zero_apply]
        have h1 := g6 (Sum.inl ρ)
        have h2 : 0 ≤ ∑ k ∈ R, v' (Sum.inr k) * (if L k = ρ then (1:ℝ) else 0) :=
          Finset.sum_nonneg fun k _ => mul_nonneg (g6 (Sum.inr k)) (by split_ifs <;> norm_num)
        have h3 : 0 ≤ V * (if L j = ρ then (1:ℝ) else 0) :=
          mul_nonneg hV0 (by split_ifs <;> norm_num)
        simp only [Pi.zero_apply] at h1
        linarith
    exact hopt α' u'' v'' (u0' - U) (v0' - V) β' hfeasR hβ

end Disjunctive.LiftProject

open Disjunctive.LiftProject


theorem solution {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (Nprime : Finset (Fin n))
    (hP : HasBoundRows Atil btil Nprime) (MR : Finset M) (R : Finset (Fin n)) (j : Fin n)
    (hj : j ∈ Nprime) (hjR : j ∈ R)
    (hMR : ∀ ρ ∉ MR, ∃ h ∉ R, (Atil ρ = Pi.single h 1 ∧ btil ρ = 0) ∨
      (Atil ρ = -Pi.single h 1 ∧ btil ρ = -1))
    (xbar : Fin n → ℝ) (hxbar : ∀ i ∉ R, xbar i = 0)
    (αR : Fin n → ℝ) (uR vR : M → ℝ) (u0R v0R βR : ℝ)
    (hfeas : IsCGLPRFeasible Atil btil MR R j αR uR u0R vR v0R βR) (hnorm : βR = 1 ∨ βR = -1)
    (hopt : ∀ (α' : Fin n → ℝ) (u' v' : M → ℝ) (u0' v0' β' : ℝ),
      IsCGLPRFeasible Atil btil MR R j α' u' u0' v' v0' β' → (β' = 1 ∨ β' = -1) →
        dotProduct αR xbar - βR ≤ dotProduct α' xbar - β') :
    ∃ (α : Fin n → ℝ) (u v : M ⊕ Fin n → ℝ),
      (∀ ρ : M, u (Sum.inl ρ) = (if ρ ∈ MR then uR ρ else 0) ∧
        v (Sum.inl ρ) = (if ρ ∈ MR then vR ρ else 0)) ∧
      (∀ i ∉ R, u (Sum.inr i) =
          (if Alpha1 Atil uR MR i < Alpha2 Atil vR MR i
            then Alpha2 Atil vR MR i - Alpha1 Atil uR MR i else 0) ∧
        v (Sum.inr i) =
          (if Alpha2 Atil vR MR i < Alpha1 Atil uR MR i
            then Alpha1 Atil uR MR i - Alpha2 Atil vR MR i else 0)) ∧
      (∀ i ∈ R, u (Sum.inr i) = 0 ∧ v (Sum.inr i) = 0) ∧
      (∀ i ∈ R, α i = αR i) ∧
      (∀ i ∉ R, α i = Alpha1 Atil uR MR i + u (Sum.inr i)) ∧
      IsCGLPFeasible (AtilExt Atil) (BtilExt btil) j α u u0R v v0R βR ∧
      ∀ (α' : Fin n → ℝ) (u' v' : M ⊕ Fin n → ℝ) (u0' v0' β' : ℝ),
        IsCGLPFeasible (AtilExt Atil) (BtilExt btil) j α' u' u0' v' v0' β' →
          (β' = 1 ∨ β' = -1) →
          dotProduct α xbar - βR ≤ dotProduct α' xbar - β' := by
  exact cglp_core Atil btil Nprime hP MR R j hj hjR hMR xbar hxbar αR uR vR u0R v0R βR hfeas hnorm hopt
