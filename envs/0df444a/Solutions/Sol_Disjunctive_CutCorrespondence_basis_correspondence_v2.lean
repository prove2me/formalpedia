-- Prove2me | solution 1 for Disjunctive.CutCorrespondence.basis_correspondence_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T23:11:46.636993+00:00
-- url     : https://prove2.me/submissions/132e85e2-c243-4b11-9a2e-00fa7d8f9bae

import Mathlib
import Definitions.Def_Disjunctive_CutCorrespondence_Cglp_v2
import Definitions.Def_Disjunctive_CutCorrespondence_Tableau_v2



namespace Disjunctive.CutCorrespondence

lemma bc_feas {n : ℕ} {M : Type*} [Fintype M] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ)
    (k : Fin n) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ)
    (h : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) :
    IsCGLPKFeasible Atil btil k α u u0 v v0 β := h.1

/-- Disjointness of the basic index sets. -/
lemma bc_disjoint {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (k : Fin n) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ)
    (β : ℝ) (M1 M2 : Finset M)
    (hf : IsCGLPKFeasible Atil btil k α u u0 v v0 β) (hu0 : 0 < u0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hbasis : IsCGLPKBasis Atil btil k M1 M2) : Disjoint M1 M2 := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -⟩ := hf
  rw [Finset.disjoint_left]
  intro ρ hρ1 hρ2
  have key := hbasis.2 (fun i => α i - (1/2) * Atil ρ i)
    (fun r => u r - if r = ρ then 1/2 else 0) u0
    (fun r => v r - if r = ρ then 1/2 else 0) v0 (β - btil ρ / 2)
    (by
      intro i
      have := h1 i
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linarith)
    (by
      intro i
      have := h2 i
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linarith)
    (by
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linarith)
    (by
      simp only [sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      linarith)
    (by
      simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      linarith)
    (by
      intro r hr
      have hne : r ≠ ρ := fun h => hr (h ▸ hρ1)
      simp [hu_supp r hr, hne])
    (by
      intro r hr
      have hne : r ≠ ρ := fun h => hr (h ▸ hρ2)
      simp [hv_supp r hr, hne])
  linarith [key.2.2.1]

/-- Nonsingularity of `Ã_J` for any enumeration of a subset of `M1 ∪ M2`. -/
lemma bc_det {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M] (Atil : Matrix M (Fin n) ℝ)
    (btil : M → ℝ) (k : Fin n) (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ)
    (β : ℝ) (M1 M2 : Finset M)
    (hf : IsCGLPKFeasible Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hbasis : IsCGLPKBasis Atil btil k M1 M2) (hdisj : Disjoint M1 M2)
    (ι : Fin n → M) (hι : Function.Injective ι) (hιJ : ∀ i, ι i ∈ M1 ∪ M2) :
    IsUnit (Ahat Atil ι).det := by
  obtain ⟨h1, h2, h3, h4, h5, -, -, -, -⟩ := hf
  rw [isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨y, hy0, hy⟩ := (Matrix.exists_vecMul_eq_zero_iff).2 hdet
  -- λ on rows
  set lam : M → ℝ := fun r => ∑ i, if ι i = r then y i else 0 with hlam
  have hsum : ∀ g : M → ℝ, ∑ r, lam r * g r = ∑ i, y i * g (ι i) := by
    intro g
    simp only [hlam, Finset.sum_mul, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp [Finset.sum_ite_eq]
  have hlamι : ∀ i, lam (ι i) = y i := by
    intro i
    simp only [hlam]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hι.ne hj]
    · simp
  have hlam_out : ∀ r, r ∉ M1 ∪ M2 → lam r = 0 := by
    intro r hr
    simp only [hlam]
    apply Finset.sum_eq_zero
    intro i _
    have : ι i ≠ r := fun h => hr (h ▸ hιJ i)
    simp [this]
  have hlamA : ∀ i, ∑ r, lam r * Atil r i = 0 := by
    intro i
    rw [hsum (fun r => Atil r i)]
    have := congrFun hy i
    simpa [Matrix.vecMul, dotProduct, Ahat] using this
  set l1 : M → ℝ := fun r => if r ∈ M1 then lam r else 0 with hl1
  set l2 : M → ℝ := fun r => if r ∈ M2 then -lam r else 0 with hl2
  have h12 : ∀ r, l1 r - l2 r = lam r := by
    intro r
    simp only [hl1, hl2]
    by_cases hr1 : r ∈ M1
    · have hr2 : r ∉ M2 := Finset.disjoint_left.1 hdisj hr1
      simp [hr1, hr2]
    · by_cases hr2 : r ∈ M2
      · simp [hr1, hr2]
      · simp [hr1, hr2, hlam_out r (by simp [hr1, hr2])]
  set L := ∑ r, lam r * btil r with hL
  set S := (∑ r, l1 r) + ∑ r, l2 r with hS
  have hsub : ∀ g : M → ℝ, ∑ r, l1 r * g r - ∑ r, l2 r * g r = ∑ r, lam r * g r := by
    intro g
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [← h12 r]; ring
  have huvA : ∀ i, ∑ r, u r * Atil r i - ∑ r, v r * Atil r i =
      (if i = k then u0 else 0) + (if i = k then v0 else 0) := by
    intro i; have := h1 i; have := h2 i; linarith
  have huvb : ∑ r, u r * btil r - ∑ r, v r * btil r = v0 := by linarith
  have key := hbasis.2
    (fun i => ∑ r, (l1 r - S * u r) * Atil r i - (if i = k then -L - S * u0 else 0))
    (fun r => l1 r - S * u r) (-L - S * u0) (fun r => l2 r - S * v r) (L - S * v0)
    (∑ r, (l1 r - S * u r) * btil r)
    (by intro i; ring)
    (by
      intro i
      have e := huvA i
      have e2 := hsub (fun r => Atil r i)
      have e3 := hlamA i
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at e2 ⊢
      split_ifs at e ⊢ with hik
      · linear_combination e2 + e3 - S * e
      · linear_combination e2 + e3 - S * e)
    (by ring)
    (by
      have e2 := hsub btil
      simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at e2 ⊢
      linear_combination -e2 + S * huvb)
    (by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      linear_combination (-S) * h5)
    (by
      intro r hr
      simp [hl1, hr, hu_supp r hr])
    (by
      intro r hr
      simp [hl2, hr, hv_supp r hr])
  obtain ⟨-, hdu, hdu0, hdv, hdv0, -⟩ := key
  have hS0 : S = 0 := by
    have : S * (u0 + v0) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · linarith
  apply hy0
  funext i
  rw [← hlamι i, ← h12 (ι i)]
  have a1 := congrFun hdu (ι i)
  have a2 := congrFun hdv (ι i)
  simp only [hS0, zero_mul, sub_zero, Pi.zero_apply] at a1 a2
  simp [a1, a2]

theorem bc_core {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (Nprime : Finset (Fin n))
    (hsys : IsMixedZeroOneSystem Atil btil Nprime) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hbasis : IsCGLPKBasis Atil btil k M1 M2) :
    Disjoint M1 M2 ∧ IsNonsingularSubmatrix Atil (M1 ∪ M2) := by
  have hf := bc_feas Atil btil k α u u0 v v0 β hbasic
  have hdisj := bc_disjoint Atil btil k α u u0 v v0 β M1 M2 hf hu0 hu_supp hv_supp hbasis
  refine ⟨hdisj, ?_⟩
  have hcard : (M1 ∪ M2).card = n := by
    rw [Finset.card_union_of_disjoint hdisj]; exact hbasis.1
  have e : Fin n ≃ (M1 ∪ M2 : Finset M) := (finCongr hcard.symm).trans
    (M1 ∪ M2).equivFin.symm
  refine ⟨fun i => (e i).1, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · ext r
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hr; exact ⟨e.symm ⟨r, hr⟩, by rw [Equiv.apply_symm_apply]⟩
  · have hinj : Function.Injective (fun i => (e i).1) :=
      fun i j hij => e.injective (Subtype.ext hij)
    have hmem : ∀ i, (fun i => (e i).1) i ∈ M1 ∪ M2 := fun i => (e i).2
    convert bc_det Atil btil k α u u0 v v0 β M1 M2 hf hu0 hv0 hu_supp hv_supp hbasis hdisj
      (fun i => (e i).1) hinj hmem using 2

end Disjunctive.CutCorrespondence

open Disjunctive.CutCorrespondence


theorem solution {n : ℕ} {M : Type*} [Fintype M] [DecidableEq M]
    [DecidableEq (Fin n)] (Atil : Matrix M (Fin n) ℝ) (btil : M → ℝ) (Nprime : Finset (Fin n))
    (hsys : IsMixedZeroOneSystem Atil btil Nprime) (k : Fin n)
    (α : Fin n → ℝ) (u : M → ℝ) (u0 : ℝ) (v : M → ℝ) (v0 : ℝ) (β : ℝ) (M1 M2 : Finset M)
    (hbasic : IsBasicCGLPKSolution Atil btil k α u u0 v v0 β) (hu0 : 0 < u0) (hv0 : 0 < v0)
    (hu_supp : ∀ ρ ∉ M1, u ρ = 0) (hv_supp : ∀ ρ ∉ M2, v ρ = 0)
    (hbasis : IsCGLPKBasis Atil btil k M1 M2) :
    Disjoint M1 M2 ∧ IsNonsingularSubmatrix Atil (M1 ∪ M2) := by
  exact bc_core Atil btil Nprime hsys k α u u0 v v0 β M1 M2 hbasic hu0 hv0 hu_supp hv_supp hbasis
