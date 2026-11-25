-- Prove2me | solution 1 for FiniteLP.farkas_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:37:11.354057+00:00
-- url     : https://prove2.me/submissions/839cef84-b23a-4a31-bc3a-a3366e052c9a

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
public import Theorems.Thm_FiniteLP_toE_apply
public import Theorems.Thm_FiniteLP_inner_toE
public import Theorems.Thm_FiniteLP_fg_cone_isClosed
attribute [local simp] FiniteLP.toE_apply

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP
namespace FiniteLP
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ]
    (N : ι → κ → ℝ) (c : ι → ℝ)
    (hinfeas : ¬ ∃ x : κ → ℝ, (∀ j, 0 ≤ x j) ∧ (∀ i, c i ≤ ∑ j, N i j * x j)) :
    ∃ y : ι → ℝ, (∀ i, 0 ≤ y i) ∧ (∀ j, ∑ i, N i j * y i ≤ 0) ∧ 0 < ∑ i, c i * y i := by
  classical
  set g : (κ ⊕ ι) → EuclideanSpace ℝ ι :=
    Sum.elim (fun j => toE (fun i => N i j)) (fun i => toE (fun i' => if i' = i then (-1:ℝ) else 0)) with hg
  have hind : ∀ a : κ ⊕ ι, ∑ k, (if k = a then (1:ℝ) else 0) • g k = g a := by
    intro a; simp [ite_smul]
  set S : Set (EuclideanSpace ℝ ι) := {y | ∃ coeff : (κ ⊕ ι) → ℝ, (∀ k, 0 ≤ coeff k) ∧ ∑ k, coeff k • g k = y} with hS
  have hSclosed : IsClosed S := fg_cone_isClosed g
  let K : ProperCone ℝ (EuclideanSpace ℝ ι) :=
    { carrier := S
      zero_mem' := ⟨fun _ => 0, fun _ => le_refl 0, by simp⟩
      smul_mem' := by
        rintro t x ⟨coeff, hcoeff, rfl⟩
        exact ⟨fun k => (t : ℝ) * coeff k, fun k => mul_nonneg t.2 (hcoeff k), by
          rw [Finset.smul_sum]; apply Finset.sum_congr rfl; intro k _
          rw [← smul_smul]; rfl⟩
      add_mem' := by
        rintro x y ⟨c1, h1, rfl⟩ ⟨c2, h2, rfl⟩
        exact ⟨fun k => c1 k + c2 k, fun k => add_nonneg (h1 k) (h2 k), by
          rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; rw [add_smul]⟩
      isClosed' := hSclosed }
  have hcne : (toE c) ∉ K := by
    rintro ⟨coeff, hcoeff, hsum⟩
    apply hinfeas
    refine ⟨fun j => coeff (Sum.inl j), fun j => hcoeff _, ?_⟩
    intro i
    have hcoord := congrArg (fun z => z i) hsum
    simp only [toE_apply] at hcoord
    have hexp : (∑ k, coeff k • g k) i
        = (∑ j, coeff (Sum.inl j) * N i j) - coeff (Sum.inr i) := by
      rw [Fintype.sum_sum_type]
      simp [hg, EuclideanSpace, PiLp, Finset.sum_apply]
      ring
    have hcomm : ∑ j, N i j * coeff (Sum.inl j) = ∑ j, coeff (Sum.inl j) * N i j := by
      apply Finset.sum_congr rfl; intro j _; ring
    rw [hexp] at hcoord
    have hnn : 0 ≤ coeff (Sum.inr i) := hcoeff _
    linarith
  obtain ⟨y, hy1, hy2⟩ :=
    ProperCone.hyperplane_separation' K hcne
  refine ⟨fun i => -(y i), fun i => ?_, fun j => ?_, ?_⟩
  · have hmem : g (Sum.inr i) ∈ K := ⟨fun k => if k = Sum.inr i then 1 else 0, fun k => by positivity, hind _⟩
    have hh := hy1 _ hmem
    rw [hg] at hh; simp only [Sum.elim_inr] at hh
    rw [inner_toE] at hh
    have hval : ∑ i', (if i' = i then (-1:ℝ) else 0) * y i' = - y i := by
      rw [Finset.sum_eq_single i] <;> simp +contextual
    rw [hval] at hh
    change 0 ≤ - y i; linarith
  · have hmem : g (Sum.inl j) ∈ K := ⟨fun k => if k = Sum.inl j then 1 else 0, fun k => by positivity, hind _⟩
    have hh := hy1 _ hmem
    rw [hg] at hh; simp only [Sum.elim_inl] at hh
    rw [inner_toE] at hh
    have h2 : ∑ i, N i j * -(y i) = - ∑ i, (fun i => N i j) i * y i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h2]; linarith
  · rw [inner_toE] at hy2
    have h2 : ∑ i, c i * -(y i) = - ∑ i, c i * y i := by
      rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro i _; ring
    rw [h2]; linarith
end FiniteLP
