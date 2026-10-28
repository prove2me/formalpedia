-- Prove2me | solution 1 for DynRiskEq.Welfare.theorem_2_i_value
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:35:03.631382+00:00
-- url     : https://prove2.me/submissions/c119f322-f242-4a5a-858d-aaca7fc77607

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

namespace Aux_DRE2
open DynRiskEq.Welfare

lemma generic {𝓜 𝓚 : Type} [Fintype 𝓜] [Fintype 𝓚]
    (q : 𝓚 → 𝓜 → ℝ) (Y : 𝓜 → ℝ) (θ : ℝ) (γ : 𝓚 → ℝ) (hsum : ∑ k, γ k = 1)
    (hc : ∀ k, Compl (γ k) (θ - ∑ m, q k m * Y m)) :
    IsGreatest ((fun ν : 𝓜 → ℝ => ∑ m, ν m * Y m) '' convexHull ℝ (Set.range q)) θ ∧
      θ = ∑ m, (∑ k, γ k * q k m) * Y m := by
  have hval : ∑ m, (∑ k, γ k * q k m) * Y m = θ := by
    have e1 : ∑ m, (∑ k, γ k * q k m) * Y m = ∑ k, γ k * ∑ m, q k m * Y m := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
      ring
    have e2 : ∀ k, γ k * ∑ m, q k m * Y m = γ k * θ := by
      intro k
      have := (hc k).2.2
      linarith [mul_sub (γ k) θ (∑ m, q k m * Y m)]
    rw [e1, Finset.sum_congr rfl fun k _ => e2 k, ← Finset.sum_mul, hsum, one_mul]
  have hlin : IsLinearMap ℝ (fun ν : 𝓜 → ℝ => ∑ m, ν m * Y m) := by
    constructor
    · intro x y
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    · intro c x
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  refine ⟨⟨⟨fun m => ∑ k, γ k * q k m, ?_, hval⟩, ?_⟩, hval.symm⟩
  · have e : (fun m => ∑ k, γ k * q k m) = ∑ k, γ k • q k := by
      funext m; simp [Finset.sum_apply]
    rw [e]
    exact (convex_convexHull ℝ _).sum_mem (fun k _ => (hc k).1) hsum
      (fun k _ => subset_convexHull ℝ _ ⟨k, rfl⟩)
  · rintro _ ⟨ν, hν, rfl⟩
    have hsub : convexHull ℝ (Set.range q) ⊆ {w | (fun ν : 𝓜 → ℝ => ∑ m, ν m * Y m) w ≤ θ} := by
      refine convexHull_min ?_ (convex_halfSpace_le hlin θ)
      rintro _ ⟨k, rfl⟩
      have := (hc k).2.1
      show ∑ m, q k m * Y m ≤ θ
      linarith
    exact hsub hν

end Aux_DRE2

open DynRiskEq.Welfare in
theorem solution {H : ℕ} (T : Tree H) {A : Type} [Fintype A] [DecidableEq A]
    (M : Market T A) (K : T.Node → ℕ) (p : (n : T.Node) → Fin (K n) → T.Node → ℝ)
    (π : T.Node → ℝ) (α : (a : A) → T.Node → Vec (M.dX a)) (μ : T.Node → ℝ)
    (u : (a : A) → T.Node → Vec (M.dU a)) (x : (a : A) → T.Node → Vec (M.dX a))
    (W : A → T.Node → ℝ) (θa : A → T.Node → ℝ) (a : A) (γ : (n : T.Node) → Fin (K n) → ℝ)
    (hAE : AE T M K p π α μ u x W θa a γ) :
    ∀ n, ¬ IsLeaf T n →
      IsGreatest
        ((fun ν : ↥(T.children n) → ℝ =>
            ∑ m : ↥(T.children n), ν m * (Z T M π α μ u x W a m - W a m + θa a m)) ''
          riskSet T K p n)
        (θa a n) ∧
      θa a n = ∑ m ∈ T.children n,
        (∑ k, γ n k * p n k m) * (Z T M π α μ u x W a m - W a m + θa a m) := by
  intro n hn
  set Y : T.Node → ℝ := fun m => Z T M π α μ u x W a m - W a m + θa a m with hY
  have hsum : ∑ k, γ n k = 1 := by linarith [hAE.1 n hn]
  have hc : ∀ k, Compl (γ n k)
      (θa a n - ∑ m : ↥(T.children n), restrictChildren T (p n k) n m * Y m) := by
    intro k
    have := hAE.2.1 n hn k
    have e : ∑ m : ↥(T.children n), restrictChildren T (p n k) n m * Y m
        = ∑ m ∈ T.children n, p n k m * Y m :=
      Finset.sum_coe_sort (T.children n) (fun m => p n k m * Y m)
    rw [e]; exact this
  obtain ⟨h1, h2⟩ := Aux_DRE2.generic (fun k => restrictChildren T (p n k) n)
    (fun m : ↥(T.children n) => Y m) (θa a n) (γ n) hsum hc
  refine ⟨h1, ?_⟩
  rw [h2]
  exact Finset.sum_coe_sort (T.children n) (fun m => (∑ k, γ n k * p n k m) * Y m)
