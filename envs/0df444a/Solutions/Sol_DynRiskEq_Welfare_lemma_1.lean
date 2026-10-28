-- Prove2me | solution 1 for DynRiskEq.Welfare.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:32:39.647707+00:00
-- url     : https://prove2.me/submissions/d87f4338-5708-433d-8469-46671830666b

import Mathlib
import Definitions.Def_DynRiskEq_Welfare_Model

open StochasticProg.Multistage FirstOrderOpt.ConvexTheory
open scoped RealInnerProductSpace

open DynRiskEq.Welfare in
theorem solution {𝓜 𝓚 : Type} [Fintype 𝓜] [Fintype 𝓚] [Nonempty 𝓚]
    (p : 𝓚 → 𝓜 → ℝ) (Zv : 𝓜 → ℝ) (θ : ℝ) :
    (θ = sSup ((fun μ : 𝓜 → ℝ => ∑ m, μ m * Zv m) '' convexHull ℝ (Set.range p)) ↔
      ∃ γ : 𝓚 → ℝ, ∑ k, γ k = 1 ∧ ∀ k, Compl (γ k) (θ - ∑ m, p k m * Zv m)) ∧
    ∀ γ : 𝓚 → ℝ, (∑ k, γ k = 1 ∧ ∀ k, Compl (γ k) (θ - ∑ m, p k m * Zv m)) →
      (fun m => ∑ k, γ k * p k m) ∈ convexHull ℝ (Set.range p) ∧
      ∑ m, (∑ k, γ k * p k m) * Zv m =
        sSup ((fun μ : 𝓜 → ℝ => ∑ m, μ m * Zv m) '' convexHull ℝ (Set.range p)) := by
  classical
  set Lf : (𝓜 → ℝ) → ℝ := fun μ => ∑ m, μ m * Zv m with hLf
  set Lk : 𝓚 → ℝ := fun k => ∑ m, p k m * Zv m with hLk
  have hne : (Finset.univ : Finset 𝓚).Nonempty := Finset.univ_nonempty
  set Mx := Finset.univ.sup' hne Lk with hMx
  obtain ⟨ks, -, hks⟩ := Finset.exists_max_image Finset.univ Lk hne
  have hLks : Lk ks = Mx := le_antisymm (Finset.le_sup' Lk (Finset.mem_univ ks))
    (Finset.sup'_le hne Lk fun k _ => hks k (Finset.mem_univ k))
  have hlin : IsLinearMap ℝ Lf := by
    constructor
    · intro x y
      simp only [hLf, Pi.add_apply, add_mul, Finset.sum_add_distrib]
    · intro c x
      simp only [hLf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  have hG : IsGreatest (Lf '' convexHull ℝ (Set.range p)) Mx := by
    refine ⟨⟨p ks, subset_convexHull ℝ _ ⟨ks, rfl⟩, hLks⟩, ?_⟩
    rintro _ ⟨μ, hμ, rfl⟩
    have hsub : convexHull ℝ (Set.range p) ⊆ {w | Lf w ≤ Mx} := by
      refine convexHull_min ?_ (convex_halfSpace_le hlin Mx)
      rintro _ ⟨k, rfl⟩
      exact Finset.le_sup' Lk (Finset.mem_univ k)
    exact hsub hμ
  have hS : sSup (Lf '' convexHull ℝ (Set.range p)) = Mx := hG.csSup_eq
  change (θ = sSup (Lf '' convexHull ℝ (Set.range p)) ↔ _) ∧ ∀ γ : 𝓚 → ℝ, _ → _ ∧
    ∑ m, (∑ k, γ k * p k m) * Zv m = sSup (Lf '' convexHull ℝ (Set.range p))
  rw [hS]
  have back : ∀ γ : 𝓚 → ℝ, (∑ k, γ k = 1 ∧ ∀ k, Compl (γ k) (θ - Lk k)) → θ = Mx := by
    rintro γ ⟨hsum, hc⟩
    obtain ⟨k, hk⟩ : ∃ k, γ k ≠ 0 := by
      by_contra hall
      push Not at hall
      simp [hall] at hsum
    have h1 : θ = Lk k := by
      have := (hc k).2.2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h hk
      · linarith
    have h2 : Mx ≤ θ := Finset.sup'_le hne Lk fun k' _ => by linarith [(hc k').2.1]
    have h3 : Lk k ≤ Mx := Finset.le_sup' Lk (Finset.mem_univ k)
    linarith
  refine ⟨⟨fun hθ => ?_, fun ⟨γ, hγ⟩ => back γ hγ⟩, fun γ hγ => ⟨?_, ?_⟩⟩
  · refine ⟨fun k => if k = ks then 1 else 0, by simp, fun k => ⟨?_, ?_, ?_⟩⟩
    · show 0 ≤ (if k = ks then (1:ℝ) else 0)
      split_ifs <;> norm_num
    · have : Lk k ≤ Mx := Finset.le_sup' Lk (Finset.mem_univ k)
      change 0 ≤ θ - Lk k
      linarith
    · by_cases h : k = ks
      · subst h; simp only [if_true]; change 1 * (θ - Lk k) = 0; rw [hθ, ← hLks]; ring
      · simp [h]
  · have e : (fun m => ∑ k, γ k * p k m) = ∑ k, γ k • p k := by
      funext m; simp [Finset.sum_apply]
    rw [e]
    exact (convex_convexHull ℝ _).sum_mem (fun k _ => (hγ.2 k).1) hγ.1
      (fun k _ => subset_convexHull ℝ _ ⟨k, rfl⟩)
  · have hθ := back γ hγ
    rw [← hθ]
    have e1 : ∑ m, (∑ k, γ k * p k m) * Zv m = ∑ k, γ k * Lk k := by
      simp only [hLk, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
      ring
    have e2 : ∀ k, γ k * Lk k = γ k * θ := by
      intro k
      have := (hγ.2 k).2.2
      change γ k * (θ - Lk k) = 0 at this
      linarith [mul_sub (γ k) θ (Lk k)]
    rw [e1, Finset.sum_congr rfl fun k _ => e2 k, ← Finset.sum_mul, hγ.1, one_mul]
