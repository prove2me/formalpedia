-- Prove2me | solution 1 for GenNewtonSubgrad.ProxReg.remark_6_5
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T21:18:53.736394+00:00
-- url     : https://prove2.me/submissions/23c25c84-2682-4aba-aad6-d6ba8be6b795

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_i
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_iii
import Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_4
import Theorems.Thm_GenNewtonSubgrad_ProxReg_scalarization_2_11

open Filter Topology
open scoped InnerProductSpace

open GenNewtonSubgrad.ProxReg in
theorem solution {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar vbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ)
    (hreg : IsContProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ W ∈ 𝓝 (xbar + lam • vbar), ∀ x ∈ W, (prox φ lam x).Nonempty ∧ ∀ p ∈ prox φ lam x,
        HasGradientAt (fun z => (moreauEnv φ lam z).toReal) (lam⁻¹ • (x - p)) x ∧
        (∀ d : EuclideanSpace ℝ (Fin n),
          -(lam⁻¹ • (x - p)) ∈ secondSubdiff φ (x - lam • (lam⁻¹ • (x - p))) (lam⁻¹ • (x - p))
              (lam • (lam⁻¹ • (x - p)) + d) ↔
            -gradient (fun z => (moreauEnv φ lam z).toReal) x ∈
              coderiv (sv (gradient (fun z => (moreauEnv φ lam z).toReal))) x
                (gradient (fun z => (moreauEnv φ lam z).toReal) x) d) ∧
        (∀ d : EuclideanSpace ℝ (Fin n),
          coderiv (sv (gradient (fun z => (moreauEnv φ lam z).toReal))) x
              (gradient (fun z => (moreauEnv φ lam z).toReal) x) d =
            NonconvexSplitting.Shared.LimitingSubdiff
              (fun z => ((⟪d, gradient (fun w => (moreauEnv φ lam w).toReal) z⟫_ℝ : ℝ) : EReal)) x)
          := by
  obtain ⟨l1, hl1, hl1r, H1⟩ := lemma_6_3_i φ xbar vbar r ε hproper hbdd hreg
  obtain ⟨l3, hl3, hl3r, H3⟩ := lemma_6_3_iii φ xbar vbar r ε hproper hbdd hreg
  obtain ⟨l4, hl4, hl4r, H4⟩ := lemma_6_4 φ xbar vbar r ε hproper hbdd hreg
  refine ⟨min l1 (min l3 l4), lt_min hl1 (lt_min hl3 hl4),
    (min_le_left _ _).trans hl1r, fun lam hlam hlt => ?_⟩
  have hlt1 : lam < l1 := lt_of_lt_of_le hlt (min_le_left _ _)
  have hlt3 : lam < l3 := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_left _ _))
  have hlt4 : lam < l4 := lt_of_lt_of_le hlt ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨W1, hW1, -, -, -, L, hL⟩ := H1 lam hlam hlt1
  obtain ⟨W3, hW3, V3, -, hW3p, -⟩ := H3 lam hlam hlt3
  obtain ⟨W4, hW4, -, hW4c⟩ := H4 lam hlam hlt4
  set ψ : EuclideanSpace ℝ (Fin n) → ℝ := fun z => (moreauEnv φ lam z).toReal with hψ
  refine ⟨interior (W1 ∩ W3 ∩ W4), interior_mem_nhds.2 (inter_mem (inter_mem hW1 hW3) hW4),
    fun x hx => ?_⟩
  have hxW : x ∈ W1 ∩ W3 ∩ W4 := interior_subset hx
  have hW1x : W1 ∈ 𝓝 x := mem_of_superset (isOpen_interior.mem_nhds hx)
    (interior_subset.trans (fun y hy => hy.1.1))
  obtain ⟨hne, hgr⟩ := hW3p x hxW.1.2
  refine ⟨hne, fun p hp => ⟨hgr p hp, fun d => ?_, fun d => ?_⟩⟩
  · have hg : gradient ψ x = lam⁻¹ • (x - p) := (hgr p hp).gradient
    have := hW4c x hxW.2 d (-(lam⁻¹ • (x - p)))
    rw [hg] at this ⊢
    rw [this, smul_neg, sub_neg_eq_add, add_comm]
  · exact scalarization_2_11 (gradient ψ) x ⟨W1, hW1x, L, hL⟩ d
