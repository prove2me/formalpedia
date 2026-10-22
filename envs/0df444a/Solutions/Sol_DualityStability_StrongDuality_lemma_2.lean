-- Prove2me | solution 1 for DualityStability.StrongDuality.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:52:39.387737+00:00
-- url     : https://prove2.me/submissions/882d1b86-5429-4c97-8f82-7a234994f86e

import Mathlib
import Definitions.Def_DualityStability_StrongDuality_Program
set_option autoImplicit false

open DualityStability.StrongDuality

variable {E E' F F' : Type*}
  [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] [T2Space E]
  [TopologicalSpace E'] [AddCommGroup E'] [Module ℝ E']
  [IsTopologicalAddGroup E'] [ContinuousSMul ℝ E'] [LocallyConvexSpace ℝ E'] [T2Space E']
  [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]
  [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F] [T2Space F]
  [TopologicalSpace F'] [AddCommGroup F'] [Module ℝ F']
  [IsTopologicalAddGroup F'] [ContinuousSMul ℝ F'] [LocallyConvexSpace ℝ F'] [T2Space F']

lemma ds_finite (p : Program E E' F F') (z : F) (x : E) (c : ℝ)
    (h : p.primalAt z x < (c : EReal)) :
    ∃ F1 G1 : ℝ, p.f x = (F1 : EReal) ∧ p.g (p.A x - z) = (G1 : EReal) ∧ F1 - G1 < c := by
  have hfb := p.f_no_neg_inf x
  have hgt := p.g_no_pos_inf (p.A x - z)
  have hneg : -(p.g (p.A x - z)) ≠ ⊥ := by
    intro h'
    apply hgt
    simpa using h'
  unfold Program.primalAt at h
  have hft : p.f x ≠ ⊤ := by
    intro hft
    rw [hft, sub_eq_add_neg, EReal.top_add_of_ne_bot hneg] at h
    exact absurd h (not_lt.2 le_top)
  have hgb : p.g (p.A x - z) ≠ ⊥ := by
    intro hgb
    rw [hgb, sub_eq_add_neg, EReal.neg_bot, EReal.add_top_of_ne_bot hfb] at h
    exact absurd h (not_lt.2 le_top)
  refine ⟨(p.f x).toReal, (p.g (p.A x - z)).toReal, (EReal.coe_toReal hft hfb).symm,
    (EReal.coe_toReal hgt hgb).symm, ?_⟩
  rw [← EReal.coe_lt_coe_iff]
  have e1 : p.f x = ((p.f x).toReal : EReal) := (EReal.coe_toReal hft hfb).symm
  have e2 : p.g (p.A x - z) = ((p.g (p.A x - z)).toReal : EReal) := (EReal.coe_toReal hgt hgb).symm
  rw [e1, e2, ← EReal.coe_sub] at h
  exact h

theorem solution (p : Program E E' F F') : EpiConvex p.h := by
  intro q1 hq1 q2 hq2 a b ha hb hab
  simp only [Set.mem_setOf_eq] at hq1 hq2 ⊢
  obtain ⟨z1, μ1⟩ := q1
  obtain ⟨z2, μ2⟩ := q2
  simp only at hq1 hq2 ⊢
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  set z := a • z1 + b • z2
  set M := a * μ1 + b * μ2
  have hε : ∀ ε : ℝ, 0 < ε → p.h z ≤ ((M + ε : ℝ) : EReal) := by
    intro ε hε
    have h1 : p.h z1 < ((μ1 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hq1 (EReal.coe_lt_coe_iff.2 (by linarith))
    have h2 : p.h z2 < ((μ2 + ε : ℝ) : EReal) :=
      lt_of_le_of_lt hq2 (EReal.coe_lt_coe_iff.2 (by linarith))
    unfold Program.h at h1 h2
    obtain ⟨x1, hx1⟩ := iInf_lt_iff.1 h1
    obtain ⟨x2, hx2⟩ := iInf_lt_iff.1 h2
    obtain ⟨F1, G1, hF1, hG1, hFG1⟩ := ds_finite p z1 x1 _ hx1
    obtain ⟨F2, G2, hF2, hG2, hFG2⟩ := ds_finite p z2 x2 _ hx2
    have hfx : p.f (a • x1 + b • x2) ≤ ((a * F1 + b * F2 : ℝ) : EReal) := by
      have := p.f_convex (show (x1, F1) ∈ {q : E × ℝ | p.f q.1 ≤ (q.2 : EReal)} from by
          simp only [Set.mem_setOf_eq]; rw [hF1])
        (show (x2, F2) ∈ {q : E × ℝ | p.f q.1 ≤ (q.2 : EReal)} from by
          simp only [Set.mem_setOf_eq]; rw [hF2]) ha hb hab
      simpa using this
    have hgy : -(p.g (p.A (a • x1 + b • x2) - z)) ≤ ((-(a * G1 + b * G2) : ℝ) : EReal) := by
      have hy : p.A (a • x1 + b • x2) - z = a • (p.A x1 - z1) + b • (p.A x2 - z2) := by
        simp only [map_add, map_smul, z]
        module
      have := p.g_concave (show (p.A x1 - z1, -G1) ∈ {q : F × ℝ | (fun y => -p.g y) q.1 ≤ (q.2 : EReal)} from by
          simp only [Set.mem_setOf_eq]; rw [hG1]; simp)
        (show (p.A x2 - z2, -G2) ∈ {q : F × ℝ | (fun y => -p.g y) q.1 ≤ (q.2 : EReal)} from by
          simp only [Set.mem_setOf_eq]; rw [hG2]; simp) ha hb hab
      rw [hy]
      simp only [Prod.smul_mk, Prod.mk_add_mk, Set.mem_setOf_eq, smul_eq_mul] at this
      refine this.trans (EReal.coe_le_coe_iff.2 (le_of_eq (by ring)))
    have hprim : p.primalAt z (a • x1 + b • x2) ≤ ((a * (F1 - G1) + b * (F2 - G2) : ℝ) : EReal) := by
      unfold Program.primalAt
      rw [sub_eq_add_neg]
      calc p.f (a • x1 + b • x2) + -(p.g (p.A (a • x1 + b • x2) - z))
          ≤ ((a * F1 + b * F2 : ℝ) : EReal) + ((-(a * G1 + b * G2) : ℝ) : EReal) := add_le_add hfx hgy
        _ = ((a * (F1 - G1) + b * (F2 - G2) : ℝ) : EReal) := by
          rw [← EReal.coe_add]; congr 1; ring
    have hbound : a * (F1 - G1) + b * (F2 - G2) ≤ M + ε := by
      have h3 : a * (F1 - G1) ≤ a * (μ1 + ε) := mul_le_mul_of_nonneg_left hFG1.le ha
      have h4 : b * (F2 - G2) ≤ b * (μ2 + ε) := mul_le_mul_of_nonneg_left hFG2.le hb
      have : a * (μ1 + ε) + b * (μ2 + ε) = M + ε := by
        simp only [M]; have : a + b = 1 := hab; nlinarith
      linarith
    calc p.h z ≤ p.primalAt z (a • x1 + b • x2) := iInf_le _ _
      _ ≤ _ := hprim
      _ ≤ _ := EReal.coe_le_coe_iff.2 hbound
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.1 hc
  have hr : M < r := EReal.coe_lt_coe_iff.1 hr1
  have := hε (r - M) (by linarith)
  have e : M + (r - M) = r := by ring
  rw [e] at this
  exact this.trans hr2.le
