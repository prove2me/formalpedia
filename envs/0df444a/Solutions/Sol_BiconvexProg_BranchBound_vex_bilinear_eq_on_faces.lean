-- Prove2me | solution 1 for BiconvexProg.BranchBound.vex_bilinear_eq_on_faces
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:33:25.70418+00:00
-- url     : https://prove2.me/submissions/d7982324-e460-4daa-9efb-ba04b53a6014

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_problem

namespace BiconvexProg.BranchBound

lemma aux_vbf_frontier {a b c d : ℝ} {p : ℝ × ℝ}
    (hp : p ∈ frontier (Set.Icc a b ×ˢ Set.Icc c d)) :
    (a ≤ p.1 ∧ p.1 ≤ b ∧ c ≤ p.2 ∧ p.2 ≤ d) ∧
      (p.1 = a ∨ p.1 = b ∨ p.2 = c ∨ p.2 = d) := by
  have hcl : IsClosed (Set.Icc a b ×ˢ Set.Icc c d) := isClosed_Icc.prod isClosed_Icc
  rw [frontier, hcl.closure_eq, interior_prod_eq, interior_Icc, interior_Icc] at hp
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, hn⟩ := hp
  refine ⟨⟨h1, h2, h3, h4⟩, ?_⟩
  by_contra hc
  simp only [not_or] at hc
  obtain ⟨e1, e2, e3, e4⟩ := hc
  exact hn ⟨⟨lt_of_le_of_ne h1 (Ne.symm e1), lt_of_le_of_ne h2 e2⟩,
    lt_of_le_of_ne h3 (Ne.symm e3), lt_of_le_of_ne h4 e4⟩

end BiconvexProg.BranchBound

open BiconvexProg.BranchBound

theorem solution {n : ℕ} (Ω : Box n) (z : (Fin n → ℝ) × (Fin n → ℝ))
    (hface : ∀ i, (z.1 i, z.2 i) ∈ frontier (Ω.rect i)) :
    convexEnvelope Ω.toSet bilin z = bilin z := by
  classical
  have hF := fun i => aux_vbf_frontier (hface i)
  have hz : z ∈ Ω.toSet :=
    ⟨⟨fun i => (hF i).1.1, fun i => (hF i).1.2.1⟩,
      fun i => (hF i).1.2.2.1, fun i => (hF i).1.2.2.2⟩
  let P : Fin n → Prop := fun i => z.1 i = Ω.l i ∨ z.2 i = Ω.m i
  let h : Fin n → ℝ → ℝ → ℝ := fun i x y =>
    if P i then Ω.m i * x + Ω.l i * y - Ω.l i * Ω.m i
    else Ω.M i * x + Ω.L i * y - Ω.L i * Ω.M i
  let g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ := fun w => ∑ i, h i (w.1 i) (w.2 i)
  have hconv : ConvexOn ℝ Ω.toSet g := by
    refine ⟨(convex_Icc _ _).prod (convex_Icc _ _), ?_⟩
    intro u _ v _ a b _ _ hab
    apply le_of_eq
    simp only [g, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [h, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    split_ifs
    · linear_combination (Ω.l i * Ω.m i) * hab
    · linear_combination (Ω.L i * Ω.M i) * hab
  have hle : ∀ w ∈ Ω.toSet, g w ≤ bilin w := by
    intro w hw
    obtain ⟨⟨hl, hL⟩, hm, hM⟩ := hw
    show ∑ i, h i (w.1 i) (w.2 i) ≤ ∑ i, w.1 i * w.2 i
    apply Finset.sum_le_sum
    intro i _
    simp only [h]
    split_ifs
    · nlinarith [mul_nonneg (sub_nonneg.2 (hl i)) (sub_nonneg.2 (hm i))]
    · nlinarith [mul_nonneg (sub_nonneg.2 (hL i)) (sub_nonneg.2 (hM i))]
  have heq : g z = bilin z := by
    show ∑ i, h i (z.1 i) (z.2 i) = ∑ i, z.1 i * z.2 i
    apply Finset.sum_congr rfl
    intro i _
    simp only [h]
    split_ifs with hP
    · rcases hP with e | e <;> rw [e] <;> ring
    · simp only [P, not_or] at hP
      rcases (hF i).2 with e | e | e | e
      · exact absurd e hP.1
      · rw [show z.1 i = Ω.L i from e]; ring
      · exact absurd e hP.2
      · rw [show z.2 i = Ω.M i from e]; ring
  apply IsGreatest.csSup_eq
  refine ⟨⟨g, hconv, hle, heq.symm⟩, ?_⟩
  rintro r ⟨g', _, hg', rfl⟩
  exact hg' z hz
