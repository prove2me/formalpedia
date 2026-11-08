-- Prove2me | solution 1 for DilatableEntropy.sum_parent_le_MQ
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:25:51.033971+00:00
-- url     : https://prove2.me/submissions/d0d3ea81-cdfe-422a-8ec9-38ba604a3188

import Mathlib
import Definitions.Def_DilatableEntropy_seqFormPolytope
import Definitions.Def_DilatableEntropy_MQ

open DilatableEntropy in
theorem solution (P : DilatableEntropy.SeqDecisionProblem) :
    ∀ x ∈ DilatableEntropy.seqFormPolytope P, ∑ j : P.J, x (P.parent j) ≤ DilatableEntropy.MQ P := by
  -- the "is the parent of" relation is well founded (finite type, acyclic)
  have hflip : WellFounded (fun j' j : P.J => ∃ a, P.parent j = some ⟨j', a⟩) := by
    have htg := P.wf.transGen
    let R : P.J → P.J → Prop := fun a b => Relation.TransGen
      (fun j' j => ∃ a, P.parent j' = some ⟨j, a⟩) b a
    haveI : IsTrans P.J R := ⟨fun a b c hab hbc => Relation.TransGen.trans hbc hab⟩
    haveI : Std.Irrefl R := ⟨fun a h => htg.asymmetric a a h h⟩
    have hR : WellFounded R := Finite.wellFounded_of_trans_of_irrefl R
    exact Subrelation.wf (fun {a b} h => Relation.TransGen.single h) hR
  have hle : ∀ y ∈ DilatableEntropy.seqFormPolytope P, ∀ σ, y σ ≤ 1 := by
    intro y hy σ
    obtain ⟨hnn, h1, hsum⟩ := hy
    have key : ∀ j : P.J, ∀ a : P.A j, y (some ⟨j, a⟩) ≤ 1 := by
      intro j
      refine hflip.induction (C := fun j => ∀ a : P.A j, y (some ⟨j, a⟩) ≤ 1) j ?_
      intro j IH a
      have h2 : y (some ⟨j, a⟩) ≤ ∑ a', y (some ⟨j, a'⟩) :=
        Finset.single_le_sum (f := fun a' => y (some ⟨j, a'⟩)) (fun a' _ => hnn _)
          (Finset.mem_univ a)
      rw [hsum j] at h2
      rcases hp : P.parent j with _ | ⟨j', a'⟩
      · rw [hp, h1] at h2
        exact h2
      · rw [hp] at h2
        exact h2.trans (IH j' ⟨a', hp⟩ a')
    rcases σ with _ | ⟨j, a⟩
    · rw [h1]
    · exact key j a
  have hbdd : BddAbove ((fun x : DilatableEntropy.Seq P → ℝ => ∑ σ, |x σ|) ''
      DilatableEntropy.seqFormPolytope P) := by
    refine ⟨(Fintype.card (DilatableEntropy.Seq P) : ℝ), ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    calc ∑ σ, |y σ| ≤ ∑ _σ : DilatableEntropy.Seq P, (1:ℝ) :=
          Finset.sum_le_sum (fun σ _ => by
            rw [abs_of_nonneg (hy.1 σ)]
            exact hle y hy σ)
      _ = (Fintype.card (DilatableEntropy.Seq P) : ℝ) := by simp
  intro x hx
  have hx' := hx
  obtain ⟨hnn, h1, hsum⟩ := hx'
  have habs : ∀ σ, |x σ| = x σ := fun σ => abs_of_nonneg (hnn σ)
  calc ∑ j : P.J, x (P.parent j) = ∑ j : P.J, ∑ a : P.A j, x (some ⟨j, a⟩) :=
        Finset.sum_congr rfl (fun j _ => (hsum j).symm)
    _ = ∑ s : (Σ j, P.A j), x (some s) := (Fintype.sum_sigma (fun s => x (some s))).symm
    _ ≤ ∑ σ, |x σ| := by
        rw [Fintype.sum_option]
        simp only [habs]
        linarith [hnn none]
    _ ≤ DilatableEntropy.MQ P := le_csSup hbdd ⟨x, hx, rfl⟩
