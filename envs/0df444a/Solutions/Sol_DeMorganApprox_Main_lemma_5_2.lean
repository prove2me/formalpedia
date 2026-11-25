-- Prove2me | solution 1 for DeMorganApprox.Main.lemma_5_2
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:12:16.577033+00:00
-- url     : https://prove2.me/submissions/3b2e67bc-a14b-4552-ad87-946865e1281e

import Definitions.Def_DeMorganApprox_Main_HeavyChains

open DeMorganApprox.Main DeMorganApprox.Main.SpanProgram

theorem solution {m : ℕ} (tie : TieRule) (i : Fin m) (b : Bool) :
    (program tie (Formula.lit i b)).Computes (Formula.lit i b).eval ∧
      (program tie (Formula.lit i b)).IsVectorForm ∧
      (program tie (Formula.lit i b)).HasBalancedBound 1 ∧
      (∀ k, (program tie (Formula.lit i b)).target k = basisV (.leaf []) k.1) := by
  classical
  let L := Formula.lit i b
  let P := program tie L
  let k₀ : fullCoords tie L := ⟨.leaf [], by simp [L, fullCoords, fullCoordsOf, Formula.isLeaf, chainCoords]⟩
  let j₀ : fullCols tie L := ⟨.lit [], by simp [L, fullCols, fullColsOf, Formula.isLeaf, chainCols]⟩
  have hk (k : fullCoords tie L) : k = k₀ := by
    apply Subtype.ext
    simpa [k₀, L, fullCoords, fullCoordsOf, Formula.isLeaf, chainCoords] using k.property
  have hj (j : fullCols tie L) : j = j₀ := by
    apply Subtype.ext
    simpa [j₀, L, fullCols, fullColsOf, Formula.isLeaf, chainCols] using j.property
  let : Unique (fullCoords tie L) := ⟨⟨k₀⟩, hk⟩
  let : Unique (fullCols tie L) := ⟨⟨j₀⟩, hj⟩
  have ht (k : fullCoords tie L) : P.target k = 1 := by
    rw [hk k]
    simp [P, program, L, k₀, exportV, exportKey, Formula.isLeaf, basisV]
  have hv (j : fullCols tie L) (k : fullCoords tie L) : P.vec j k = 1 := by
    rw [hj j, hk k]
    simp [P, program, L, j₀, k₀, colVec, basisV]
  have hl (j : fullCols tie L) (x : Fin m → Bool) : (P.label j).avail x = L.eval x := by
    cases b <;> rfl
  have hc : P.Computes L.eval := by
    intro x
    by_cases hx : L.eval x = true
    · refine ⟨fun _ => hx, fun _ => Submodule.subset_span ?_⟩
      exact ⟨j₀, (hl j₀ x).trans hx, funext (fun k => (hv j₀ k).trans (ht k).symm)⟩
    · have he : {j | (P.label j).avail x = true} = ∅ := by
        ext j
        simp [hl, hx]
      have hzero : P.target ≠ 0 := by
        intro h
        have h' := congrFun h k₀
        simp [ht] at h'
      simp [Accepts, he, hzero, hx]
  change P.Computes L.eval ∧ P.IsVectorForm ∧ P.HasBalancedBound 1 ∧ _
  refine ⟨hc, ⟨?_, fun j => ?_⟩, ⟨le_rfl, le_rfl, fun x => ⟨?_, ?_⟩⟩, fun _ => rfl⟩
  · simp [sqNorm, ht]
  · simp [sqNorm, hv]
  · intro ha
    have hx := (hc x).mp ha
    refine ⟨fun _ => 1, funext (fun k => ?_), ?_⟩
    · simp [applyAvail, hl, hx, hv, ht]
    · simp [sqNorm]
  · intro hn
    have hx : L.eval x ≠ true := fun h => hn ((hc x).mpr h)
    exact ⟨fun _ => 1, ⟨by simp [ht], fun j h => (hx ((hl j x).symm.trans h)).elim⟩, by simp [sqNorm]⟩
