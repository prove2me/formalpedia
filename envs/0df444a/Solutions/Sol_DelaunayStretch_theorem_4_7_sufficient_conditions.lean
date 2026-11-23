-- Prove2me | solution 1 for DelaunayStretch.theorem_4_7_sufficient_conditions
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-23T00:45:17.169028+00:00
-- url     : https://prove2.me/submissions/11cf7f26-98af-481b-aaf3-38586c4f9e8f

import Theorems.Thm_DelaunayStretch_theorem_3_9_potential_criterion
import Theorems.Thm_DelaunayStretch_lemma_4_4_pencil
import Theorems.Thm_DelaunayStretch_lemma_4_9_sliding_gate
import Theorems.Thm_DelaunayStretch_corollary_4_10_sliding_disk
import Theorems.Thm_DelaunayStretch_lemma_4_11_initial_final

open DelaunayStretch

/-- Two disks through the ends of a gate, with the second center to the right, are two members
`O(X₁)`, `O(X₂)`, `X₁ < X₂`, of the pencil of the gate. -/
theorem pencil_pair_of_boundary (a b : ℂ) (ha : 0 < a.im) (hb : b.im < 0) (O O' : Disk)
    (h : O.boundary ∩ O'.boundary = {a, b}) (hc : O.center.re < O'.center.re) :
    ∃ X₁ X₂ : ℝ, X₁ < X₂ ∧ O = pencilDisk a b X₁ ∧ O' = pencilDisk a b X₂ := by
  have hP := lemma_4_4_pencil a b ha hb
  have haO : a ∈ O.boundary ∧ a ∈ O'.boundary := by
    have : a ∈ O.boundary ∩ O'.boundary := by rw [h]; simp
    exact this
  have hbO : b ∈ O.boundary ∧ b ∈ O'.boundary := by
    have : b ∈ O.boundary ∩ O'.boundary := by rw [h]; simp
    exact this
  obtain ⟨X₁, rfl⟩ := (hP.1 O).1 ⟨haO.1, hbO.1⟩
  obtain ⟨X₂, rfl⟩ := (hP.1 O').1 ⟨haO.2, hbO.2⟩
  refine ⟨X₁, X₂, ?_, rfl, rfl⟩
  rcases lt_trichotomy X₁ X₂ with h12 | h12 | h12
  · exact h12
  · subst h12; exact absurd hc (lt_irrefl _)
  · exact absurd ((hP.2.1 X₂ X₁ (ne_of_lt h12)).2.mpr h12) (not_lt.mpr hc.le)

theorem solution (U : ℝ) (hU : Real.pi / 2 ≤ U) (H : R4 → ℝ)
    (hH : SatisfiesH0toH4 U H) :
    IsFeasiblePotential U (potential H U) ∧ ChainInequality U := by
  obtain ⟨P, h0, h1, h2, h3, h4⟩ := hH
  have hI := (lemma_4_11_initial_final U H h1 h3)
  have hfeas : IsFeasiblePotential U (potential H U) := by
    refine ⟨?_, ?_, ?_⟩
    · intro O₁ O₂ a₁ b₁ hip
      obtain ⟨hgs, hle⟩ := hI.1 O₁ O₂ a₁ b₁ hip
      obtain ⟨hint, ha, hb, hc⟩ := hip
      obtain ⟨X₁, X₂, hX, rfl, rfl⟩ := pencil_pair_of_boundary a₁ b₁ ha hb O₁ O₂ hint hc
      have h10 := corollary_4_10_sliding_disk U H ⟨P, h0, h4⟩ a₁ b₁ ha hb
        (initialDiff (pencilDisk a₁ b₁ X₁) a₁ b₁) hgs.2.2.2.2.2 X₁ X₂ hX
      have : initialState (pencilDisk a₁ b₁ X₁) (pencilDisk a₁ b₁ X₂) a₁ b₁ =
          pencilState a₁ b₁ (initialDiff (pencilDisk a₁ b₁ X₁) a₁ b₁) X₂ := rfl
      rw [this]
      have : (⟨pencilDisk a₁ b₁ X₁, a₁, b₁, initialDiff (pencilDisk a₁ b₁ X₁) a₁ b₁⟩ : GateState) =
          pencilState a₁ b₁ (initialDiff (pencilDisk a₁ b₁ X₁) a₁ b₁) X₁ := rfl
      rw [this] at hle
      linarith
    · intro s hs O' a' b' hnd
      obtain ⟨hgs, hle⟩ := lemma_4_9_sliding_gate U H ⟨P, h0, h1, h2⟩ s hs O' a' b' hnd
      obtain ⟨hint, ha, hb, hc, -⟩ := hnd
      obtain ⟨X₁, X₂, hX, hO, hO'⟩ := pencil_pair_of_boundary a' b' ha hb s.O O' hint hc
      have h10 := corollary_4_10_sliding_disk U H ⟨P, h0, h4⟩ a' b' ha hb
        (stepDiff s a' b') hgs.2.2.2.2.2 X₁ X₂ hX
      have e1 : stepState s O' a' b' = pencilState a' b' (stepDiff s a' b') X₂ := by
        rw [stepState, hO']; rfl
      have e2 : (⟨s.O, a', b', stepDiff s a' b'⟩ : GateState) =
          pencilState a' b' (stepDiff s a' b') X₁ := by
        rw [hO]; rfl
      rw [e1]
      rw [e2] at hle
      linarith
    · intro s hs
      have := hI.2 s hs
      linarith
  exact ⟨hfeas, theorem_3_9_potential_criterion U hU ⟨_, hfeas⟩⟩
