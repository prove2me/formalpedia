-- Prove2me | solution 1 for ClassicalSchur.lift_lemma
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-26T21:38:32.948728+00:00
-- url     : https://prove2.me/submissions/5da50563-7163-4399-8401-ed51b28e0553

-- Generated from lean/ClassicalSchur/Lift.lean
--   imports : 3 platform node(s), 2 definition bundle(s)
--   inlined : 3 file-scoped / sub-threshold helper(s)
--   rename  : lift_lemma -> solution, hoisted out of the namespace
import Definitions.Def_ClassicalSchurBasic
import Definitions.Def_ClassicalSchurLift
import Theorems.Thm_ClassicalSchur_coveredBySumFree_liftSeq
import Theorems.Thm_ClassicalSchur_liftPrefix_strictMono
import Theorems.Thm_ClassicalSchur_liftSeq_take_sum
import Mathlib



namespace ClassicalSchur

/-- A cover by `q ≥ 1` sumfree sets bounds the Schur degree by `q`. -/
theorem sdeg_le_of_coveredBySumFree {X : Set ℕ} {q : ℕ} (hq : 1 ≤ q)
    (h : CoveredBySumFree X q) : sdeg X ≤ q :=
  sInf_le ⟨q, ⟨hq, h⟩, rfl⟩

theorem liftSeq_pos {m₁ m₂ M : ℕ} (hm₁ : 0 < m₁) (hM : m₁ ≤ M) :
    ∀ a ∈ liftSeq m₁ m₂ M, 0 < a := by
  intro a ha
  simp only [liftSeq, List.mem_map, List.mem_range] at ha
  obtain ⟨k, -, rfl⟩ := ha
  have := liftPrefix_strictMono hm₁ hM (show k < k + 1 by omega)
  omega

@[simp] theorem liftSeq_length (m₁ m₂ M : ℕ) : (liftSeq m₁ m₂ M).length = m₁ * m₂ - 1 := by
  simp [liftSeq]

end ClassicalSchur

open ClassicalSchur in
theorem solution {m₁ m₂ q M : ℕ} (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hq : 0 < q)
    (hM : 3 * m₁ - 2 ≤ M) (C : Fin q → Set (ZMod m₁ × ZMod m₂))
    (hC : ∀ i, GroupSumFree (C i)) (hcov : ∀ g : ZMod m₁ × ZMod m₂, g ≠ 0 → ∃ i, g ∈ C i) :
    (liftSeq m₁ m₂ M).length = m₁ * m₂ - 1 ∧ (∀ a ∈ liftSeq m₁ m₂ M, 0 < a) ∧
      sdeg (blockSums (liftSeq m₁ m₂ M)) ≤ q ∧
      ∀ L ≤ m₁ * m₂ - 1, ((liftSeq m₁ m₂ M).take L).sum = L % m₁ + M * (L / m₁) := by
  have hM' : m₁ ≤ M := by omega
  exact ⟨liftSeq_length .., liftSeq_pos hm₁ hM',
    sdeg_le_of_coveredBySumFree hq (coveredBySumFree_liftSeq hm₁ hm₂ hM C hC hcov),
    fun _ hL => liftSeq_take_sum hm₁ hM' hL⟩
