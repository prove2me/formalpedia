-- Prove2me | solution 1 for DivQuotient.dq_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:41:33.575199+00:00
-- url     : https://prove2.me/submissions/e9783ba4-f547-4085-861f-7c69169387f1

import Mathlib
import Definitions.Def_DivQuotient_DQ

open MeasureTheory

open DivQuotient in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (hn : 0 < n) (abar : EReal) (ρ : ℝ → Lp ℝ ⊤ P → ℝ) (α : ℝ) (hα : α ∈ IndexSet abar)
    (hsub : IsSubadditive (ρ α)) (X : Fin n → Lp ℝ ⊤ P) :
    DQ abar (fun β X => (ρ β X : EReal)) α X ∈ Set.Icc (0 : EReal) 1 := by
  obtain ⟨hα0, hαa⟩ := hα
  have hsubsum : ∀ m (Y : Fin (m + 1) → Lp ℝ ⊤ P), ρ α (∑ i, Y i) ≤ ∑ i, ρ α (Y i) := by
    intro m
    induction m with
    | zero => intro Y; rw [Fin.sum_univ_one, Fin.sum_univ_one]
    | succ m ih =>
      intro Y
      rw [Fin.sum_univ_succ (f := Y), Fin.sum_univ_succ (f := fun i => ρ α (Y i))]
      exact le_trans (hsub _ _) (add_le_add le_rfl (ih _))
  have hcoe : ∀ (s : Finset (Fin n)) (f : Fin n → ℝ),
      ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, (f i : EReal) := by
    intro s f
    refine Finset.induction_on s (by simp) (fun a s ha ih => ?_)
    rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]
  have hSX : ρ α (S X) ≤ ∑ i, ρ α (X i) := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact hsubsum m X
  have hmem : α ∈ {β : ℝ | β ∈ IndexSet abar ∧
      (fun β X => (ρ β X : EReal)) β (S X) ≤ ∑ i, (fun β X => (ρ β X : EReal)) α (X i)} := by
    refine ⟨⟨hα0, hαa⟩, ?_⟩
    show (ρ α (S X) : EReal) ≤ ∑ i, (ρ α (X i) : EReal)
    rw [← hcoe]
    exact EReal.coe_le_coe_iff.mpr hSX
  have hle : alphaStar abar (fun β X => (ρ β X : EReal)) α X ≤ (α : EReal) :=
    le_trans (min_le_right _ _) (biInf_le (fun β : ℝ => (β : EReal)) hmem)
  have hge : 0 ≤ alphaStar abar (fun β X => (ρ β X : EReal)) α X :=
    le_min (le_trans (EReal.coe_nonneg.mpr hα0.le) hαa.le)
      (le_iInf₂ (fun β hβ => EReal.coe_nonneg.mpr hβ.1.1.le))
  have htop : alphaStar abar (fun β X => (ρ β X : EReal)) α X ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top α) hle
  have hbot : alphaStar abar (fun β X => (ρ β X : EReal)) α X ≠ ⊥ :=
    (lt_of_lt_of_le EReal.bot_lt_zero hge).ne'
  obtain ⟨a, ha⟩ : ∃ a : ℝ, alphaStar abar (fun β X => (ρ β X : EReal)) α X = a :=
    ⟨_, (EReal.coe_toReal htop hbot).symm⟩
  rw [ha] at hle hge
  have ha0 : 0 ≤ a := EReal.coe_nonneg.mp hge
  have ha1 : a ≤ α := EReal.coe_le_coe_iff.mp hle
  show alphaStar abar (fun β X => (ρ β X : EReal)) α X / (α : EReal) ∈ Set.Icc (0 : EReal) 1
  rw [ha, ← EReal.coe_div]
  refine ⟨EReal.coe_nonneg.mpr (div_nonneg ha0 hα0.le), ?_⟩
  rw [← EReal.coe_one, EReal.coe_le_coe_iff]
  exact (div_le_one hα0).mpr ha1
