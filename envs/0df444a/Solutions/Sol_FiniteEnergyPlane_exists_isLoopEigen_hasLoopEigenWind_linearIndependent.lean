-- Prove2me | solution 1 for FiniteEnergyPlane.exists_isLoopEigen_hasLoopEigenWind_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-01T23:07:37.627013+00:00
-- url     : https://prove2.me/submissions/9f91b965-83e9-4726-999f-7b735a7b17e0

import Definitions.Def_FiniteEnergyPlane_Winding
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_FiniteEnergyPlane_exists_angle_fundamentalSolution
import Theorems.Thm_FiniteEnergyPlane_exists_isLoopEigen_hasLoopEigenWind_of_extremal_angle
import Theorems.Thm_FiniteEnergyPlane_loopEigen_apply_ne_smul_of_hasLoopEigenWind
import Mathlib



namespace FiniteEnergyPlane

open Matrix Filter Topology ComplexConjugate
open scoped Real ContDiff

theorem exists_isLoopEigen_hasLoopEigenWind_linearIndependent_aux
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (k : ℤ) :
    ∃ μ₁ μ₂ : ℝ, ∃ e₁ e₂ : ℝ → CauchyRiemannIndex.Vec 1,
      IsLoopEigen Sinf μ₁ e₁ ∧ IsLoopEigen Sinf μ₂ e₂ ∧ HasLoopEigenWind Sinf μ₁ k ∧
        HasLoopEigenWind Sinf μ₂ k ∧ LinearIndependent ℝ ![e₁ 0, e₂ 0] := by
  have hpi := Real.pi_pos
  have hcont : ∀ μ : ℝ, Continuous fun t => Sinf t + μ • (1 : CauchyRiemannIndex.Mat 1) :=
    fun μ => hSinf.1.add continuous_const
  choose Ψ hΨ using fun μ =>
    (CauchyRiemannIndex.fundamentalSolution_existsUnique 1 _ (hcont μ)).exists
  obtain ⟨C, θ, hne, hθc, hθ0, hθ2π, hrep, hθ1c, hbd⟩ :=
    exists_angle_fundamentalSolution Sinf hSinf Ψ hΨ
  set D : ℝ → ℝ → ℝ := fun μ α => θ μ α 1 - α with hDdef
  have hDc : Continuous fun p : ℝ × ℝ => D p.1 p.2 := hθ1c.sub continuous_snd
  have hDc1 : ∀ μ, Continuous (D μ) := fun μ =>
    hDc.comp (continuous_const.prodMk continuous_id)
  have hθ1c' : ∀ μ, Continuous fun α => θ μ α 1 := fun μ =>
    hθ1c.comp (continuous_const.prodMk continuous_id)
  have hDper : ∀ μ, Function.Periodic (D μ) (2 * π) := fun μ α => by
    simp only [hDdef, hθ2π]; ring
  have hred : ∀ μ α, ∃ α' ∈ Set.Icc 0 (2 * π), D μ α = D μ α' := by
    intro μ α
    refine ⟨α - ⌊α / (2 * π)⌋ * (2 * π), ⟨?_, ?_⟩, ((hDper μ).sub_int_mul_eq _).symm⟩
    · have h := Int.floor_le (α / (2 * π))
      have : (⌊α / (2 * π)⌋ : ℝ) * (2 * π) ≤ α / (2 * π) * (2 * π) :=
        mul_le_mul_of_nonneg_right h (by linarith)
      rw [div_mul_cancel₀ _ (by positivity)] at this
      linarith
    · have h := Int.lt_floor_add_one (α / (2 * π))
      have : α / (2 * π) * (2 * π) ≤ ((⌊α / (2 * π)⌋ : ℝ) + 1) * (2 * π) :=
        mul_le_mul_of_nonneg_right h.le (by linarith)
      rw [div_mul_cancel₀ _ (by positivity)] at this
      linarith
  have hcpt : IsCompact (Set.Icc (0 : ℝ) (2 * π)) := isCompact_Icc
  have hne' : (Set.Icc (0 : ℝ) (2 * π)).Nonempty := ⟨0, le_refl _, by linarith⟩
  set M : ℝ → ℝ := fun μ => sSup (D μ '' Set.Icc 0 (2 * π)) with hMdef
  set m : ℝ → ℝ := fun μ => sInf (D μ '' Set.Icc 0 (2 * π)) with hmdef
  have hMc : Continuous M := hcpt.continuous_sSup hDc
  have hmc : Continuous m := hcpt.continuous_sInf hDc
  have himc : ∀ μ, IsCompact (D μ '' Set.Icc 0 (2 * π)) := fun μ => hcpt.image (hDc1 μ)
  have hle : ∀ μ α, D μ α ≤ M μ := by
    intro μ α
    obtain ⟨α', hα', h⟩ := hred μ α
    rw [h]
    exact le_csSup (himc μ).bddAbove (Set.mem_image_of_mem _ hα')
  have hge : ∀ μ α, m μ ≤ D μ α := by
    intro μ α
    obtain ⟨α', hα', h⟩ := hred μ α
    rw [h]
    exact csInf_le (himc μ).bddBelow (Set.mem_image_of_mem _ hα')
  have hDb : ∀ μ α, μ - C ≤ D μ α ∧ D μ α ≤ μ + C := by
    intro μ α
    have := abs_le.1 (hbd μ α)
    show μ - C ≤ θ μ α 1 - α ∧ θ μ α 1 - α ≤ μ + C
    constructor <;> linarith [this.1, this.2]
  have hC : 0 ≤ C := (abs_nonneg _).trans (hbd 0 0)
  have hMb : ∀ μ, M μ ≤ μ + C := fun μ =>
    csSup_le (hne'.image _) (by rintro _ ⟨α, -, rfl⟩; exact (hDb μ α).2)
  have hMa : ∀ μ, μ - C ≤ M μ := fun μ => (hDb μ 0).1.trans (hle μ 0)
  have hmb : ∀ μ, m μ ≤ μ + C := fun μ => (hge μ 0).trans (hDb μ 0).2
  have hma : ∀ μ, μ - C ≤ m μ := fun μ =>
    le_csInf (hne'.image _) (by rintro _ ⟨α, -, rfl⟩; exact (hDb μ α).1)
  set a := 2 * π * k - C with ha
  set b := 2 * π * k + C with hb
  have hab : a ≤ b := by linarith
  obtain ⟨μ₁, -, hμ₁⟩ := intermediate_value_Icc hab hMc.continuousOn
    (show (2 * π * k : ℝ) ∈ Set.Icc (M a) (M b) from
      ⟨by linarith [hMb a], by linarith [hMa b]⟩)
  obtain ⟨μ₂, -, hμ₂⟩ := intermediate_value_Icc hab hmc.continuousOn
    (show (2 * π * k : ℝ) ∈ Set.Icc (m a) (m b) from
      ⟨by linarith [hmb a], by linarith [hma b]⟩)
  obtain ⟨α₁, -, hα₁⟩ := (himc μ₁).sSup_mem (hne'.image _)
  obtain ⟨α₂, -, hα₂⟩ := (himc μ₂).sInf_mem (hne'.image _)
  have key := fun μ => exists_isLoopEigen_hasLoopEigenWind_of_extremal_angle Sinf hSinf hSinf' μ (Ψ μ) (hΨ μ) (θ μ) (hne μ) (hθc μ) (hθ0 μ)
    (hrep μ) (hθ1c' μ) k
  have hvsum : ∀ (s t : ℝ) (p q : CauchyRiemannIndex.Vec 1),
      vecToC (s • p + t • q) = s * vecToC p + t * vecToC q := fun s t p q => by
    exact Complex.ext (by simp [vecToC]) (by simp [vecToC])
  by_cases hμ : μ₁ = μ₂
  · rw [← hμ] at hμ₂
    have hall : ∀ β, D μ₁ β = 2 * π * k := fun β =>
      le_antisymm ((hle μ₁ β).trans hμ₁.le) (hμ₂.symm.le.trans (hge μ₁ β))
    obtain ⟨f₁, hf₁, hw₁, h0₁⟩ := key μ₁ 0 (hall 0) (Or.inl fun β => (hall β).le)
    obtain ⟨f₂, hf₂, hw₂, h0₂⟩ := key μ₁ (π / 2) (hall _) (Or.inl fun β => (hall β).le)
    refine ⟨μ₁, μ₁, f₁, f₂, hf₁, hf₂, hw₁, hw₁, ?_⟩
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := congrArg vecToC hst
    rw [hvsum, h0₁, h0₂] at h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, vecToC] at hre him
    exact ⟨hre, him⟩
  · obtain ⟨e₁, he₁, hw₁, h0₁⟩ := key μ₁ α₁ (show D μ₁ α₁ = 2 * π * k from hα₁.trans hμ₁)
      (Or.inl fun β => (hle μ₁ β).trans hμ₁.le)
    obtain ⟨e₂, he₂, hw₂, h0₂⟩ := key μ₂ α₂ (show D μ₂ α₂ = 2 * π * k from hα₂.trans hμ₂)
      (Or.inr fun β => hμ₂.symm.le.trans (hge μ₂ β))
    refine ⟨μ₁, μ₂, e₁, e₂, he₁, he₂, hw₁, hw₂, ?_⟩
    have hnp := loopEigen_apply_ne_smul_of_hasLoopEigenWind Sinf hSinf hSinf' hμ hw₁ hw₂ he₁ he₂ 0
    have he₁0 : e₁ 0 ≠ 0 := by
      intro h
      have h' := h0₁
      rw [h] at h'
      exact Complex.exp_ne_zero _ (h'.symm.trans (Complex.ext (by simp [vecToC])
        (by simp [vecToC])))
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      simp only [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.1 hst).resolve_right he₁0, rfl⟩
    · exfalso
      apply hnp (-s / t)
      have : t • e₂ 0 = -(s • e₁ 0) := eq_neg_of_add_eq_zero_right hst
      rw [div_eq_mul_inv, mul_comm, mul_smul, neg_smul, ← this, smul_smul, inv_mul_cancel₀ ht,
        one_smul]

end FiniteEnergyPlane

open FiniteEnergyPlane

open scoped ContDiff

theorem solution
    (Sinf : ℝ → CauchyRiemannIndex.Mat 1) (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j)) (k : ℤ) :
    ∃ μ₁ μ₂ : ℝ, ∃ e₁ e₂ : ℝ → CauchyRiemannIndex.Vec 1,
      IsLoopEigen Sinf μ₁ e₁ ∧ IsLoopEigen Sinf μ₂ e₂ ∧ HasLoopEigenWind Sinf μ₁ k ∧
        HasLoopEigenWind Sinf μ₂ k ∧ LinearIndependent ℝ ![e₁ 0, e₂ 0] :=
  exists_isLoopEigen_hasLoopEigenWind_linearIndependent_aux Sinf hSinf hSinf' k
