-- Prove2me | solution 1 for FiniteEnergyPlane.exists_loopAlpha_czIndexOfPath_eq
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T16:55:35.54557+00:00
-- url     : https://prove2.me/submissions/54b658a4-93b6-4d72-8cb7-7c2e7568d3cc

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib
import Theorems.Thm_CauchyRiemannIndex_fundamentalSolution_existsUnique
import Theorems.Thm_FiniteEnergyPlane_exists_angle_fundamentalSolution
import Theorems.Thm_FiniteEnergyPlane_exists_isLoopEigen_hasLoopEigenWind_of_extremal_angle
import Theorems.Thm_FiniteEnergyPlane_loopEigen_apply_ne_smul_of_hasLoopEigenWind
import Theorems.Thm_FiniteEnergyPlane_hasLoopEigenWind_mono
import Theorems.Thm_FiniteEnergyPlane_false_of_three_hasLoopEigenWind
import Theorems.Thm_FiniteEnergyPlane_isLoopEigen_apply_ne_zero
import Theorems.Thm_HryniewiczCriterion_windingInterval_eq_image_of_isAngleLift



namespace FiniteEnergyPlane

open Matrix
open scoped Real

/-- Angle lifts of `Ψ(t) e^{iα}` in `vecToC` form are angle lifts of the reindexed path. -/
theorem lc_isAngleLift (A : ℝ → CauchyRiemannIndex.Mat 1) (θ : ℝ → ℝ → ℝ)
    (hne : ∀ (t : ℝ) (v : CauchyRiemannIndex.Vec 1), v ≠ 0 → Matrix.toEuclideanLin (A t) v ≠ 0)
    (hθc : ∀ α, Continuous (θ α)) (hθ0 : ∀ α, θ α 0 = α)
    (hrep : ∀ (α : ℝ) (v : CauchyRiemannIndex.Vec 1), vecToC v = Complex.exp (α * Complex.I) →
      ∀ t, vecToC (Matrix.toEuclideanLin (A t) v) =
        (‖vecToC (Matrix.toEuclideanLin (A t) v)‖ : ℂ) * Complex.exp (θ α t * Complex.I))
    (s : ℝ) :
    HryniewiczCriterion.IsAngleLift
      (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (A τ)) s (θ s) := by
  refine ⟨(hθc s).continuousOn, hθ0 s, fun t _ => ?_⟩
  set v : CauchyRiemannIndex.Vec 1 :=
    Real.cos s • EuclideanSpace.single (Sum.inl 0) 1 +
      Real.sin s • EuclideanSpace.single (Sum.inr 0) 1 with hv
  have hvC : vecToC v = Complex.exp (s * Complex.I) := by
    apply Complex.ext <;>
      simp [hv, vecToC, EuclideanSpace.single_apply, Complex.exp_ofReal_mul_I_re,
        Complex.exp_ofReal_mul_I_im]
  have hv0 : v ≠ 0 := by
    intro h
    have := congrArg vecToC h
    rw [hvC] at this
    exact Complex.exp_ne_zero _ (this.trans (Complex.ext (by simp [vecToC]) (by simp [vecToC])))
  set w := Matrix.toEuclideanLin (A t) v with hw
  have hwne : vecToC w ≠ 0 := by
    intro h
    apply hne t v hv0
    have h1 : w (Sum.inl 0) = 0 := congrArg Complex.re h
    have h2 : w (Sum.inr 0) = 0 := congrArg Complex.im h
    ext i
    rcases i with i | i <;> rw [Subsingleton.elim i 0] <;> simpa [hw] using ‹_›
  have hrp := hrep s v hvC t
  rw [← hw] at hrp
  refine ⟨‖vecToC w‖, norm_pos_iff.2 hwne, ?_⟩
  have hre := congrArg Complex.re hrp
  have him := congrArg Complex.im hrp
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im] at hre him
  have e0 : w (Sum.inl 0) = A t (Sum.inl 0) (Sum.inl 0) * Real.cos s +
      A t (Sum.inl 0) (Sum.inr 0) * Real.sin s := by
    simp [hw, hv, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      EuclideanSpace.single_apply]
  have e1 : w (Sum.inr 0) = A t (Sum.inr 0) (Sum.inl 0) * Real.cos s +
      A t (Sum.inr 0) (Sum.inr 0) * Real.sin s := by
    simp [hw, hv, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
      EuclideanSpace.single_apply]
  have hre' : w (Sum.inl 0) = ‖vecToC w‖ * Real.cos (θ s t) := by simpa [vecToC] using hre
  have him' : w (Sum.inr 0) = ‖vecToC w‖ * Real.sin (θ s t) := by simpa [vecToC] using him
  have f0 : finSumFinEquiv.symm (0 : Fin 2) = (Sum.inl 0 : Fin 1 ⊕ Fin 1) := rfl
  have f1 : finSumFinEquiv.symm (1 : Fin 2) = (Sum.inr 0 : Fin 1 ⊕ Fin 1) := rfl
  ext i
  fin_cases i
  · show (Matrix.reindex finSumFinEquiv finSumFinEquiv (A t)).mulVec
        (HryniewiczCriterion.rotationVector s) 0 = _
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, HryniewiczCriterion.rotationVector, f0, f1]
    rw [← e0, hre']
  · show (Matrix.reindex finSumFinEquiv finSumFinEquiv (A t)).mulVec
        (HryniewiczCriterion.rotationVector s) 1 = _
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, HryniewiczCriterion.rotationVector, f0, f1]
    rw [← e1, him']

end FiniteEnergyPlane

namespace FiniteEnergyPlane

open Matrix Filter Topology
open scoped Real ContDiff

theorem exists_loopAlpha_czIndexOfPath_eq_aux (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (_hnd : CauchyRiemannIndex.IsNondegenerate Sinf) :
    ∃ a b : ℤ,
      ((∃ μ < 0, HasLoopEigenWind Sinf μ a) ∧
        ∀ μ < 0, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ a) ∧
      ((∃ μ, 0 ≤ μ ∧ HasLoopEigenWind Sinf μ b) ∧
        ∀ μ, 0 ≤ μ → ∀ k : ℤ, HasLoopEigenWind Sinf μ k → b ≤ k) ∧
      (b = a ∨ b = a + 1) ∧
      ∀ Ψ : ℝ → CauchyRiemannIndex.Mat 1, CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ →
        HryniewiczCriterion.czIndexOfPath
          (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)) = a + b := by
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
  have hmM : ∀ μ, m μ ≤ M μ := fun μ => (hge μ 0).trans (hle μ 0)
  have key := fun μ => exists_isLoopEigen_hasLoopEigenWind_of_extremal_angle Sinf hSinf hSinf'
    μ (Ψ μ) (hΨ μ) (θ μ) (hne μ) (hθc μ) (hθ0 μ) (hrep μ) (hθ1c' μ)
  -- extremal values on `2πℤ` are eigenvalues
  have hMeig : ∀ (μ : ℝ) (k : ℤ), M μ = 2 * π * k → HasLoopEigenWind Sinf μ k := by
    intro μ k h
    obtain ⟨α₁, -, hα₁⟩ := (himc μ).sSup_mem (hne'.image _)
    obtain ⟨_, _, hw, _⟩ := key μ k α₁ (show D μ α₁ = 2 * π * k from hα₁.trans h)
      (Or.inl fun β => (hle μ β).trans h.le)
    exact hw
  have hmeig : ∀ (μ : ℝ) (k : ℤ), m μ = 2 * π * k → HasLoopEigenWind Sinf μ k := by
    intro μ k h
    obtain ⟨α₂, -, hα₂⟩ := (himc μ).sInf_mem (hne'.image _)
    obtain ⟨_, _, hw, _⟩ := key μ k α₂ (show D μ α₂ = 2 * π * k from hα₂.trans h)
      (Or.inr fun β => h.symm.le.trans (hge μ β))
    exact hw
  have vC_inj : ∀ {v w : CauchyRiemannIndex.Vec 1}, vecToC v = vecToC w → v = w := by
    intro v w h
    have h1 : v (Sum.inl 0) = w (Sum.inl 0) := congrArg Complex.re h
    have h2 : v (Sum.inr 0) = w (Sum.inr 0) := congrArg Complex.im h
    ext i
    rcases i with i | i <;> rw [Subsingleton.elim i 0] <;> assumption
  have vC_smul : ∀ (c : ℝ) (v : CauchyRiemannIndex.Vec 1), vecToC (c • v) = (c : ℂ) * vecToC v :=
    fun c v => Complex.ext (by simp [vecToC]) (by simp [vecToC])
  -- at most the two extremal crossings carry a given winding
  have hG : ∀ (k : ℤ) (μ₁ μ₂ : ℝ), M μ₁ = 2 * π * k → m μ₂ = 2 * π * k →
      ∀ μ, HasLoopEigenWind Sinf μ k → μ = μ₁ ∨ μ = μ₂ := by
    intro k μ₁ μ₂ h1 h2 μ hμ
    by_contra hcon
    push Not at hcon
    have w1 := hMeig μ₁ k h1
    have w2 := hmeig μ₂ k h2
    by_cases h12 : μ₁ = μ₂
    · subst h12
      have hall : ∀ β, D μ₁ β = 2 * π * k := fun β =>
        le_antisymm ((hle μ₁ β).trans h1.le) (h2.symm.le.trans (hge μ₁ β))
      obtain ⟨e', he'⟩ := hμ.1
      set α₀ := Complex.arg (vecToC (e' 0))
      obtain ⟨f, hf, -, hf0⟩ := key μ₁ k α₀ (hall α₀) (Or.inl fun β => (hall β).le)
      apply loopEigen_apply_ne_smul_of_hasLoopEigenWind Sinf hSinf hSinf' (Ne.symm hcon.1)
        w1 hμ hf he' 0 ‖vecToC (e' 0)‖
      apply vC_inj
      rw [vC_smul, hf0, Complex.norm_mul_exp_arg_mul_I]
    · have three := fun {x y z : ℝ} (hxy : x < y) (hyz : y < z) =>
        false_of_three_hasLoopEigenWind Sinf hSinf hSinf' (k := k) hxy hyz
      rcases lt_or_gt_of_ne h12 with a | a <;> rcases lt_or_gt_of_ne hcon.1 with b | b <;>
        rcases lt_or_gt_of_ne hcon.2 with c | c <;>
        first
        | exact three (by linarith) (by linarith) hμ w1 w2
        | exact three (by linarith) (by linarith) hμ w2 w1
        | exact three (by linarith) (by linarith) w1 hμ w2
        | exact three (by linarith) (by linarith) w1 w2 hμ
        | exact three (by linarith) (by linarith) w2 hμ w1
        | exact three (by linarith) (by linarith) w2 w1 hμ
        | linarith
  -- the winding interval of the fundamental solution of `S∞`
  set φ : ℝ → Matrix (Fin 2) (Fin 2) ℝ :=
    fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ 0 τ) with hφ
  have hW : HryniewiczCriterion.windingInterval φ = (fun x => x / (2 * π)) '' (D 0 '' Set.Icc 0 (2 * π)) := by
    rw [HryniewiczCriterion.windingInterval_eq_image_of_isAngleLift φ (θ 0)
      (lc_isAngleLift (Ψ 0) (θ 0) (hne 0) (hθc 0) (hθ0 0) (hrep 0)), Set.image_image]
  have hmono : Monotone fun x : ℝ => x / (2 * π) := fun x y h =>
    div_le_div_of_nonneg_right h (by positivity)
  have hsup : sSup (HryniewiczCriterion.windingInterval φ) = M 0 / (2 * π) := by
    rw [hW]
    exact (hmono.map_isGreatest ((himc 0).isGreatest_sSup (hne'.image _))).csSup_eq
  have hinf : sInf (HryniewiczCriterion.windingInterval φ) = m 0 / (2 * π) := by
    rw [hW]
    exact (hmono.map_isLeast ((himc 0).isLeast_sInf (hne'.image _))).csInf_eq
  set K : ℤ := ⌈M 0 / (2 * π)⌉ - 1 with hKdef
  have hK1 : 2 * π * K < M 0 := by
    have h := Int.ceil_lt_add_one (M 0 / (2 * π))
    have : (K : ℝ) < M 0 / (2 * π) := by rw [hKdef]; push_cast; linarith
    rw [lt_div_iff₀ (by positivity)] at this; linarith
  have hK2 : M 0 ≤ 2 * π * ((K + 1 : ℤ) : ℝ) := by
    have h := Int.le_ceil (M 0 / (2 * π))
    have : M 0 / (2 * π) ≤ ((K + 1 : ℤ) : ℝ) := by rw [hKdef]; push_cast; linarith
    rw [div_le_iff₀ (by positivity)] at this; linarith
  have hidx : HryniewiczCriterion.czIndexOfPath φ = if m 0 ≤ 2 * π * K then 2 * K else 2 * K + 1 := by
    unfold HryniewiczCriterion.czIndexOfPath
    simp only [hsup, hinf]
    have hiff : m 0 / (2 * π) ≤ ((⌈M 0 / (2 * π)⌉ - 1 : ℤ) : ℝ) ↔ m 0 ≤ 2 * π * K := by
      rw [div_le_iff₀ (by positivity), hKdef]; constructor <;> intro h <;> linarith
    by_cases h : m 0 ≤ 2 * π * K
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h, hKdef]; ring
  have hΨ0 : ∀ Ψ' : ℝ → CauchyRiemannIndex.Mat 1, CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ' →
      Ψ' = Ψ 0 := by
    intro Ψ' hΨ'
    have h0 : (fun t => Sinf t + (0 : ℝ) • (1 : CauchyRiemannIndex.Mat 1)) = Sinf := by
      funext t; simp
    have h := hΨ 0
    rw [h0] at h
    exact (CauchyRiemannIndex.fundamentalSolution_existsUnique 1 Sinf hSinf.1).unique hΨ' h
  -- search intervals
  set L : ℝ := -(|2 * π * K| + C + 1) with hL
  set U : ℝ := |2 * π * ((K + 1 : ℤ) : ℝ)| + C + 1 with hU
  have hL0 : L ≤ 0 := by have := abs_nonneg (2 * π * K); linarith
  have hU0 : 0 ≤ U := by have := abs_nonneg (2 * π * ((K + 1 : ℤ) : ℝ)); linarith
  have hML : M L ≤ 2 * π * K := by
    have := hMb L; have := neg_abs_le (2 * π * K); linarith
  have hmU : 2 * π * ((K + 1 : ℤ) : ℝ) ≤ m U := by
    have := hma U; have := le_abs_self (2 * π * ((K + 1 : ℤ) : ℝ)); linarith
  have hKK : 2 * π * (K : ℝ) ≤ 2 * π * ((K + 1 : ℤ) : ℝ) := by push_cast; linarith
  -- the negative crossing of `M` at level `2πK`
  obtain ⟨μ₁, hμ₁I, hμ₁⟩ := intermediate_value_Icc hL0 hMc.continuousOn
    (show (2 * π * K : ℝ) ∈ Set.Icc (M L) (M 0) from ⟨hML, hK1.le⟩)
  have hμ₁0 : μ₁ < 0 := lt_of_le_of_ne hμ₁I.2 (fun h => by rw [h] at hμ₁; linarith)
  have w₁ := hMeig μ₁ K hμ₁
  by_cases hA : m 0 ≤ 2 * π * K
  · obtain ⟨μ₂, hμ₂I, hμ₂⟩ := intermediate_value_Icc hU0 hmc.continuousOn
      (show (2 * π * K : ℝ) ∈ Set.Icc (m 0) (m U) from ⟨hA, hKK.trans hmU⟩)
    have w₂ := hmeig μ₂ K hμ₂
    refine ⟨K, K, ⟨⟨μ₁, hμ₁0, w₁⟩, fun μ hμ k hk =>
        hasLoopEigenWind_mono Sinf hSinf hSinf' hk w₂ (by linarith [hμ₂I.1])⟩,
      ⟨⟨μ₂, hμ₂I.1, w₂⟩, fun μ hμ k hk =>
        hasLoopEigenWind_mono Sinf hSinf hSinf' w₁ hk (by linarith)⟩, Or.inl rfl,
      fun Ψ' hΨ' => ?_⟩
    rw [hΨ0 Ψ' hΨ', ← hφ, hidx, if_pos hA]; ring
  · push Not at hA
    have hmL : m L ≤ 2 * π * K := (hmM L).trans hML
    obtain ⟨μ₄, hμ₄I, hμ₄⟩ := intermediate_value_Icc hL0 hmc.continuousOn
      (show (2 * π * K : ℝ) ∈ Set.Icc (m L) (m 0) from ⟨hmL, hA.le⟩)
    have hμ₄0 : μ₄ < 0 := lt_of_le_of_ne hμ₄I.2 (fun h => by rw [h] at hμ₄; linarith)
    obtain ⟨μ₂, hμ₂I, hμ₂⟩ := intermediate_value_Icc hU0 hmc.continuousOn
      (show (2 * π * ((K + 1 : ℤ) : ℝ) : ℝ) ∈ Set.Icc (m 0) (m U) from
        ⟨(hmM 0).trans hK2, hmU⟩)
    obtain ⟨μ₃, hμ₃I, hμ₃⟩ := intermediate_value_Icc hU0 hMc.continuousOn
      (show (2 * π * ((K + 1 : ℤ) : ℝ) : ℝ) ∈ Set.Icc (M 0) (M U) from
        ⟨hK2, hmU.trans (hmM U)⟩)
    have w₂ := hmeig μ₂ (K + 1) hμ₂
    refine ⟨K, K + 1, ⟨⟨μ₁, hμ₁0, w₁⟩, fun μ hμ k hk => ?_⟩,
      ⟨⟨μ₂, hμ₂I.1, w₂⟩, fun μ hμ k hk => ?_⟩, Or.inr rfl, fun Ψ' hΨ' => ?_⟩
    · have h1 := hasLoopEigenWind_mono Sinf hSinf hSinf' hk w₂ (by linarith [hμ₂I.1])
      rcases (show k = K + 1 ∨ k ≤ K by omega) with h | h
      · subst h
        rcases hG (K + 1) μ₃ μ₂ hμ₃ hμ₂ μ hk with h' | h' <;>
          linarith [hμ₃I.1, hμ₂I.1]
      · exact h
    · have h1 := hasLoopEigenWind_mono Sinf hSinf hSinf' w₁ hk (by linarith)
      rcases (show k = K ∨ K + 1 ≤ k by omega) with h | h
      · subst h
        rcases hG K μ₁ μ₄ hμ₁ hμ₄ μ hk with h' | h' <;> linarith
      · exact h
    · rw [hΨ0 Ψ' hΨ', ← hφ, hidx, if_neg (not_le.2 hA)]; ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (Sinf : ℝ → CauchyRiemannIndex.Mat 1)
    (hSinf : CauchyRiemannIndex.IsSymLoop Sinf)
    (hSinf' : ∀ i j, ContDiff ℝ ∞ (fun t => Sinf t i j))
    (hnd : CauchyRiemannIndex.IsNondegenerate Sinf) :
    ∃ a b : ℤ,
      ((∃ μ < 0, HasLoopEigenWind Sinf μ a) ∧
        ∀ μ < 0, ∀ k : ℤ, HasLoopEigenWind Sinf μ k → k ≤ a) ∧
      ((∃ μ, 0 ≤ μ ∧ HasLoopEigenWind Sinf μ b) ∧
        ∀ μ, 0 ≤ μ → ∀ k : ℤ, HasLoopEigenWind Sinf μ k → b ≤ k) ∧
      (b = a ∨ b = a + 1) ∧
      ∀ Ψ : ℝ → CauchyRiemannIndex.Mat 1, CauchyRiemannIndex.IsFundamentalSolution Sinf Ψ →
        HryniewiczCriterion.czIndexOfPath
          (fun τ => Matrix.reindex finSumFinEquiv finSumFinEquiv (Ψ τ)) = a + b :=
  FiniteEnergyPlane.exists_loopAlpha_czIndexOfPath_eq_aux Sinf hSinf hSinf' hnd
