-- Prove2me | solution 1 for FiniteEnergyPlane.isPrime_of_isFastPlane_of_isNondegenerateEnd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T21:08:22.461142+00:00
-- url     : https://prove2.me/submissions/dbef8f45-7da5-440d-a2fc-10559cb22d89

import Definitions.Def_FiniteEnergyPlane_Compactness
import Theorems.Thm_FiniteEnergyPlane_dlambdaEnergy_univ_eq_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitzOnWith_reeb
import Mathlib



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A periodic Reeb orbit passing twice through one point is periodic with the time difference. -/
theorem lp_orbit_shift {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (Q : ReebOrbit H)
    (σ₁ σ₂ : ℝ) (h : Q.x σ₁ = Q.x σ₂) (σ : ℝ) : Q.x (σ₁ + σ) = Q.x (σ₂ + σ) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_reeb H hH
  have huniq : (fun s => Q.x (σ₁ + s)) = fun s => Q.x (σ₂ + s) := by
    refine ODE_solution_unique_univ (v := fun _ => reeb H) (s := fun _ => energySurface H)
      (K := K) (t₀ := 0) (fun _ => hK) (fun s => ⟨?_, Q.mem _⟩) (fun s => ⟨?_, Q.mem _⟩)
      (by simpa using h)
    · simpa using (Q.hasDerivAt (σ₁ + s)).comp_const_add σ₁ s
    · simpa using (Q.hasDerivAt (σ₂ + s)).comp_const_add σ₂ s
  exact congrFun huniq σ

theorem isPrime_of_isFastPlane_of_isNondegenerateEnd_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hfast : IsFastPlane H J u) (P : ReebOrbit H) (hnd : IsNondegenerateEnd H u cylInf P 1) :
    P.IsPrime := by
  obtain ⟨hfe, ⟨P', hprime, hnd'⟩, -⟩ := hfast
  have hT : P.T = P'.T := (ENNReal.ofReal_eq_ofReal_iff P.T_pos.le P'.T_pos.le).1
    ((dlambdaEnergy_univ_eq_of_isNondegenerateEnd H hH J hJ u hfe P hnd).symm.trans
      (dlambdaEnergy_univ_eq_of_isNondegenerateEnd H hH J hJ u hfe P' hnd'))
  obtain ⟨-, c, b, hb, -, h⟩ := hnd
  obtain ⟨-, c', b', hb', -, h'⟩ := hnd'
  have hclose : ∀ (R : ReebOrbit H) (c₀ b₀ : ℝ), 0 < b₀ →
      TendstoZeroUnif (fun p : ℝ × ℝ =>
        Real.exp (b₀ * p.1) • (endW H u cylInf p - R.x (1 * R.T * p.2 + c₀))) →
      ∀ ε > 0, ∃ s₀ : ℝ, ∀ s ≥ s₀, ∀ t : ℝ, ‖endW H u cylInf (s, t) - R.x (1 * R.T * t + c₀)‖ ≤ ε := by
    intro R c₀ b₀ hb₀ hz ε hε
    obtain ⟨s₀, hs₀⟩ := hz ε hε
    refine ⟨max s₀ 0, fun s hs t => ?_⟩
    have h1 := hs₀ s (le_trans (le_max_left _ _) hs) t
    simp only at h1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
    have hs0 : 0 ≤ s := le_trans (le_max_right _ _) hs
    have h2 : 1 ≤ Real.exp (b₀ * s) := Real.one_le_exp (by positivity)
    nlinarith [norm_nonneg (endW H u cylInf (s, t) - R.x (1 * R.T * t + c₀))]
  have key : ∀ t : ℝ, P.x (P.T * t + c) = P'.x (P.T * t + c') := by
    intro t
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨s₁, hs₁⟩ := hclose P c b hb h (ε / 2) (half_pos hε)
    obtain ⟨s₂, hs₂⟩ := hclose P' c' b' hb' h' (ε / 2) (half_pos hε)
    have h1 := hs₁ (max s₁ s₂) (le_max_left _ _) t
    have h2 := hs₂ (max s₁ s₂) (le_max_right _ _) t
    rw [one_mul] at h1 h2
    rw [← hT] at h2
    rw [dist_eq_norm]
    calc ‖P.x (P.T * t + c) - P'.x (P.T * t + c')‖
        ≤ ‖endW H u cylInf (max s₁ s₂, t) - P.x (P.T * t + c)‖ +
          ‖endW H u cylInf (max s₁ s₂, t) - P'.x (P.T * t + c')‖ := by
          rw [← norm_neg (endW H u cylInf (max s₁ s₂, t) - P.x (P.T * t + c))]
          refine (norm_add_le _ _).trans_eq' ?_
          congr 1
          abel
      _ ≤ ε := by linarith
  have hshift : ∀ τ : ℝ, P.x τ = P'.x (τ + (c' - c)) := by
    intro τ
    have := key ((τ - c) / P.T)
    rw [mul_div_cancel₀ _ P.T_pos.ne'] at this
    rw [sub_add_cancel] at this
    rw [this]
    congr 1
    ring
  intro τ hτ0 hτT heq
  have h1 : P'.x (τ + (c' - c)) = P'.x (0 + (c' - c)) := by
    rw [← hshift, ← hshift]; exact heq
  have h2 := lp_orbit_shift H hH P' _ _ h1 (-(c' - c))
  simp only [add_neg_cancel_right, add_neg_cancel] at h2
  exact hprime τ hτ0 (hT ▸ hτT) (by simpa using h2)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V 1)
    (hfast : IsFastPlane H J u) (P : ReebOrbit H) (hnd : IsNondegenerateEnd H u cylInf P 1) :
    P.IsPrime :=
  isPrime_of_isFastPlane_of_isNondegenerateEnd_aux H hH J hJ u hfast P hnd
