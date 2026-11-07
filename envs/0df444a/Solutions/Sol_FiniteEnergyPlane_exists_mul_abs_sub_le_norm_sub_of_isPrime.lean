-- Prove2me | solution 1 for FiniteEnergyPlane.exists_mul_abs_sub_le_norm_sub_of_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-06T16:41:32.4255+00:00
-- url     : https://prove2.me/submissions/73262481-bdad-4df9-96ad-a2268e3dbe9d

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_lipschitzOnWith_reeb
import Theorems.Thm_FiniteEnergyPlane_ReebOrbit_contDiff_x
import Theorems.Thm_FiniteEnergyPlane_exists_mul_norm_sub_le_of_isCompact_pairs



namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff Real

/-- A periodic Reeb orbit passing twice through one point is periodic with the time difference. -/
theorem emb_orbit_shift {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (Q : ReebOrbit H)
    (σ₁ σ₂ : ℝ) (h : Q.x σ₁ = Q.x σ₂) (σ : ℝ) : Q.x (σ₁ + σ) = Q.x (σ₂ + σ) := by
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_reeb H hH
  have huniq : (fun s => Q.x (σ₁ + s)) = fun s => Q.x (σ₂ + s) := by
    refine ODE_solution_unique_univ (v := fun _ => reeb H) (s := fun _ => energySurface H)
      (K := K) (t₀ := 0) (fun _ => hK) (fun s => ⟨?_, Q.mem _⟩) (fun s => ⟨?_, Q.mem _⟩)
      (by simpa using h)
    · simpa using (Q.hasDerivAt (σ₁ + s)).comp_const_add σ₁ s
    · simpa using (Q.hasDerivAt (σ₂ + s)).comp_const_add σ₂ s
  exact congrFun huniq σ

/-- On a prime periodic Reeb orbit, `‖x(τ) - x(τ')‖` is bounded below by a multiple of `|τ - τ'|`
whenever `|τ - τ'| ≤ T / 2`. -/
theorem exists_mul_abs_sub_le_norm_sub_of_isPrime_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (hP : P.IsPrime) :
    ∃ c > 0, ∀ τ τ' : ℝ, |τ - τ'| ≤ P.T / 2 → c * |τ - τ'| ≤ ‖P.x τ - P.x τ'‖ := by
  have hT := P.T_pos
  have hperZ : ∀ (k : ℤ) (τ : ℝ), P.x (τ + k * P.T) = P.x τ := by
    intro k τ
    have hp : Function.Periodic P.x P.T := P.periodic
    simpa using (hp.int_mul k) τ
  -- injective on a period
  have hsep : ∀ τ τ' : ℝ, τ ≠ τ' → |τ - τ'| ≤ P.T / 2 → P.x τ ≠ P.x τ' := by
    intro τ τ' hne hle heq
    have hne' : τ - τ' ≠ 0 := sub_ne_zero.2 hne
    wlog hlt : τ' < τ generalizing τ τ'
    · exact this τ' τ hne.symm (by rwa [abs_sub_comm]) heq.symm (sub_ne_zero.2 hne.symm)
        (lt_of_le_of_ne (not_lt.1 hlt) hne)
    have h1 := emb_orbit_shift H hH P τ τ' heq (-τ')
    have h2 : P.x (τ - τ') = P.x 0 := by
      simpa [sub_eq_add_neg] using h1
    have h3 : τ - τ' ≤ P.T / 2 := (le_abs_self _).trans hle
    exact hP (τ - τ') (by linarith) (by linarith) h2
  -- the velocity does not vanish
  have hvel : ∀ τ : ℝ, reeb H (P.x τ) ≠ 0 := by
    intro τ h0
    obtain ⟨K, hK⟩ := exists_lipschitzOnWith_reeb H hH
    have huniq : (fun s => P.x (τ + s)) = fun _ => P.x τ := by
      refine ODE_solution_unique_univ (v := fun _ => reeb H) (s := fun _ => energySurface H)
        (K := K) (t₀ := 0) (fun _ => hK) (fun s => ⟨?_, P.mem _⟩) (fun s => ⟨?_, P.mem _⟩)
        (by simp)
      · simpa using (P.hasDerivAt (τ + s)).comp_const_add τ s
      · rw [h0]; exact hasDerivAt_const _ _
    have h1 : P.x (τ + P.T / 2) = P.x (τ + 0) := by
      rw [add_zero]; exact congrFun huniq _
    have h2 := emb_orbit_shift H hH P _ _ h1 (-τ)
    have h3 : P.x (P.T / 2) = P.x 0 := by
      have e1 : τ + P.T / 2 + -τ = P.T / 2 := by ring
      have e2 : τ + 0 + -τ = 0 := by ring
      rwa [e1, e2] at h2
    exact hP (P.T / 2) (by linarith) (by linarith) h3
  have hG : ContDiff ℝ 1 P.x :=
    (ReebOrbit.contDiff_x H hH P).of_le (by exact_mod_cast le_top)
  set Q : Set (ℝ × ℝ) := {p | p.1 ∈ Set.Icc 0 P.T ∧ |p.1 - p.2| ≤ P.T / 2} with hQdef
  have hQ : IsCompact Q := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_Icc.preimage continuous_fst).inter
        (isClosed_le (f := fun p : ℝ × ℝ => |p.1 - p.2|) (g := fun _ => P.T / 2)
          (by fun_prop) continuous_const)
    · refine (Metric.isBounded_closedBall (x := ((0 : ℝ), (0 : ℝ))) (r := 2 * P.T)).subset ?_
      rintro ⟨a, b⟩ ⟨⟨h0, h1⟩, h2⟩
      simp only at h0 h1 h2
      rw [show (((0 : ℝ), (0 : ℝ)) : ℝ × ℝ) = 0 from rfl, mem_closedBall_zero_iff, Prod.norm_def]
      have h3 := abs_le.1 h2
      simp only [Real.norm_eq_abs]
      refine max_le ?_ ?_
      · rw [abs_of_nonneg h0]; linarith
      · rw [abs_le]; constructor <;> linarith [h3.1, h3.2]
  obtain ⟨c, hc, hcQ⟩ := exists_mul_norm_sub_le_of_isCompact_pairs P.x hG Q hQ
    (fun p hp hne => hsep _ _ hne hp.2)
    (fun p _ _ => by
      have hd : HasDerivAt P.x (reeb H (P.x p.1)) p.1 := P.hasDerivAt _
      rw [hd.hasFDerivAt.fderiv]
      intro a b hab
      have hab' : a • reeb H (P.x p.1) = b • reeb H (P.x p.1) := by simpa using hab
      exact smul_left_injective ℝ (hvel p.1) hab')
  refine ⟨c, hc, fun τ τ' hle => ?_⟩
  -- shift `τ` into a period
  set k : ℤ := ⌊τ / P.T⌋ with hk
  have hk1 : (k : ℝ) * P.T ≤ τ := by
    have := Int.floor_le (τ / P.T)
    rw [le_div_iff₀ hT] at this
    exact this
  have hk2 : τ < ((k : ℝ) + 1) * P.T := by
    have := Int.lt_floor_add_one (τ / P.T)
    rw [div_lt_iff₀ hT] at this
    exact this
  have hmem := hcQ (τ + (-k : ℤ) * P.T, τ' + (-k : ℤ) * P.T) ⟨⟨by
      push_cast; nlinarith, by push_cast; nlinarith⟩, by
      simpa using hle⟩
  simp only [hperZ] at hmem
  have e : τ + ((-k : ℤ) : ℝ) * P.T - (τ' + ((-k : ℤ) : ℝ) * P.T) = τ - τ' := by ring
  rw [e, Real.norm_eq_abs] at hmem
  exact hmem

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (hP : P.IsPrime) :
    ∃ c > 0, ∀ τ τ' : ℝ, |τ - τ'| ≤ P.T / 2 → c * |τ - τ'| ≤ ‖P.x τ - P.x τ'‖ :=
  exists_mul_abs_sub_le_norm_sub_of_isPrime_aux H hH P hP
