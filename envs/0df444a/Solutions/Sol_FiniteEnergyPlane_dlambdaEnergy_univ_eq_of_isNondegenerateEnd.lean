-- Prove2me | solution 1 for FiniteEnergyPlane.dlambdaEnergy_univ_eq_of_isNondegenerateEnd
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T17:56:00.353591+00:00
-- url     : https://prove2.me/submissions/f0705cdb-4c11-41e6-b6dc-3a0214178425

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_plane_asymptotics
import Theorems.Thm_FiniteEnergyPlane_exists_ne_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_reeb_spec



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem bu_liouville_smul {n : ℕ} (x v : V n) (c : ℝ) :
    liouville x (c • v) = c * liouville x v := by
  simp only [liouville, omega0, dot, Pi.smul_apply, smul_eq_mul]
  rw [mul_div_assoc', Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- The total `dλ`-energy of a plane with a nondegenerate end over `P` at `∞` is the period of `P`. -/
theorem dlambdaEnergy_univ_eq_of_isNondegenerateEnd_aux {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (P : ReebOrbit H) (hnd : IsNondegenerateEnd H u cylInf P 1) :
    dlambdaEnergy H Set.univ u = ENNReal.ofReal P.T := by
  have hnc := exists_ne_of_isNondegenerateEnd H u cylInf P one_ne_zero hnd
  obtain ⟨hpos, -, -, hseq⟩ := plane_asymptotics H hH J hJ u hu hnc
  set R : ℕ → ℝ := fun k => Real.exp (2 * π * k) with hR
  have hRt : Tendsto R atTop atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    exact tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  obtain ⟨φ, hφ, P', hT', c', hconv⟩ := hseq R hRt
  obtain ⟨d, c, b, hb, -, hW⟩ := hnd
  have hlim1 : ∀ t : ℝ, Tendsto (fun k => loopInS H u (ccwLoop (R (φ k))) t) atTop
      (𝓝 (P'.x (P'.T * t + c'))) := by
    intro t
    have := (hconv 0).tendsto_at t
    simpa using this
  have hlim2 : ∀ t : ℝ, Tendsto (fun k => loopInS H u (ccwLoop (R (φ k))) t) atTop
      (𝓝 (P.x (P.T * t + c))) := by
    intro t
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨s₀, hs₀⟩ := hW (ε / 2) (half_pos hε)
    obtain ⟨N₀, hN₀⟩ := exists_nat_ge (max s₀ 0)
    refine ⟨N₀, fun k hk => ?_⟩
    have hφk : N₀ ≤ φ k := hk.trans (hφ.id_le k)
    have hsk : max s₀ 0 ≤ ((φ k : ℕ) : ℝ) := hN₀.trans (by exact_mod_cast hφk)
    have h1 := hs₀ (φ k) ((le_max_left _ _).trans hsk) t
    have hs0 : (0 : ℝ) ≤ ((φ k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hexp : 1 ≤ Real.exp (b * ((φ k : ℕ) : ℝ)) := Real.one_le_exp (by positivity)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
    have h2 : ‖endW H u cylInf (((φ k : ℕ) : ℝ), t) - P.x (1 * P.T * t + c)‖ ≤ ε / 2 := by
      refine le_trans ?_ h1
      exact le_mul_of_one_le_left (norm_nonneg _) hexp
    rw [dist_eq_norm]
    have e : loopInS H u (ccwLoop (R (φ k))) t = endW H u cylInf (((φ k : ℕ) : ℝ), t) := rfl
    rw [e]
    rw [one_mul] at h2
    linarith
  have heq : ∀ t : ℝ, P'.x (P'.T * t + c') = P.x (P.T * t + c) := fun t =>
    tendsto_nhds_unique (hlim1 t) (hlim2 t)
  have hd' : ∀ (Q : ReebOrbit H) (e : ℝ), HasDerivAt (fun t => Q.x (Q.T * t + e))
      (Q.T • reeb H (Q.x e)) 0 := by
    intro Q e
    have hin : HasDerivAt (fun t : ℝ => Q.T * t + e) Q.T 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul Q.T).add_const e
    have h0 : HasDerivAt Q.x (reeb H (Q.x e)) (Q.T * 0 + e) := by simpa using Q.hasDerivAt e
    exact h0.scomp (0 : ℝ) hin
  have hfun : (fun t => P'.x (P'.T * t + c')) = fun t => P.x (P.T * t + c) := funext heq
  have h1 := hd' P' c'
  rw [hfun] at h1
  have huniq := h1.unique (hd' P c)
  have hpt : P'.x c' = P.x c := by simpa using heq 0
  rw [hpt] at huniq
  have hspec := (reeb_spec H hH (P.x c) (P.mem c)).2.1
  have hTT : P'.T = P.T := by
    have hL : liouville (P.x c) (P'.T • reeb H (P.x c)) = P'.T := by
      rw [bu_liouville_smul, hspec, mul_one]
    have hL2 : liouville (P.x c) (P.T • reeb H (P.x c)) = P.T := by
      rw [bu_liouville_smul, hspec, mul_one]
    rw [← hL, huniq, hL2]
  have htop : dlambdaEnergy H Set.univ u ≠ ⊤ := by
    intro h; rw [h] at hpos; simp at hpos
  rw [← hTT, hT', ENNReal.ofReal_toReal htop]

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n) (hu : IsFiniteEnergyCurve H J Set.univ u)
    (P : ReebOrbit H) (hnd : IsNondegenerateEnd H u cylInf P 1) :
    dlambdaEnergy H Set.univ u = ENNReal.ofReal P.T :=
  dlambdaEnergy_univ_eq_of_isNondegenerateEnd_aux H hH J hJ u hu P hnd
