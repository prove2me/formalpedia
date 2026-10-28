-- Prove2me | solution 2 for FiniteEnergyPlane.exists_bubble
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-25T23:48:11.615038+00:00
-- url     : https://prove2.me/submissions/4749540f-9d62-4817-8117-f6678528c264

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_plane_asymptotics
import Theorems.Thm_FiniteEnergyPlane_exists_bubbling_plane

open FiniteEnergyPlane MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hryniewicz 2014, Lemma 2.20, as a reduction to the bubbling-off analysis
(`exists_bubbling_plane`) and Hofer's asymptotics of finite-energy planes (`plane_asymptotics`):
the period of the asymptotic orbit of the bubble plane is its `dλ`-energy `T ≤ E ≤ C`, the
`dλ`-energies of the plane on the discs `B(0, m + 1)` tend to `T`, and a diagonal subsequence with
radii `r_m = (m + 1) / R_{j_m} → 0` captures them. -/
theorem solution  {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (U : ℕ → Set ℂ)
    (hUo : ∀ k, IsOpen (U k)) (hUmono : Monotone U) (hUsub : ∀ k, U k ⊆ (↑Γ)ᶜ)
    (hUunion : ⋃ k, U k = (↑Γ)ᶜ) (u : ℕ → ℂ → V n)
    (hu : ∀ k, IsFiniteEnergyCurve H J (U k) (u k)) (C : ℝ)
    (hC : ∀ k, energy H (U k) (u k) ≤ ENNReal.ofReal C) (z : ℕ → ℂ) (hz : ∀ k, z k ∈ U k)
    (hblow : Tendsto (fun k => gradNorm H (u k) (z k)) atTop atTop)
    (haway : ∃ δ : ℝ, 0 < δ ∧ ∀ k, ∀ γ ∈ Γ, δ ≤ ‖z k - γ‖)
    (hbdd : (∃ R : ℝ, ∀ k, ‖z k‖ ≤ R) ∨ ∃ m : ℕ, ∃ R : ℝ, {w : ℂ | R < ‖w‖} ⊆ U m)  :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z' : ℕ → ℂ, ∃ r : ℕ → ℝ, ∃ P : ReebOrbit H,
      Tendsto (fun j => ‖z (φ j) - z' j‖) atTop (𝓝 0) ∧ (∀ j, 0 < r j) ∧
      Tendsto r atTop (𝓝 0) ∧ (∀ j, ball (z' j) (r j) ⊆ U (φ j)) ∧ P.T ≤ C ∧
      ENNReal.ofReal P.T ≤
        limsup (fun j => dlambdaEnergy H (ball (z' j) (r j)) (u (φ j))) atTop := by
  obtain ⟨φ, hφ, z', R, v, hz', hR0, hR, hv, hnc, hvE, hloc⟩ :=
    exists_bubbling_plane H hH J hJ Γ U hUo hUmono hUsub hUunion u hu C hC z hz hblow haway hbdd
  obtain ⟨-, -, -, hasy⟩ := plane_asymptotics H hH J hJ v hv hnc
  obtain ⟨-, -, P, hPT, -⟩ := hasy (fun k => (k : ℝ)) tendsto_natCast_atTop_atTop
  set E := dlambdaEnergy H Set.univ v with hEdef
  -- the `dλ`-energy is the Hofer energy integrand for the admissible function `φ ≡ 1`
  have hEle : E ≤ energy H Set.univ v := by
    refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun φ (_ : Admissible φ) =>
      ∫⁻ z in Set.univ, ENNReal.ofReal (energyDensity H φ v z)) (fun _ => (1 : ℝ))
      ⟨contDiff_const, monotone_const, fun _ => ⟨zero_le_one, le_rfl⟩⟩)
    simp [hEdef, dlambdaEnergy, energyDensity, dlambdaDensity]
  have hEC : E ≤ ENNReal.ofReal C := hEle.trans hvE
  have hEtop : E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hEC
  have hPE : ENNReal.ofReal P.T = E := by rw [hPT, ENNReal.ofReal_toReal hEtop]
  have hTC : P.T ≤ C := by
    rcases (ENNReal.ofReal_le_ofReal_iff').1 (hPE ▸ hEC) with h | h
    · exact h
    · exact absurd h (not_le.2 P.T_pos)
  -- `dλ`-energies of the plane on the discs `B(0, m + 1)` increase to `E`
  set D : ℕ → ℝ≥0∞ := fun m => dlambdaEnergy H (ball 0 ((m : ℝ) + 1)) v with hDdef
  have hD : Tendsto D atTop (𝓝 E) := by
    have hmono : Monotone (fun m : ℕ => ball (0 : ℂ) ((m : ℝ) + 1)) := fun a b h =>
      ball_subset_ball (by gcongr)
    have hUn : ⋃ m : ℕ, ball (0 : ℂ) ((m : ℝ) + 1) = Set.univ := by
      refine Set.eq_univ_of_forall fun w => Set.mem_iUnion.2 ?_
      obtain ⟨m, hm⟩ := exists_nat_gt ‖w‖
      exact ⟨m, by rw [mem_ball, dist_zero_right]; linarith⟩
    have := tendsto_measure_iUnion_atTop
      (μ := volume.withDensity (fun z => ENNReal.ofReal (dlambdaDensity H v z))) hmono
    rw [hUn, withDensity_apply _ MeasurableSet.univ] at this
    exact this.congr fun m => withDensity_apply _ measurableSet_ball
  have hDE : ∀ m, D m ≤ E := fun m => lintegral_mono_set (Set.subset_univ _)
  -- diagonal subsequence
  set δ : ℕ → ℝ≥0∞ := fun m => ((m + 1 : ℕ) : ℝ≥0∞)⁻¹ with hδdef
  have hev : ∀ m : ℕ, ∀ᶠ j in atTop, ball (z' j) (((m : ℝ) + 1) / R j) ⊆ U (φ j) ∧
      ((m : ℝ) + 1) / R j < 1 / ((m : ℝ) + 1) ∧
      D m - δ m ≤ dlambdaEnergy H (ball (z' j) (((m : ℝ) + 1) / R j)) (u (φ j)) := by
    intro m
    have hρ : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    obtain ⟨h1, h2⟩ := hloc _ hρ
    refine h1.and (((hR.eventually_gt_atTop (((m : ℝ) + 1) ^ 2))).and ?_ |>.mono
      fun j hj => ⟨?_, hj.2⟩)
    · by_cases hD0 : D m = 0
      · exact Eventually.of_forall fun j => by rw [hD0, zero_tsub]; exact bot_le
      · have hlt : D m - δ m < D m := ENNReal.sub_lt_self (ne_top_of_le_ne_top hEtop (hDE m))
          hD0 (ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top _))
        exact (eventually_lt_of_lt_liminf (hlt.trans_le h2)).mono fun j hj => hj.le
    · rw [div_lt_div_iff₀ (hR0 j) hρ]; nlinarith [hj.1]
  obtain ⟨ψ, hψ, hψP⟩ := extraction_forall_of_eventually hev
  refine ⟨φ ∘ ψ, hφ.comp hψ, z' ∘ ψ, fun m => ((m : ℝ) + 1) / R (ψ m), P,
    hz'.comp hψ.tendsto_atTop, fun m => div_pos (by positivity) (hR0 _), ?_,
    fun m => (hψP m).1, hTC, ?_⟩
  · exact squeeze_zero (fun m => (div_pos (by positivity) (hR0 _)).le)
      (fun m => (hψP m).2.1.le) tendsto_one_div_add_atTop_nhds_zero_nat
  · have hδ : Tendsto δ atTop (𝓝 0) :=
      ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    have hlim := ENNReal.Tendsto.sub hD hδ (Or.inl hEtop)
    rw [tsub_zero] at hlim
    rw [hPE, ← hlim.limsup_eq]
    exact limsup_le_limsup (Eventually.of_forall fun m => (hψP m).2.2)
