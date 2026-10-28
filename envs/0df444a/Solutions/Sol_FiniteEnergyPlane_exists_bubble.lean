-- Prove2me | solution 1 for FiniteEnergyPlane.exists_bubble
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-25T17:58:19.262062+00:00
-- url     : https://prove2.me/submissions/c1d410cb-6a58-49b7-9785-34a22a2b3e7a

import Definitions.Def_FiniteEnergyPlane_Setting
import Theorems.Thm_FiniteEnergyPlane_exists_blowup_points
import Theorems.Thm_FiniteEnergyPlane_exists_closedBall_subset_of_away
import Theorems.Thm_FiniteEnergyPlane_rescale_isFiniteEnergyCurve
import Theorems.Thm_FiniteEnergyPlane_exists_plane_of_gradNorm_le
import Theorems.Thm_FiniteEnergyPlane_plane_asymptotics
import Theorems.Thm_FiniteEnergyPlane_jtilde_isAlmostComplexOn



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Bubbling-off points (Hryniewicz 2014, Lemma 2.20). -/
theorem exists_bubble_aux {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (U : ℕ → Set ℂ)
    (hUo : ∀ k, IsOpen (U k)) (hUmono : Monotone U) (hUsub : ∀ k, U k ⊆ (↑Γ)ᶜ)
    (hUunion : ⋃ k, U k = (↑Γ)ᶜ) (u : ℕ → ℂ → V n)
    (hu : ∀ k, IsFiniteEnergyCurve H J (U k) (u k)) (C : ℝ)
    (hC : ∀ k, energy H (U k) (u k) ≤ ENNReal.ofReal C) (z : ℕ → ℂ) (hz : ∀ k, z k ∈ U k)
    (hblow : Tendsto (fun k => gradNorm H (u k) (z k)) atTop atTop)
    (haway : ∃ δ : ℝ, 0 < δ ∧ ∀ k, ∀ γ ∈ Γ, δ ≤ ‖z k - γ‖)
    (hbdd : (∃ R : ℝ, ∀ k, ‖z k‖ ≤ R) ∨ ∃ m : ℕ, ∃ R : ℝ, {w : ℂ | R < ‖w‖} ⊆ U m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z' : ℕ → ℂ, ∃ r : ℕ → ℝ, ∃ P : ReebOrbit H,
      Tendsto (fun j => ‖z (φ j) - z' j‖) atTop (𝓝 0) ∧ (∀ j, 0 < r j) ∧
      Tendsto r atTop (𝓝 0) ∧ (∀ j, ball (z' j) (r j) ⊆ U (φ j)) ∧ P.T ≤ C ∧
      ENNReal.ofReal P.T ≤
        limsup (fun j => dlambdaEnergy H (ball (z' j) (r j)) (u (φ j))) atTop := by
  classical
  obtain ⟨-, hprojs, haCs, -, -⟩ := jtilde_isAlmostComplexOn H hH J hJ
  obtain ⟨ρ₀, hρ₀, m, hm⟩ :=
    exists_closedBall_subset_of_away Γ U hUo hUmono hUunion z haway hbdd
  obtain ⟨m', hm'⟩ := eventually_atTop.1 (hblow.eventually (eventually_gt_atTop (0 : ℝ)))
  set N := max m m' with hN
  -- shifted data
  set uu : ℕ → ℂ → V n := fun k => u (k + N) with huu
  set UU : ℕ → Set ℂ := fun k => U (k + N) with hUU
  set zz : ℕ → ℂ := fun k => z (k + N) with hzz
  set g : ℕ → ℂ → ℝ := fun k => gradNorm H (uu k) with hg
  have hgc : ∀ k, ContinuousOn (g k) (UU k) := by
    intro k
    obtain ⟨hsm, hne, -, -⟩ := hu (k + N)
    have ho := hUo (k + N)
    have ha : ContDiffOn ℝ ∞ (fun z => aCoord H (u (k + N) z)) (U (k + N)) :=
      haCs.comp hsm (fun z hz => hne z hz)
    have hp : ContDiffOn ℝ ∞ (fun z => proj H (u (k + N) z)) (U (k + N)) :=
      hprojs.comp hsm (fun z hz => hne z hz)
    exact (ha.continuousOn_fderiv_of_isOpen ho (by simp)).norm.add
      (hp.continuousOn_fderiv_of_isOpen ho (by simp)).norm
  have hg0 : ∀ k w, 0 ≤ g k w := fun k w => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hgpos : ∀ k, 0 < g k (zz k) := fun k => hm' (k + N) (by omega)
  have hgblow : Tendsto (fun k => g k (zz k)) atTop atTop :=
    hblow.comp (tendsto_add_atTop_nat N)
  have hball : ∀ k, closedBall (zz k) ρ₀ ⊆ UU k := fun k => hm (k + N) (by omega)
  obtain ⟨ζ, ε, hε, hε0, hεR, hzζ, hRpos, hsub, hdbl⟩ :=
    exists_blowup_points g UU zz ρ₀ hρ₀ hball hgc hg0 hgpos hgblow
  set R : ℕ → ℝ := fun k => g k (ζ k) with hR
  set a : ℕ → ℝ := fun k => aCoord H (uu k (ζ k)) with ha
  set c : ℕ → ℝ := fun k => Real.exp (-2 * a k) with hc
  have hcpos : ∀ k, 0 < c k := fun k => Real.exp_pos _
  set v : ℕ → ℂ → V n := fun k w => c k • uu k (ζ k + (R k)⁻¹ • w) with hv
  set ρ : ℕ → ℝ := fun k => ε k * R k with hρ
  have hD := fun k => rescale_isFiniteEnergyCurve H hH J hJ (UU k) (hUo (k + N)) (uu k)
    (hu (k + N)) (ζ k) (R k)⁻¹ (inv_pos.2 (hRpos k)) (c k) (hcpos k)
  -- points of `ball 0 (ρ k)` land in `closedBall (ζ k) (ε k)`
  have hmem : ∀ k, ∀ w ∈ ball (0 : ℂ) (ρ k), ζ k + (R k)⁻¹ • w ∈ ball (ζ k) (ε k) := by
    intro k w hw
    rw [mem_ball_zero_iff] at hw
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 (hRpos k)), inv_mul_lt_iff₀ (hRpos k)]
    simpa [hρ, mul_comm] using hw
  have hballU : ∀ k, ball (ζ k) (ε k) ⊆ UU k := fun k => ball_subset_closedBall.trans (hsub k)
  have hpre : ∀ k, ball (0 : ℂ) (ρ k) ⊆ {w | ζ k + (R k)⁻¹ • w ∈ UU k} :=
    fun k w hw => hballU k (hmem k w hw)
  -- the rescaled curves
  have hvfe : ∀ k, IsFiniteEnergyCurve H J (ball 0 (ρ k)) (v k) := by
    intro k
    obtain ⟨⟨h1, h2, h3, h4⟩, -, -, -⟩ := hD k
    refine ⟨h1.mono (hpre k), fun w hw => h2 w (hpre k hw), fun w hw => h3 w (hpre k hw),
      lt_of_le_of_lt ?_ h4⟩
    exact iSup₂_mono fun φ _ => lintegral_mono_set (hpre k)
  have hvC : ∀ k, energy H (ball 0 (ρ k)) (v k) ≤ ENNReal.ofReal C := by
    intro k
    obtain ⟨-, -, -, hE⟩ := hD k
    calc energy H (ball 0 (ρ k)) (v k)
        ≤ energy H {w | ζ k + (R k)⁻¹ • w ∈ UU k} (v k) :=
          iSup₂_mono fun φ _ => lintegral_mono_set (hpre k)
      _ = energy H (UU k) (uu k) := (hE (UU k) subset_rfl (hUo (k + N)).measurableSet).1
      _ ≤ ENNReal.ofReal C := hC (k + N)
  have hvgrad : ∀ k, ∀ w ∈ ball (0 : ℂ) (ρ k), gradNorm H (v k) w ≤ 2 := by
    intro k w hw
    obtain ⟨-, -, hG, -⟩ := hD k
    rw [hG w (hpre k hw)]
    have h := hdbl k _ (ball_subset_closedBall (hmem k w hw))
    have hi := inv_pos.2 (hRpos k)
    calc (R k)⁻¹ * gradNorm H (uu k) (ζ k + (R k)⁻¹ • w) ≤ (R k)⁻¹ * (2 * R k) :=
          mul_le_mul_of_nonneg_left h hi.le
      _ = 2 := by rw [mul_left_comm, inv_mul_cancel₀ (hRpos k).ne', mul_one]
  have hεR' : Tendsto ρ atTop atTop := hεR
  have h0pre : ∀ k, ζ k + (R k)⁻¹ • (0 : ℂ) ∈ UU k := by
    intro k
    rw [smul_zero, add_zero]
    exact hsub k (mem_closedBall_self (hε k).le)
  have hva0 : ∀ k, aCoord H (v k 0) = 0 := by
    intro k
    obtain ⟨-, hA, -, -⟩ := hD k
    show aCoord H (c k • uu k (ζ k + (R k)⁻¹ • (0 : ℂ))) = 0
    rw [hA 0 (h0pre k)]
    simp only [smul_zero, add_zero, hc, Real.log_exp, ha]
    ring
  have hvg0 : ∀ k, gradNorm H (v k) 0 = 1 := by
    intro k
    obtain ⟨-, -, hG, -⟩ := hD k
    rw [hG 0 (h0pre k)]
    simp only [smul_zero, add_zero]
    exact inv_mul_cancel₀ (hRpos k).ne'
  obtain ⟨φ, hφ, w, hw, hnc, hEw, hlim⟩ := exists_plane_of_gradNorm_le H hH J hJ v ρ hεR' hvfe C
    hvC hvgrad hva0 hvg0
  -- the asymptotic orbit of the plane
  obtain ⟨hTpos, -, -, hseq⟩ := plane_asymptotics H hH J hJ w hw hnc
  obtain ⟨-, -, P, hPT, -⟩ := hseq (fun k => (k : ℝ)) tendsto_natCast_atTop_atTop
  set D := dlambdaEnergy H Set.univ w with hDdef
  have hDtop : D ≠ ⊤ := by
    intro h
    rw [h] at hTpos
    simp at hTpos
  have hTD : ENNReal.ofReal P.T = D := by rw [hPT, ENNReal.ofReal_toReal hDtop]
  -- `dλ`-energy is bounded by Hofer's energy
  have hDE : D ≤ energy H Set.univ w := by
    have hadm : Admissible (fun _ : ℝ => (1 : ℝ)) :=
      ⟨contDiff_const, monotone_const, fun _ => ⟨zero_le_one, le_rfl⟩⟩
    refine le_trans (le_of_eq ?_) (le_iSup₂ (f := fun (φ : ℝ → ℝ) (_ : Admissible φ) =>
      ∫⁻ z in Set.univ, ENNReal.ofReal (energyDensity H φ w z)) _ hadm)
    simp [hDdef, dlambdaEnergy, energyDensity, dlambdaDensity]
  have hTC : P.T ≤ C := by
    have h1 : ENNReal.ofReal P.T ≤ ENNReal.ofReal C := hTD ▸ hDE.trans hEw
    by_contra hlt
    push_neg at hlt
    have hC0 : C < 0 ∨ 0 ≤ C := lt_or_ge C 0
    rcases hC0 with hC0 | hC0
    · rw [ENNReal.ofReal_of_nonpos hC0.le, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at h1
      linarith [P.T_pos]
    · exact absurd ((ENNReal.ofReal_le_ofReal_iff hC0).1 h1) (not_le.2 hlt)
  -- exhaustion by balls
  have hballs : Tendsto (fun N : ℕ => dlambdaEnergy H (ball 0 N) w) atTop (𝓝 D) := by
    set μ := volume.withDensity (fun z => ENNReal.ofReal (dlambdaDensity H w z)) with hμ
    have hmono : Monotone (fun N : ℕ => ball (0 : ℂ) N) :=
      fun i j hij => ball_subset_ball (by exact_mod_cast hij)
    have hU : (⋃ N : ℕ, ball (0 : ℂ) N) = Set.univ := by
      refine Set.eq_univ_of_forall fun x => ?_
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      exact Set.mem_iUnion.2 ⟨N, mem_ball_zero_iff.2 hN⟩
    have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hU] at h
    have e1 : ∀ s : Set ℂ, MeasurableSet s → μ s = dlambdaEnergy H s w := fun s hs => by
      rw [hμ, withDensity_apply _ hs]; rfl
    rw [e1 _ MeasurableSet.univ] at h
    refine h.congr fun N => ?_
    exact e1 _ measurableSet_ball
  -- targets below `T`
  set t : ℕ → ℝ≥0∞ := fun j : ℕ => ENNReal.ofReal (P.T - 1 / ((j : ℝ) + 1)) with ht
  have htlt : ∀ j, t j < D := by
    intro j
    rw [← hTD, ht]
    exact (ENNReal.ofReal_lt_ofReal_iff P.T_pos).2 (by
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith)
  have htT : Tendsto t atTop (𝓝 (ENNReal.ofReal P.T)) := by
    refine ENNReal.tendsto_ofReal ?_
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub P.T
    simpa using this
  have hRad : ∀ j : ℕ, ∃ M : ℕ, (j : ℝ) + 1 ≤ M ∧ t j < dlambdaEnergy H (ball 0 M) w := by
    intro j
    obtain ⟨M, hM⟩ := eventually_atTop.1 ((hballs.eventually (lt_mem_nhds (htlt j))).and
      (eventually_ge_atTop (j + 1)))
    refine ⟨M, ?_, (hM M le_rfl).1⟩
    exact_mod_cast (hM M le_rfl).2
  choose M hMj hMt using hRad
  -- `R k → ∞`
  have hRtop : Tendsto R atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hεR
    filter_upwards [hε0.eventually (ge_mem_nhds (zero_lt_one : (0 : ℝ) < 1))] with k hk
    have := hRpos k
    simp only [hρ]
    nlinarith [hε k]
  have hφt := hφ.tendsto_atTop
  have hP : ∀ j : ℕ, ∀ᶠ i in atTop, t j < dlambdaEnergy H (ball 0 (M j)) (v (φ i)) ∧
      (M j : ℝ) < ρ (φ i) ∧ ((j : ℝ) + 1) * M j ≤ R (φ i) := by
    intro j
    have e1 := eventually_lt_of_lt_liminf ((hMt j).trans_le (hlim (M j)))
    have e2 := (hεR.comp hφt).eventually (eventually_gt_atTop (M j : ℝ))
    have e3 := (hRtop.comp hφt).eventually (eventually_ge_atTop (((j : ℝ) + 1) * M j))
    filter_upwards [e1, e2, e3] with i h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨ψ, hψ, hψP⟩ := extraction_forall_of_eventually hP
  have hφψ : Tendsto (fun j => φ (ψ j)) atTop atTop := hφt.comp hψ.tendsto_atTop
  have hMpos : ∀ j : ℕ, (0 : ℝ) < M j := fun j => by
    have := hMj j
    have : (0 : ℝ) ≤ j := j.cast_nonneg
    linarith
  refine ⟨fun j => φ (ψ j) + N, fun i j hij => by
      have := hφ (hψ hij)
      simp only
      omega,
    fun j => ζ (φ (ψ j)), fun j => M j / R (φ (ψ j)), P, ?_, ?_, ?_, ?_, hTC, ?_⟩
  · exact hzζ.comp hφψ
  · exact fun j => div_pos (hMpos j) (hRpos _)
  · refine squeeze_zero (fun j => (div_pos (hMpos j) (hRpos _)).le) (g := fun j : ℕ => 1 / ((j : ℝ) + 1))
      (fun j => ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    have h3 := (hψP j).2.2
    rw [div_le_div_iff₀ (hRpos _) (by positivity)]
    linarith
  · intro j
    refine (ball_subset_ball ?_).trans (hballU (φ (ψ j)))
    have h2 := (hψP j).2.1
    rw [div_le_iff₀ (hRpos _)]
    simp only [hρ] at h2
    linarith
  · -- the `dλ`-energy on the small balls
    have heq : ∀ j, dlambdaEnergy H (ball (ζ (φ (ψ j))) (M j / R (φ (ψ j)))) (u (φ (ψ j) + N)) =
        dlambdaEnergy H (ball 0 (M j)) (v (φ (ψ j))) := by
      intro j
      set k := φ (ψ j) with hk
      obtain ⟨-, -, -, hE⟩ := hD k
      have hsubk : ball (ζ k) (M j / R k) ⊆ UU k := by
        refine (ball_subset_ball ?_).trans (hballU k)
        have h2 := (hψP j).2.1
        rw [div_le_iff₀ (hRpos _)]
        simp only [hρ] at h2
        linarith
      have h := (hE _ hsubk measurableSet_ball).2
      have hset : {w : ℂ | ζ k + (R k)⁻¹ • w ∈ ball (ζ k) (M j / R k)} = ball 0 (M j) := by
        ext x
        simp only [Set.mem_setOf_eq, mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, sub_zero]
        rw [abs_inv, abs_of_pos (hRpos k), inv_mul_lt_iff₀ (hRpos k), mul_div_cancel₀ _ (hRpos k).ne']
      rw [hset] at h
      exact h.symm
    calc ENNReal.ofReal P.T = liminf t atTop := htT.liminf_eq.symm
      _ ≤ liminf (fun j => dlambdaEnergy H (ball (ζ (φ (ψ j))) (M j / R (φ (ψ j))))
            (u (φ (ψ j) + N))) atTop :=
          liminf_le_liminf (Eventually.of_forall fun j => by rw [heq j]; exact (hψP j).1.le)
      _ ≤ _ := liminf_le_limsup

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (U : ℕ → Set ℂ)
    (hUo : ∀ k, IsOpen (U k)) (hUmono : Monotone U) (hUsub : ∀ k, U k ⊆ (↑Γ)ᶜ)
    (hUunion : ⋃ k, U k = (↑Γ)ᶜ) (u : ℕ → ℂ → V n)
    (hu : ∀ k, IsFiniteEnergyCurve H J (U k) (u k)) (C : ℝ)
    (hC : ∀ k, energy H (U k) (u k) ≤ ENNReal.ofReal C) (z : ℕ → ℂ) (hz : ∀ k, z k ∈ U k)
    (hblow : Tendsto (fun k => gradNorm H (u k) (z k)) atTop atTop)
    (haway : ∃ δ : ℝ, 0 < δ ∧ ∀ k, ∀ γ ∈ Γ, δ ≤ ‖z k - γ‖)
    (hbdd : (∃ R : ℝ, ∀ k, ‖z k‖ ≤ R) ∨ ∃ m : ℕ, ∃ R : ℝ, {w : ℂ | R < ‖w‖} ⊆ U m) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ z' : ℕ → ℂ, ∃ r : ℕ → ℝ, ∃ P : ReebOrbit H,
      Tendsto (fun j => ‖z (φ j) - z' j‖) atTop (𝓝 0) ∧ (∀ j, 0 < r j) ∧
      Tendsto r atTop (𝓝 0) ∧ (∀ j, ball (z' j) (r j) ⊆ U (φ j)) ∧ P.T ≤ C ∧
      ENNReal.ofReal P.T ≤
        limsup (fun j => dlambdaEnergy H (ball (z' j) (r j)) (u (φ j))) atTop :=
  exists_bubble_aux H hH J hJ Γ U hUo hUmono hUsub hUunion u hu C hC z hz hblow haway hbdd
