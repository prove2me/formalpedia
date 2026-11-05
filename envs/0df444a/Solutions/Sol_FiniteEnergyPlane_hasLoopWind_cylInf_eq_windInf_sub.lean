-- Prove2me | solution 1 for FiniteEnergyPlane.hasLoopWind_cylInf_eq_windInf_sub
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-04T20:16:10.831418+00:00
-- url     : https://prove2.me/submissions/760b9faf-0b92-4d37-abcf-ea762227d99f

import Definitions.Def_FiniteEnergyPlane_Compactness
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Theorems.Thm_FiniteEnergyPlane_exists_ball_piDs_eq_zero_or_isolated
import Theorems.Thm_FiniteEnergyPlane_exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf
import Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_unique
import Theorems.Thm_FiniteEnergyPlane_continuousOn_piDs
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_cylInf_of_hasLoopWind_circle
import Theorems.Thm_FiniteEnergyPlane_hasLoopWind_ccwLoop_annulus_eq_add_sum



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma wcm_energy_mono (H : V 1 → ℝ) {U W : Set ℂ} (h : W ⊆ U) (u : ℂ → V 1) :
    energy H W u ≤ energy H U u := by
  unfold energy
  exact iSup₂_mono fun φ _ => lintegral_mono_set h

lemma wcm_restrict {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {U W : Set ℂ} {u : ℂ → V 1}
    (hu : IsFiniteEnergyCurve H J U u) (h : W ⊆ U) : IsFiniteEnergyCurve H J W u :=
  ⟨hu.1.mono h, fun z hz => hu.2.1 z (h hz), fun z hz => hu.2.2.1 z (h hz),
    lt_of_le_of_lt (wcm_energy_mono H h u) hu.2.2.2⟩

lemma wcm_exists_ne (z : ℂ) {r : ℝ} (hr : 0 < r) : ∃ w ∈ ball z r, w ≠ z := by
  refine ⟨z + ((r / 2 : ℝ) : ℂ), ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  · intro h
    have h2 : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination h
    rw [Complex.ofReal_eq_zero] at h2
    linarith

lemma wcm_ball_sub {z w : ℂ} {r : ℝ} (hw : w ∈ ball z r) (hwz : w ≠ z) :
    0 < min (r - dist w z) (dist w z) ∧
      ∀ v ∈ ball w (min (r - dist w z) (dist w z)), v ∈ ball z r ∧ v ≠ z := by
  have hd : 0 < dist w z := dist_pos.2 hwz
  have hwr := mem_ball.1 hw
  refine ⟨lt_min (by linarith) hd, fun v hv => ⟨?_, ?_⟩⟩
  · have := mem_ball.1 hv
    rw [mem_ball]
    linarith [dist_triangle v w z, min_le_left (r - dist w z) (dist w z)]
  · intro hvz
    rw [hvz] at hv
    have := mem_ball.1 hv
    rw [dist_comm] at this
    linarith [min_le_right (r - dist w z) (dist w z)]

/-- The zeros of `piDs` beyond a radius enclosing `Γ` are finite, with local indices, and bounded. -/
lemma wcm_zeros (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1) (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) (R₀ : ℝ)
    (hΓ : ∀ z ∈ Γ, ‖z‖ < R₀) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ R₀ < ‖z‖ ∧ piDs H u z = 0) ∧
      ∃ idx : ℂ → ℤ, (∀ z ∈ Z, HasZeroIndex (piDs H u) z (idx z)) := by
  classical
  set U : Set ℂ := (↑Γ)ᶜ with hUdef
  have hUo : IsOpen U := Γ.finite_toSet.isClosed.isOpen_compl
  have hR₀U : ∀ z : ℂ, R₀ ≤ ‖z‖ → z ∈ U := fun z hz hzΓ => by
    have := hΓ z (Finset.mem_coe.1 hzΓ)
    linarith
  have hloc : ∀ z₀ ∈ U, ∃ r > (0 : ℝ), ball z₀ r ⊆ U ∧
      ((∀ z ∈ ball z₀ r, piDs H u z = 0) ∨
        ((∀ z ∈ ball z₀ r, z ≠ z₀ → piDs H u z ≠ 0) ∧
          (piDs H u z₀ = 0 → ∃ m : ℤ, 1 ≤ m ∧ HasZeroIndex (piDs H u) z₀ m))) :=
    fun z₀ hz => exists_ball_piDs_eq_zero_or_isolated H hH J hJ U hUo u hu.1 hu.2.1 hu.2.2.1 z₀ hz
  set A : Set ℂ := {z | z ∈ U ∧ ∃ r > (0 : ℝ), ∀ w ∈ ball z r, piDs H u w = 0} with hAdef
  set B : Set ℂ := {z | z ∈ U ∧ ∃ r > (0 : ℝ), ball z r ⊆ U ∧
    ∀ w ∈ ball z r, w ≠ z → piDs H u w ≠ 0} with hBdef
  have hAo : IsOpen A := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, r, hr, hz⟩
    obtain ⟨r', hr', hr'U⟩ := Metric.isOpen_iff.1 hUo z hzU
    refine ⟨min r r', lt_min hr hr', fun w hw => ⟨hr'U (ball_subset_ball (min_le_right _ _) hw), ?_⟩⟩
    have hw' := mem_ball.1 hw
    refine ⟨r - dist w z, sub_pos.2 (lt_of_lt_of_le hw' (min_le_left _ _)), fun v hv => hz v ?_⟩
    have := mem_ball.1 hv
    rw [mem_ball]
    linarith [dist_triangle v w z]
  have hBo : IsOpen B := by
    rw [Metric.isOpen_iff]
    rintro z ⟨hzU, r, hr, hrU, hz⟩
    refine ⟨r, hr, fun w hw => ?_⟩
    by_cases hwz : w = z
    · rw [hwz]; exact ⟨hzU, r, hr, hrU, hz⟩
    obtain ⟨hpos, hsub⟩ := wcm_ball_sub hw hwz
    exact ⟨hrU hw, _, hpos, fun v hv => hrU (hsub v hv).1,
      fun v hv _ => hz v (hsub v hv).1 (hsub v hv).2⟩
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro z ⟨_, r₁, hr₁, h₁⟩ ⟨_, r₂, hr₂, _, h₂⟩
    obtain ⟨w, hw, hwz⟩ := wcm_exists_ne z (lt_min hr₁ hr₂)
    exact h₂ w (ball_subset_ball (min_le_right _ _) hw) hwz
      (h₁ w (ball_subset_ball (min_le_left _ _) hw))
  have hUAB : U ⊆ A ∪ B := by
    intro z hz
    obtain ⟨r, hr, hrU, h | ⟨h, _⟩⟩ := hloc z hz
    · exact Or.inl ⟨hz, r, hr, h⟩
    · exact Or.inr ⟨hz, r, hr, hrU, h⟩
  have hpre : IsPreconnected U :=
    (Set.Countable.isConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      (Γ.countable_toSet)).isPreconnected
  have hUB : U ⊆ B := by
    rcases hpre.subset_or_subset hAo hBo hdisj hUAB with h | h
    · exfalso
      obtain ⟨z, hzΓ, hz⟩ := hne
      obtain ⟨_, r, hr, h0⟩ := h (show z ∈ U from hzΓ)
      exact hz (h0 z (mem_ball_self hr))
    · exact h
  have hnotA : ∀ z ∈ U, ∀ r > (0 : ℝ), ∃ w ∈ ball z r, piDs H u w ≠ 0 := by
    intro z hz r hr
    obtain ⟨_, r₀, hr₀, _, h₀⟩ := hUB hz
    obtain ⟨w, hw, hwz⟩ := wcm_exists_ne z (lt_min hr hr₀)
    exact ⟨w, ball_subset_ball (min_le_left _ _) hw,
      h₀ w (ball_subset_ball (min_le_right _ _) hw) hwz⟩
  have part1 : ∀ z ∈ U, piDs H u z = 0 → ∃ m : ℤ, HasZeroIndex (piDs H u) z m := by
    intro z hzΓ hz0
    obtain ⟨r, hr, _, h | ⟨_, h⟩⟩ := hloc z hzΓ
    · obtain ⟨w, hw, hw0⟩ := hnotA z hzΓ r hr
      exact absurd (h w hw) hw0
    · obtain ⟨m, -, hm⟩ := h hz0
      exact ⟨m, hm⟩
  have hfarU : {z : ℂ | R₀ < ‖z‖} ⊆ U := fun z hz => hR₀U z (le_of_lt hz)
  obtain ⟨R₁, hR₁⟩ := exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf H hH J hJ R₀ u
    (wcm_restrict hu hfarU) Pinf 1 (Or.inl rfl) hinf (by
      intro R'
      set p : ℂ := ((max R' R₀ + 2 + |R₀| : ℝ) : ℂ)
      have hmax : 0 ≤ max R' R₀ + |R₀| := by
        linarith [le_max_right R' R₀, neg_abs_le R₀]
      have hpn : ‖p‖ = max R' R₀ + 2 + |R₀| := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
        linarith
      have hpU : p ∈ U := hfarU (by
        show R₀ < ‖p‖
        rw [hpn]; linarith [le_max_right R' R₀, abs_nonneg R₀])
      obtain ⟨w, hw, hw0⟩ := hnotA p hpU 1 one_pos
      refine ⟨w, ?_, hw0⟩
      have h1 := mem_ball.1 hw
      rw [dist_eq_norm] at h1
      have h2 := norm_sub_norm_le p w
      rw [norm_sub_rev] at h1
      linarith [le_max_left R' R₀, abs_nonneg R₀])
  set K : Set ℂ := closedBall 0 (max R₁ R₀) \ ball 0 R₀ with hK
  have hKc : IsCompact K := (isCompact_closedBall _ _).diff isOpen_ball
  have hKU : K ⊆ U := by
    rintro x ⟨_, hx⟩
    refine hR₀U x ?_
    simpa using hx
  set Zs : Set ℂ := {z | R₀ < ‖z‖ ∧ piDs H u z = 0} with hZs
  have hZK : Zs ⊆ K := by
    rintro z ⟨hzR, hz0⟩
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      by_contra hlt
      exact hR₁ z (lt_of_le_of_lt (le_max_left _ _) (not_le.1 hlt)) hz0
    · simpa using hzR.le
  have hBx : ∀ x ∈ U, ∃ r > (0 : ℝ), ∀ w ∈ ball x r, w ≠ x → piDs H u w ≠ 0 := by
    intro x hx
    obtain ⟨_, r, hr, _, h⟩ := hUB hx
    exact ⟨r, hr, h⟩
  choose! rr hrrpos hrr using hBx
  obtain ⟨t, ht, hcover⟩ := hKc.elim_nhds_subcover (fun x => ball x (rr x))
    (fun x hx => ball_mem_nhds x (hrrpos x (hKU hx)))
  have hZt : Zs ⊆ ↑t := by
    intro z hz
    obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.1 (hcover (hZK hz))
    by_cases h : z = x
    · rw [h]; exact hx
    · exact absurd hz.2 (hrr x (hKU (ht x hx)) z hzx h)
  have hfin : Zs.Finite := t.finite_toSet.subset hZt
  choose! idx hidx using part1
  refine ⟨hfin.toFinset, fun z => ?_, idx, fun z hz => ?_⟩
  · rw [Set.Finite.mem_toFinset]
    rfl
  · rw [Set.Finite.mem_toFinset] at hz
    exact hidx z (hfarU hz.1) hz.2

theorem hasLoopWind_cylInf_eq_windInf_sub_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1) (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) (k : ℤ)
    (hk : HasWindInfAt H u cylInf 1 k) (s₀ : ℝ)
    (hΓ : ∀ z ∈ Γ, ‖z‖ < Real.exp (2 * π * s₀))
    (hcirc : ∀ z : ℂ, ‖z‖ = Real.exp (2 * π * s₀) → piDs H u z ≠ 0) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ Real.exp (2 * π * s₀) < ‖z‖ ∧ piDs H u z = 0) ∧
      ∃ idx : ℂ → ℤ, (∀ z ∈ Z, HasZeroIndex (piDs H u) z (idx z)) ∧
        HasLoopWind (fun t => xiCoordC H (endW H u cylInf (s₀, t))
      (piXi H (endW H u cylInf (s₀, t)) (fderiv ℝ (endW H u cylInf) (s₀, t) (1, 0)))) (k - ∑ z ∈ Z, idx z) := by
  classical
  have hpi := Real.pi_pos
  set R₀ : ℝ := Real.exp (2 * π * s₀) with hR₀
  have hR₀0 : 0 < R₀ := Real.exp_pos _
  obtain ⟨Z, hZ, idx, hidx⟩ := wcm_zeros H hH J hJ Γ u hu Pinf hinf hne R₀ hΓ
  refine ⟨Z, hZ, idx, hidx, ?_⟩
  obtain ⟨huc, hu0, hhol, -⟩ := hu
  set U : Set ℂ := (↑Γ)ᶜ with hUdef
  have hU : IsOpen U := Γ.finite_toSet.isClosed.isOpen_compl
  have hR₀U : ∀ z : ℂ, R₀ ≤ ‖z‖ → z ∈ U := fun z hz hzΓ => by
    have := hΓ z (Finset.mem_coe.1 hzΓ)
    linarith
  have hpc : ContinuousOn (piDs H u) U := continuousOn_piDs H hH U hU u huc hu0
  -- a big radius above all zeros, at which `hk` applies
  obtain ⟨s₁, hs₁⟩ := hk
  set s₂ : ℝ := max (max s₁ s₀ + 1) (Real.log (∑ z ∈ Z, ‖z‖ + 1) / (2 * π)) with hs₂
  set R₂ : ℝ := Real.exp (2 * π * s₂) with hR₂
  have hR₂0 : 0 < R₂ := Real.exp_pos _
  have hs₂s₁ : s₁ ≤ s₂ := by
    linarith [le_max_left s₁ s₀, le_max_left (max s₁ s₀ + 1) (Real.log (∑ z ∈ Z, ‖z‖ + 1) / (2 * π))]
  have hs₂s₀ : s₀ < s₂ := by
    linarith [le_max_right s₁ s₀, le_max_left (max s₁ s₀ + 1) (Real.log (∑ z ∈ Z, ‖z‖ + 1) / (2 * π))]
  have hR₀₂ : R₀ < R₂ := Real.exp_lt_exp.2 (by nlinarith)
  have hZnn : 0 ≤ ∑ z ∈ Z, ‖z‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hZR₂ : ∀ z ∈ Z, ‖z‖ < R₂ := by
    intro z hz
    have h1 := Finset.single_le_sum (f := fun z : ℂ => ‖z‖) (fun _ _ => norm_nonneg _) hz
    have h2 : Real.log (∑ z ∈ Z, ‖z‖ + 1) ≤ 2 * π * s₂ := by
      have := le_max_right (max s₁ s₀ + 1) (Real.log (∑ z ∈ Z, ‖z‖ + 1) / (2 * π))
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have h3 : ∑ z ∈ Z, ‖z‖ + 1 ≤ R₂ := by
      rw [hR₂, ← Real.exp_log (by positivity : (0 : ℝ) < ∑ z ∈ Z, ‖z‖ + 1)]
      exact Real.exp_le_exp.2 h2
    linarith
  -- the annulus minus `Z`
  set S : Set ℂ := {z : ℂ | R₀ ≤ ‖z‖ ∧ ‖z‖ ≤ R₂} \ ↑Z with hS
  have hSU : S ⊆ U := fun z hz => hR₀U z hz.1.1
  have hS0 : ∀ z ∈ S, piDs H u z ≠ 0 := by
    rintro z ⟨⟨h1, _⟩, hzZ⟩ h0
    rcases h1.lt_or_eq with h | h
    · exact hzZ ((hZ z).2 ⟨h, h0⟩)
    · exact hcirc z h.symm h0
  have hloop : ∀ ρ, 0 < ρ → (∀ t, ccwLoop ρ t ∈ U) → (∀ t, piDs H u (ccwLoop ρ t) ≠ 0) →
      ∃ m : ℤ, HasLoopWind (fun t => piDs H u (ccwLoop ρ t)) m := by
    intro ρ _ hmem hnz
    exact exists_hasLoopWind _ (hpc.comp_continuous (by unfold ccwLoop; fun_prop) hmem)
      (fun t => by
        have : ccwLoop ρ (t + 1) = ccwLoop ρ t := by
          unfold ccwLoop
          have h : ((2 * π * (t + 1) : ℝ) : ℂ) * Complex.I =
              ((2 * π * t : ℝ) : ℂ) * Complex.I + 2 * π * Complex.I := by
            push_cast; ring
          rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
        simp only [this]) hnz
  have hnorm : ∀ ρ t, 0 < ρ → ‖ccwLoop ρ t‖ = ρ := by
    intro ρ t hρ
    unfold ccwLoop
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  -- windings on the two boundary circles
  obtain ⟨m₀, hm₀⟩ := hloop R₀ hR₀0 (fun t => hR₀U _ (hnorm R₀ t hR₀0).ge)
    (fun t => hcirc _ (hnorm R₀ t hR₀0))
  have hgt : ∀ t, piDs H u (ccwLoop R₂ t) ≠ 0 := fun t => by
    refine hS0 _ ⟨⟨?_, ?_⟩, fun hz => ?_⟩
    · rw [hnorm R₂ t hR₂0]; exact hR₀₂.le
    · rw [hnorm R₂ t hR₂0]
    · have := hZR₂ _ hz
      rw [hnorm R₂ t hR₂0] at this
      exact lt_irrefl _ this
  have hann := hasLoopWind_ccwLoop_annulus_eq_add_sum (piDs H u) Z R₀ R₂ hR₀0 hR₀₂
    (fun p hp => ⟨((hZ p).1 hp).1, hZR₂ p hp⟩) (hpc.mono hSU) hS0 m₀ hm₀ idx
    (fun p hp => by
      obtain ⟨-, r, hr, -, hw⟩ := hidx p hp
      exact ⟨r, hr, hw⟩)
  have hbig := hasLoopWind_cylInf_of_hasLoopWind_circle H hH J hJ U hU u huc hu0 hhol s₂
    (fun t => hR₀U _ (by rw [hnorm R₂ t hR₂0]; exact hR₀₂.le)) _ hann
  have hkbig := hs₁ s₂ hs₂s₁
  simp only [one_mul] at hkbig
  have hkeq := hasLoopWind_unique hbig hkbig
  have hsmall := hasLoopWind_cylInf_of_hasLoopWind_circle H hH J hJ U hU u huc hu0 hhol s₀
    (fun t => hR₀U _ (hnorm R₀ t hR₀0).ge) m₀ hm₀
  have harith : m₀ + 1 = k - ∑ z ∈ Z, idx z := by linarith
  rwa [harith] at hsmall

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1) (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) (k : ℤ)
    (hk : HasWindInfAt H u cylInf 1 k) (s₀ : ℝ)
    (hΓ : ∀ z ∈ Γ, ‖z‖ < Real.exp (2 * π * s₀))
    (hcirc : ∀ z : ℂ, ‖z‖ = Real.exp (2 * π * s₀) → piDs H u z ≠ 0) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ Real.exp (2 * π * s₀) < ‖z‖ ∧ piDs H u z = 0) ∧
      ∃ idx : ℂ → ℤ, (∀ z ∈ Z, HasZeroIndex (piDs H u) z (idx z)) ∧
        HasLoopWind (fun t => xiCoordC H (endW H u cylInf (s₀, t))
      (piXi H (endW H u cylInf (s₀, t)) (fderiv ℝ (endW H u cylInf) (s₀, t) (1, 0)))) (k - ∑ z ∈ Z, idx z) :=
  hasLoopWind_cylInf_eq_windInf_sub_aux H hH J hJ Γ u hu Pinf hinf hne k hk s₀ hΓ hcirc
