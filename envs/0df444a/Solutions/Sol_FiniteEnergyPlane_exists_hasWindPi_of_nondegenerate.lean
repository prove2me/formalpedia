-- Prove2me | solution 1 for FiniteEnergyPlane.exists_hasWindPi_of_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-02T20:30:45.878055+00:00
-- url     : https://prove2.me/submissions/87260940-f3df-46d8-8816-6cda3d71f352

import Definitions.Def_FiniteEnergyPlane_Winding
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Theorems.Thm_FiniteEnergyPlane_exists_ball_piDs_eq_zero_or_isolated
import Theorems.Thm_FiniteEnergyPlane_exists_ball_piDs_ne_zero_of_isNondegenerateEnd
import Theorems.Thm_FiniteEnergyPlane_exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

lemma w14_energy_mono (H : V 1 → ℝ) {U W : Set ℂ} (h : W ⊆ U) (u : ℂ → V 1) :
    energy H W u ≤ energy H U u := by
  unfold energy
  exact iSup₂_mono fun φ _ => lintegral_mono_set h

lemma w14_restrict {H : V 1 → ℝ} {J : V 1 → V 1 →L[ℝ] V 1} {U W : Set ℂ} {u : ℂ → V 1}
    (hu : IsFiniteEnergyCurve H J U u) (h : W ⊆ U) : IsFiniteEnergyCurve H J W u :=
  ⟨hu.1.mono h, fun z hz => hu.2.1 z (h hz), fun z hz => hu.2.2.1 z (h hz),
    lt_of_le_of_lt (w14_energy_mono H h u) hu.2.2.2⟩

lemma w14_exists_ne (z : ℂ) {r : ℝ} (hr : 0 < r) : ∃ w ∈ ball z r, w ≠ z := by
  refine ⟨z + ((r / 2 : ℝ) : ℂ), ?_, ?_⟩
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  · intro h
    have h2 : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination h
    rw [Complex.ofReal_eq_zero] at h2
    linarith

/-- A small ball around `w ∈ ball z r \ {z}` inside `ball z r \ {z}`. -/
lemma w14_ball_sub {z w : ℂ} {r : ℝ} (hw : w ∈ ball z r) (hwz : w ≠ z) :
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

theorem exists_hasWindPi_of_nondegenerate_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1)
    (hΓ : ∀ z ∈ Γ, ∃ Pz : ReebOrbit H, IsNondegenerateEnd H u (cylEndAt z) Pz (-1))
    (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) :
    (∀ z ∉ Γ, piDs H u z = 0 → ∃ m : ℤ, 1 ≤ m ∧ HasZeroIndex (piDs H u) z m) ∧
      ∃ k : ℤ, 0 ≤ k ∧ HasWindPi H u Γ k := by
  classical
  set U : Set ℂ := (↑Γ)ᶜ with hUdef
  have hUo : IsOpen U := Γ.finite_toSet.isClosed.isOpen_compl
  have hloc : ∀ z₀ ∈ U, ∃ r > (0 : ℝ), ball z₀ r ⊆ U ∧
      ((∀ z ∈ ball z₀ r, piDs H u z = 0) ∨
        ((∀ z ∈ ball z₀ r, z ≠ z₀ → piDs H u z ≠ 0) ∧
          (piDs H u z₀ = 0 → ∃ m : ℤ, 1 ≤ m ∧ HasZeroIndex (piDs H u) z₀ m))) :=
    fun z₀ hz => exists_ball_piDs_eq_zero_or_isolated H hH J hJ U hUo u hu.1 hu.2.1 hu.2.2.1 z₀ hz
  -- `A`: points near which `π ∂ₛu ≡ 0`; `B`: points that are isolated from the other zeros.
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
    obtain ⟨hpos, hsub⟩ := w14_ball_sub hw hwz
    exact ⟨hrU hw, _, hpos, fun v hv => hrU (hsub v hv).1,
      fun v hv _ => hz v (hsub v hv).1 (hsub v hv).2⟩
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    rintro z ⟨_, r₁, hr₁, h₁⟩ ⟨_, r₂, hr₂, _, h₂⟩
    obtain ⟨w, hw, hwz⟩ := w14_exists_ne z (lt_min hr₁ hr₂)
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
  -- `π ∂ₛu` has nonzero values in every ball around a point of `U`.
  have hnotA : ∀ z ∈ U, ∀ r > (0 : ℝ), ∃ w ∈ ball z r, piDs H u w ≠ 0 := by
    intro z hz r hr
    obtain ⟨_, r₀, hr₀, _, h₀⟩ := hUB hz
    obtain ⟨w, hw, hwz⟩ := w14_exists_ne z (lt_min hr hr₀)
    exact ⟨w, ball_subset_ball (min_le_left _ _) hw,
      h₀ w (ball_subset_ball (min_le_right _ _) hw) hwz⟩
  -- Part 1: local indices.
  have part1 : ∀ z ∉ Γ, piDs H u z = 0 → ∃ m : ℤ, 1 ≤ m ∧ HasZeroIndex (piDs H u) z m := by
    intro z hzΓ hz0
    obtain ⟨r, hr, _, h | ⟨_, h⟩⟩ := hloc z hzΓ
    · obtain ⟨w, hw, hw0⟩ := hnotA z hzΓ r hr
      exact absurd (h w hw) hw0
    · exact h hz0
  refine ⟨part1, ?_⟩
  -- Finite punctures: no zeros on a punctured disc.
  have hpunct : ∀ z ∈ Γ, ∃ ρ > (0 : ℝ), ∀ w ∈ ball z ρ \ {z}, piDs H u w ≠ 0 := by
    intro z hz
    have hopen : IsOpen ((↑(Γ.erase z) : Set ℂ)ᶜ) := (Γ.erase z).finite_toSet.isClosed.isOpen_compl
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.1 hopen z (by simp)
    have hsubU : ball z δ \ {z} ⊆ U := by
      rintro w ⟨hw, hwz⟩ hwΓ
      exact hδsub hw (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hwz, hwΓ⟩))
    obtain ⟨Pz, hPz⟩ := hΓ z hz
    refine exists_ball_piDs_ne_zero_of_isNondegenerateEnd H hH J hJ z δ hδ u
      (w14_restrict hu hsubU) Pz (-1) (Or.inr rfl) hPz ?_
    intro ρ hρ
    obtain ⟨p, hp, hpz⟩ := w14_exists_ne z (lt_min hρ hδ)
    obtain ⟨hpos, hsub⟩ := w14_ball_sub hp hpz
    have hpU : p ∈ U := hsubU ⟨ball_subset_ball (min_le_right _ _) hp, hpz⟩
    obtain ⟨w, hw, hw0⟩ := hnotA p hpU _ hpos
    exact ⟨w, ⟨ball_subset_ball (min_le_left _ _) (hsub w hw).1, (hsub w hw).2⟩, hw0⟩
  choose! ρ hρpos hρ using hpunct
  -- The puncture at `∞`.
  set R₀ : ℝ := ∑ z ∈ Γ, ‖z‖ with hR₀
  have hR₀nn : 0 ≤ R₀ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hfarU : {z : ℂ | R₀ < ‖z‖} ⊆ U := by
    intro z hz hzΓ
    have := Finset.single_le_sum (f := fun z : ℂ => ‖z‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_coe.1 hzΓ)
    exact absurd hz (not_lt.2 this)
  obtain ⟨R₁, hR₁⟩ := exists_piDs_ne_zero_of_isNondegenerateEnd_cylInf H hH J hJ R₀ u
    (w14_restrict hu hfarU) Pinf 1 (Or.inl rfl) hinf (by
      intro R'
      set p : ℂ := ((max R' R₀ + 2 : ℝ) : ℂ)
      have hpn : ‖p‖ = max R' R₀ + 2 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
        linarith [le_max_right R' R₀]
      have hpU : p ∈ U := hfarU (by
        show R₀ < ‖p‖
        rw [hpn]; linarith [le_max_right R' R₀])
      obtain ⟨w, hw, hw0⟩ := hnotA p hpU 1 one_pos
      refine ⟨w, ?_, hw0⟩
      have h1 := mem_ball.1 hw
      rw [dist_eq_norm] at h1
      have h2 := norm_sub_norm_le p w
      rw [norm_sub_rev] at h1
      linarith [le_max_left R' R₀])
  -- The zero set lies in a compact subset of `U` and is discrete, hence finite.
  set K : Set ℂ := closedBall 0 (max R₁ 0) \ ⋃ z ∈ Γ, ball z (ρ z) with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall _ _).diff (isOpen_biUnion fun _ _ => isOpen_ball)
  have hKU : K ⊆ U := by
    rintro x ⟨_, hx⟩ hxΓ
    exact hx (Set.mem_biUnion (Finset.mem_coe.1 hxΓ) (mem_ball_self (hρpos x hxΓ)))
  set Zs : Set ℂ := {z | z ∉ Γ ∧ piDs H u z = 0} with hZs
  have hZK : Zs ⊆ K := by
    rintro z ⟨hzΓ, hz0⟩
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      by_contra hlt
      exact hR₁ z (lt_of_le_of_lt (le_max_left _ _) (not_le.1 hlt)) hz0
    · intro hz
      obtain ⟨z', hz', hzb⟩ := Set.mem_iUnion₂.1 hz
      have hne' : z ≠ z' := fun h => hzΓ (h ▸ hz')
      exact hρ z' hz' z ⟨hzb, hne'⟩ hz0
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
  choose! idx hidx1 hidx2 using part1
  refine ⟨∑ z ∈ hfin.toFinset, idx z, Finset.sum_nonneg fun z hz => ?_,
    hfin.toFinset, fun z => ?_, idx, fun z hz => ?_, rfl⟩
  · rw [Set.Finite.mem_toFinset] at hz
    exact le_trans zero_le_one (hidx1 z hz.1 hz.2)
  · rw [Set.Finite.mem_toFinset]
    rfl
  · rw [Set.Finite.mem_toFinset] at hz
    exact hidx2 z hz.1 hz.2

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1)
    (hΓ : ∀ z ∈ Γ, ∃ Pz : ReebOrbit H, IsNondegenerateEnd H u (cylEndAt z) Pz (-1))
    (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) :
    (∀ z ∉ Γ, piDs H u z = 0 → ∃ m : ℤ, 1 ≤ m ∧ HasZeroIndex (piDs H u) z m) ∧
      ∃ k : ℤ, 0 ≤ k ∧ HasWindPi H u Γ k :=
  exists_hasWindPi_of_nondegenerate_aux H hH J hJ Γ u hu Pinf hinf hΓ hne
