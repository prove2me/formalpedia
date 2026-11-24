-- Prove2me | solution 1 for FiniteEnergyPlane.exists_isPageFamilyOn_Ioo_glue
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-23T22:37:35.647786+00:00
-- url     : https://prove2.me/submissions/d4bbc672-1fcd-4b8e-a3f3-3ee9a9a6089f

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_exists_contDiff_rotation_gauge
import Theorems.Thm_FiniteEnergyPlane_comp_exp_mul_mem_embeddedFastPlaneSet



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_isPageFamilyOn_Ioo_glue_aux (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (a s c d m : ℝ) (U W : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l (Set.Ioo a s) U)
    (hW : IsPageFamilyOn H J P γ y l (Set.Ioo c d) W)
    (hm : m ∈ Set.Ioo a s) (hm' : m ∈ Set.Ioo c d) :
    ∃ U' : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (Set.Ioo a d) U' ∧
      ∀ t ∈ Set.Ioc a m, ∀ z, U' (t, z) = U (t, z) := by
  obtain ⟨θ, hθ, hθU⟩ := exists_contDiff_rotation_gauge H hH J hJ P hcz γ y hy l hl
    (Set.Ioo a s) (Set.Ioo c d) isOpen_Ioo isOpen_Ioo (convex_Ioo _ _) (convex_Ioo _ _) U W hU hW
  obtain ⟨m₁, h1, h1'⟩ := exists_between (lt_min hm.2 hm'.2)
  obtain ⟨m₂, h2, h2'⟩ := exists_between h1'
  have h2s : m₂ < s := lt_of_lt_of_le h2' (min_le_left _ _)
  have h2d : m₂ < d := lt_of_lt_of_le h2' (min_le_right _ _)
  have hpos : 0 < m₂ - m₁ := by linarith
  obtain ⟨ham, hms⟩ := hm
  obtain ⟨hcm, hmd⟩ := hm'
  -- the cutoff
  let χ : ℝ → ℝ := fun t => 1 - Real.smoothTransition ((t - m₁) / (m₂ - m₁))
  have hχ : ContDiff ℝ l χ :=
    contDiff_const.sub (Real.smoothTransition.contDiff.comp
      ((contDiff_id.sub contDiff_const).div_const _))
  have hχ1 : ∀ t ≤ m₁, χ t = 1 := fun t ht => by
    show 1 - _ = _
    rw [Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le),
      sub_zero]
  have hχ0 : ∀ t ≥ m₂, χ t = 0 := fun t ht => by
    show 1 - _ = _
    rw [Real.smoothTransition.one_of_one_le ((one_le_div hpos).2 (by linarith)), sub_self]
  let θ' : ℝ → ℝ := fun t => χ t * θ t
  have hθ'1 : ∀ t ≤ m₁, θ' t = θ t := fun t ht => by show χ t * θ t = _; rw [hχ1 t ht, one_mul]
  have hθ' : ContDiffOn ℝ l θ' (Set.Ioo m d) := by
    intro t ht
    refine ContDiffAt.contDiffWithinAt ?_
    rcases lt_or_ge t s with hts | hts
    · refine hχ.contDiffAt.mul (hθ.contDiffAt ((isOpen_Ioo.inter isOpen_Ioo).mem_nhds ?_))
      exact ⟨⟨ham.trans ht.1, hts⟩, hcm.trans ht.1, ht.2⟩
    · refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [lt_mem_nhds (h2s.trans_le hts)] with r hr
      show χ r * θ r = 0
      rw [hχ0 r hr.le, zero_mul]
  let E : ℝ → ℂ := fun t => Complex.exp (((2 * π * θ' t : ℝ) : ℂ) * Complex.I)
  have hE : ContDiffOn ℝ l E (Set.Ioo m d) := by
    have h3 : ContDiffOn ℝ l (fun t => ((2 * π * θ' t : ℝ) : ℂ)) (Set.Ioo m d) :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul hθ')
    exact (h3.mul contDiffOn_const).cexp
  let W' : ℝ × ℂ → V 1 := fun p => W (p.1, E p.1 * p.2)
  have hW' : ContDiffOn ℝ l W' (Set.Ioo m d ×ˢ Set.univ) := by
    have hg : ContDiffOn ℝ l (fun p : ℝ × ℂ => (p.1, E p.1 * p.2)) (Set.Ioo m d ×ˢ Set.univ) := by
      refine contDiffOn_fst.prodMk (ContDiffOn.mul ?_ contDiffOn_snd)
      exact hE.comp contDiffOn_fst (fun p hp => hp.1)
    exact hW.1.comp hg (fun p hp => ⟨⟨hcm.trans hp.1.1, hp.1.2⟩, trivial⟩)
  let U' : ℝ × ℂ → V 1 := fun p => if p.1 < m₁ then U p else W' p
  have hU'U : ∀ p : ℝ × ℂ, p.1 < m₁ → U' p = U p := fun p hp => if_pos hp
  have hU'W : ∀ p : ℝ × ℂ, m < p.1 → U' p = W' p := by
    rintro ⟨t, z⟩ ht
    by_cases h : t < m₁
    · rw [hU'U _ h]
      have := hθU t ⟨⟨ham.trans ht, by linarith⟩, hcm.trans ht, by linarith⟩ z
      rw [this]
      show _ = W (t, Complex.exp (((2 * π * θ' t : ℝ) : ℂ) * Complex.I) * z)
      rw [hθ'1 t h.le]
    · exact if_neg h
  refine ⟨U', ⟨?_, ?_⟩, fun t ht z => hU'U _ (lt_of_le_of_lt ht.2 h1)⟩
  · rintro ⟨t, z⟩ ⟨ht, -⟩
    refine ContDiffAt.contDiffWithinAt ?_
    rcases lt_or_ge t m₁ with h | h
    · refine (hU.1.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨⟨ht.1, by show t < s; linarith⟩, trivial⟩)).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_Iio.preimage continuous_fst).mem_nhds
        (show (t, z) ∈ Prod.fst ⁻¹' Set.Iio m₁ from h)] with p hp
      exact hU'U p hp
    · refine (hW'.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨⟨by show m < t; linarith, ht.2⟩, trivial⟩)).congr_of_eventuallyEq ?_
      filter_upwards [(isOpen_Ioi.preimage continuous_fst).mem_nhds
        (show (t, z) ∈ Prod.fst ⁻¹' Set.Ioi m from lt_of_lt_of_le h1 h)] with p hp
      exact hU'W p hp
  · intro t ht
    rcases lt_or_ge t m₁ with h | h
    · have : (fun z => U' (t, z)) = fun z => U (t, z) := funext fun z => hU'U _ h
      rw [this]
      exact hU.2 t ⟨ht.1, by linarith⟩
    · have hmt : m < t := lt_of_lt_of_le h1 h
      have : (fun z => U' (t, z)) = fun z => W (t, E t * z) := funext fun z => hU'W _ hmt
      rw [this]
      exact comp_exp_mul_mem_embeddedFastPlaneSet H hH J hJ P {y t} γ _
        (hW.2 t ⟨hcm.trans hmt, ht.2⟩) (θ' t)

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (a s c d m : ℝ) (U W : ℝ × ℂ → V 1)
    (hU : IsPageFamilyOn H J P γ y l (Set.Ioo a s) U)
    (hW : IsPageFamilyOn H J P γ y l (Set.Ioo c d) W)
    (hm : m ∈ Set.Ioo a s) (hm' : m ∈ Set.Ioo c d) :
    ∃ U' : ℝ × ℂ → V 1, IsPageFamilyOn H J P γ y l (Set.Ioo a d) U' ∧
      ∀ t ∈ Set.Ioc a m, ∀ z, U' (t, z) = U (t, z) :=
  exists_isPageFamilyOn_Ioo_glue_aux H hH J hJ P hcz γ y hy l hl a s c d m U W hU hW hm hm'
