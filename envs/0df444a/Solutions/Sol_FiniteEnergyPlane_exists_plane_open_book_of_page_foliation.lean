-- Prove2me | solution 1 for FiniteEnergyPlane.exists_plane_open_book_of_page_foliation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-25T14:14:39.007266+00:00
-- url     : https://prove2.me/submissions/b6445dd0-0973-4015-83e2-66ae4c00971f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_FiniteEnergyPlane_OpenBook
import Mathlib
import Theorems.Thm_FiniteEnergyPlane_isFastPlane_exp_smul_comp_affine
import Theorems.Thm_FiniteEnergyPlane_exists_periodic_family_of_transition
import Theorems.Thm_FiniteEnergyPlane_exists_contDiffOn_transition_of_pageMap_eq
import Theorems.Thm_FiniteEnergyPlane_proj_aCoord_exp_smul
import Theorems.Thm_FiniteEnergyPlane_contDiffOn_pageMap
import Theorems.Thm_FiniteEnergyPlane_injective_proj_of_isEmbeddedPlane



namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem exists_plane_open_book_of_page_foliation_aux (H : V 1 → ℝ)
    (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (L δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (U : ℝ × ℂ → V 1)
    (hU : IsPageFoliation H J P γ y l L δ U) :
    ∃ W : ℝ × ℂ → V 1, IsPlaneOpenBook H J P l W := by
  obtain ⟨hUf, hUp, hUr, hUb⟩ := hU
  set I : Set ℝ := Set.Ioo (-δ) (L + δ) with hIdef
  have hI : IsOpen I := isOpen_Ioo
  have hIo : IsOpen (I ×ˢ (Set.univ : Set ℂ)) := hI.prod isOpen_univ
  have h0I : (0 : ℝ) ∈ I := ⟨by linarith, by linarith⟩
  have hLI : L ∈ I := ⟨by linarith, by linarith⟩
  have hne : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), U p ≠ 0 := fun p hp =>
    (hUf.2 p.1 hp.1).1.1.1.2.1 p.2 trivial
  have hpd : ∀ p ∈ I ×ˢ (Set.univ : Set ℂ), DifferentiableAt ℝ (pageMap H U) p := fun p hp =>
    ((contDiffOn_pageMap H hH U I hI (hUf.1.of_le (by exact_mod_cast hl)) hne).contDiffAt
      (hIo.mem_nhds hp)).differentiableAt (by norm_num)
  obtain ⟨z₁, hz₁⟩ : ∃ z₁, pageMap H U (L, z₁) = pageMap H U (0, 0) := by
    have : pageMap H U (0, 0) ∈ Set.range (fun z => pageMap H U (L, z)) := by
      rw [hUr]; exact ⟨0, rfl⟩
    exact this
  obtain ⟨η, hη, -, β, c, A, B, hβ, hc, hA, hB, hβ0, hs⟩ :=
    exists_contDiffOn_transition_of_pageMap_eq H hH J hJ P hcz γ y hy l hl I hI U hUf
      (fun p hp => (hUp p hp).2.1) (fun p hp => (hUp p hp).2.2) 0 L h0I hLI 0 z₁ hz₁.symm
  obtain ⟨W, κ, b, a, d, hW, hper, hκ, ha, hd, hκ0, hκ1, hκa, hWe⟩ :=
    exists_periodic_family_of_transition l hl L δ η hL hδ hη U hUf.1 β c A B hβ hc hA hB hβ0
      (fun s h => (hs s h).1) (fun s h => (hs s h).2.1) (fun s h => (hs s h).2.2.1)
      (fun s h => (hs s h).2.2.2)
  have hl0 : ((l : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (by omega : l ≠ 0)
  -- the pages of `W`
  have hWp : ∀ (n : ℤ) (θ : ℝ), θ - n ∈ Set.Ioo (-1 / 3 : ℝ) 1 → ∀ z,
      pageMap H W (θ, z) = pageMap H U (κ (θ - n), a (θ - n) * z + d (θ - n)) := by
    intro n θ hθ z
    show proj H (W (θ, z)) = _
    rw [hWe n θ hθ z]
    exact (proj_aCoord_exp_smul H hH _ _
      (hne _ ⟨(hκa _ ⟨by linarith [hθ.1], by linarith [hθ.2]⟩).1, trivial⟩)).1
  have hWp0 : ∀ θ ∈ Set.Ico (0 : ℝ) 1, ∀ z,
      pageMap H W (θ, z) = pageMap H U (κ θ, a θ * z + d θ) := by
    intro θ hθ z
    have := hWp 0 θ (by rw [Int.cast_zero, sub_zero]; exact ⟨by linarith [hθ.1], hθ.2⟩) z
    simpa using this
  have hfl : ∀ θ : ℝ, θ - (⌊θ⌋ : ℤ) ∈ Set.Ioo (-1 / 3 : ℝ) 1 := by
    intro θ
    have h1 := Int.floor_le θ
    have h2 := Int.lt_floor_add_one θ
    exact ⟨by linarith, by linarith⟩
  have hm2 : ∀ t ∈ Set.Ioo (-1 / 3 : ℝ) 1, t ∈ Set.Ioo (-1 : ℝ) 2 := fun t ht =>
    ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- derivatives of the pages of `W`
  have hDW : ∀ p : ℝ × ℂ, ∃ q ∈ I ×ˢ (Set.univ : Set ℂ), ∃ (k : ℝ) (α m : ℂ), 0 < k ∧ α ≠ 0 ∧
      pageMap H W p = pageMap H U q ∧
      ∀ (x : ℝ) (v : ℂ), fderiv ℝ (pageMap H W) p (x, v) =
        fderiv ℝ (pageMap H U) q (k * x, α * v + (x : ℂ) * m) := by
    rintro ⟨θ, z⟩
    have hθ := hm2 _ (hfl θ)
    generalize hn : ⌊θ⌋ = n at hθ
    have hθ' : θ - n ∈ Set.Ioo (-1 / 3 : ℝ) 1 := hn ▸ hfl θ
    obtain ⟨j1, j2, j3⟩ := hκa _ hθ
    have hnh : Set.Ioo (-1 : ℝ) 2 ∈ 𝓝 (θ - n) := isOpen_Ioo.mem_nhds hθ
    have sh : HasDerivAt (fun x : ℝ => x - n) 1 θ := (hasDerivAt_id θ).sub_const _
    have fsh : HasFDerivAt (fun p : ℝ × ℂ => p.1 - n) (ContinuousLinearMap.fst ℝ ℝ ℂ) (θ, z) :=
      hasFDerivAt_fst.sub_const _
    have d1 : HasFDerivAt (fun p : ℝ × ℂ => κ (p.1 - n)) _ (θ, z) :=
      HasDerivAt.comp_hasFDerivAt (θ, z)
        ((hκ.contDiffAt hnh).differentiableAt hl0).hasDerivAt fsh
    have d2 : HasFDerivAt (fun p : ℝ × ℂ => a (p.1 - n))
        ((fderiv ℝ a (θ - n)).comp (ContinuousLinearMap.fst ℝ ℝ ℂ)) (θ, z) :=
      HasFDerivAt.comp (θ, z) (g := a) ((ha.contDiffAt hnh).differentiableAt hl0).hasFDerivAt fsh
    have d3 : HasFDerivAt (fun p : ℝ × ℂ => d (p.1 - n))
        ((fderiv ℝ d (θ - n)).comp (ContinuousLinearMap.fst ℝ ℝ ℂ)) (θ, z) :=
      HasFDerivAt.comp (θ, z) (g := d) ((hd.contDiffAt hnh).differentiableAt hl0).hasFDerivAt fsh
    have d4 := d1.prodMk ((d2.mul hasFDerivAt_snd).add d3)
    have hq : (κ (θ - n), a (θ - n) * z + d (θ - n)) ∈ I ×ˢ (Set.univ : Set ℂ) := ⟨j1, trivial⟩
    have d5 : HasFDerivAt (pageMap H W) _ (θ, z) :=
      (HasFDerivAt.comp (θ, z) (g := pageMap H U) (hpd _ hq).hasFDerivAt d4).congr_of_eventuallyEq (by
        have h6 : IsOpen {p : ℝ × ℂ | p.1 - n ∈ Set.Ioo (-1 / 3 : ℝ) 1} :=
          isOpen_Ioo.preimage (continuous_fst.sub continuous_const)
        filter_upwards [h6.mem_nhds (show (θ, z) ∈
          {p : ℝ × ℂ | p.1 - n ∈ Set.Ioo (-1 / 3 : ℝ) 1} from hθ')] with p hp
        exact hWp n p.1 hp p.2)
    refine ⟨_, hq, deriv κ (θ - n), a (θ - n), z * deriv a (θ - n) + deriv d (θ - n), j2, j3,
      hWp n θ hθ' z, fun x v => ?_⟩
    rw [d5.fderiv]
    have e1 : ∀ g : ℝ → ℂ, fderiv ℝ g (θ - n) x = (x : ℂ) * deriv g (θ - n) := fun g => by
      rw [fderiv_eq_smul_deriv, Complex.real_smul]
    show fderiv ℝ (pageMap H U) _ _ = _
    congr 1
    refine Prod.ext ?_ ?_
    · simp
    · simp [e1]
      ring
  -- `κ` on `[0, 1]`
  have hκm : StrictMonoOn κ (Set.Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1)
      (hκ.continuousOn.mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩) ?_
    intro t ht
    rw [interior_Icc] at ht
    exact (hκa t ⟨by linarith [ht.1], by linarith [ht.2]⟩).2.1
  have hκc : ContinuousOn κ (Set.Icc 0 1) :=
    hκ.continuousOn.mono fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- injectivity of the pages of `U` on `[0, L)`
  have hUi : ∀ s ∈ Set.Ico 0 L, ∀ s' ∈ Set.Ico 0 L, ∀ z z',
      pageMap H U (s, z) = pageMap H U (s', z') → s = s' ∧ z = z' := by
    have h00 : ∀ z z', pageMap H U (0, z) = pageMap H U (0, z') → z = z' := by
      intro z z' h
      obtain ⟨⟨h1, h2, -, -⟩, h3⟩ := hUf.2 0 h0I
      exact injective_proj_of_isEmbeddedPlane H hH J hJ P _ h1 h2 h3 h
    have h0s : ∀ s ∈ Set.Ioo 0 L, ∀ z z', pageMap H U (0, z) ≠ pageMap H U (s, z') := by
      intro s hs z z' h
      exact (hUb.mapsTo (x := (s, z')) ⟨hs, trivial⟩).2 (Or.inl ⟨z, h⟩)
    intro s hs s' hs' z z' h
    rcases hs.1.eq_or_lt with rfl | h1
    · rcases hs'.1.eq_or_lt with rfl | h2
      · exact ⟨rfl, h00 _ _ h⟩
      · exact absurd h (h0s s' ⟨h2, hs'.2⟩ z z')
    · rcases hs'.1.eq_or_lt with rfl | h2
      · exact absurd h.symm (h0s s ⟨h1, hs.2⟩ z' z)
      · have := hUb.injOn (x₁ := (s, z)) ⟨⟨h1, hs.2⟩, trivial⟩ (x₂ := (s', z'))
          ⟨⟨h2, hs'.2⟩, trivial⟩ h
        exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hκI : ∀ t ∈ Set.Ico (0 : ℝ) 1, κ t ∈ Set.Ico 0 L := by
    intro t ht
    constructor
    · rw [← hκ0]; exact hκm.monotoneOn ⟨le_rfl, zero_le_one⟩ ⟨ht.1, ht.2.le⟩ ht.1
    · rw [← hκ1]; exact hκm ⟨ht.1, ht.2.le⟩ ⟨zero_le_one, le_rfl⟩ ht.2
  have hκs : ∀ s ∈ Set.Ico 0 L, ∃ t ∈ Set.Ico (0 : ℝ) 1, κ t = s := by
    intro s hs
    have := intermediate_value_Ico (zero_le_one' ℝ) hκc
    rw [hκ0, hκ1] at this
    exact this hs
  have haI : ∀ t ∈ Set.Ico (0 : ℝ) 1, a t ≠ 0 := fun t ht =>
    (hκa t ⟨by linarith [ht.1], by linarith [ht.2]⟩).2.2
  refine ⟨W, hW, hper, fun θ => ?_, fun p => ?_, fun q hq hqP => ?_, fun p => ?_, fun p => ?_⟩
  · have hθ := hfl θ
    obtain ⟨j1, -, j3⟩ := hκa _ (hm2 _ hθ)
    have he : (fun z => W (θ, z)) = fun z => Real.exp (2 * b (θ - (⌊θ⌋ : ℤ))) •
        U (κ (θ - (⌊θ⌋ : ℤ)), a (θ - (⌊θ⌋ : ℤ)) * z + d (θ - (⌊θ⌋ : ℤ))) :=
      funext fun z => hWe ⌊θ⌋ θ hθ z
    rw [he]
    exact isFastPlane_exp_smul_comp_affine H hH J hJ P _ γ _ (hUf.2 _ j1) _ _ _ j3
  · obtain ⟨q, hq, -, -, -, -, -, h, -⟩ := hDW p
    rw [h]
    exact (hUp q hq).1
  · obtain ⟨s, hs, z, hz⟩ : ∃ s ∈ Set.Ico 0 L, ∃ z, pageMap H U (s, z) = q := by
      by_cases h : q ∈ Set.range (fun z => pageMap H U (0, z))
      · obtain ⟨z, hz⟩ := h
        exact ⟨0, ⟨le_rfl, hL⟩, z, hz⟩
      · obtain ⟨⟨s, z⟩, ⟨hs, -⟩, hz⟩ := hUb.surjOn (show q ∈ energySurface H \
          (Set.range (fun z => pageMap H U (0, z)) ∪ Set.range P.x) from
          ⟨hq, fun h' => h'.elim h hqP⟩)
        exact ⟨s, ⟨hs.1.le, hs.2⟩, z, hz⟩
    obtain ⟨t, ht, rfl⟩ := hκs s hs
    have hat := haI t ht
    refine ⟨(t, (a t)⁻¹ * (z - d t)), ⟨ht, ?_⟩, ?_⟩
    · rw [hWp0 t ht, ← hz]
      congr 2
      field_simp
      ring
    · rintro ⟨t', z'⟩ ⟨ht', h'⟩
      replace ht' : t' ∈ Set.Ico (0 : ℝ) 1 := ht'
      rw [hWp0 t' ht', ← hz] at h'
      obtain ⟨e1, e2⟩ := hUi _ (hκI t' ht') _ hs _ _ h'
      have e3 : t' = t := hκm.injOn ⟨ht'.1, ht'.2.le⟩ ⟨ht.1, ht.2.le⟩ e1
      subst e3
      rw [← e2]
      congr 1
      field_simp
      ring
  · obtain ⟨q, hq, k, α, m, hk, hα, -, hD⟩ := hDW p
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, v⟩ h
    rw [hD] at h
    have h1 := (hUp q hq).2.1 (h.trans (map_zero _).symm)
    have h2 : k * x = 0 := congrArg Prod.fst h1
    have hx : x = 0 := (mul_eq_zero.1 h2).resolve_left hk.ne'
    subst hx
    have h3 : α * v + ((0 : ℝ) : ℂ) * m = 0 := congrArg Prod.snd h1
    have hv : v = 0 := by simpa [hα] using h3
    rw [hv]; rfl
  · obtain ⟨q, hq, k, α, m, hk, hα, hpq, hD⟩ := hDW p
    obtain ⟨x, hx, v, hv⟩ := (hUp q hq).2.2
    refine ⟨x / k, div_pos hx hk, α⁻¹ * (v - ((x / k : ℝ) : ℂ) * m), ?_⟩
    rw [hD, hpq, ← hv]
    congr 1
    refine Prod.ext ?_ ?_
    · show k * (x / k) = x
      field_simp
    · show α * (α⁻¹ * (v - ((x / k : ℝ) : ℂ) * m)) + ((x / k : ℝ) : ℂ) * m = v
      rw [mul_inv_cancel_left₀ hα]; ring

end FiniteEnergyPlane

open FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

theorem solution (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (P : ReebOrbit H) (hcz : P.IsCZAtLeast 3) (γ : ℝ) (y : ℝ → V 1) (hy : IsReebTrajectory H y)
    (l : ℕ) (hl : 1 ≤ l) (L δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (U : ℝ × ℂ → V 1)
    (hU : IsPageFoliation H J P γ y l L δ U) :
    ∃ W : ℝ × ℂ → V 1, IsPlaneOpenBook H J P l W :=
  exists_plane_open_book_of_page_foliation_aux H hH J hJ P hcz γ y hy l hl L δ hL hδ U hU
