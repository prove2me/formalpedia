-- Prove2me | solution 1 for GagieRIndex.Kmers.sampled_character
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-10-11T20:47:44.989923+00:00
-- url     : https://prove2.me/submissions/a30d98bd-657c-4e40-84a7-e6c1bd1bd400

import Mathlib
import Definitions.Def_GagieRIndex_Locate_Core

set_option autoImplicit false

namespace SampledCharAux

variable (n : ℕ) (T SA : ℕ → ℕ)

/-- `textPos` maps `[1,n]` back into `[1,n]`. -/
theorem textPos_mem_Icc (h1n : 1 ≤ n)
    (hSA1 : ∀ p, 1 ≤ p → p ≤ n → 1 ≤ SA p ∧ SA p ≤ n)
    {p : ℕ} (hp : p ∈ Finset.Icc 1 n) :
    GagieRIndex.Locate.textPos n SA p ∈ Finset.Icc 1 n := by
  obtain ⟨h1p, hpn⟩ := Finset.mem_Icc.mp hp
  obtain ⟨hSAp1, hSApn⟩ := hSA1 p h1p hpn
  unfold GagieRIndex.Locate.textPos
  split
  · rw [Finset.mem_Icc]; exact ⟨h1n, le_rfl⟩
  · rw [Finset.mem_Icc]; constructor <;> omega

/-- `textPos` is injective on `[1,n]` (uses `SA` injectivity and range). -/
theorem textPos_injOn (h1n : 1 ≤ n)
    (hSA1 : ∀ p, 1 ≤ p → p ≤ n → 1 ≤ SA p ∧ SA p ≤ n)
    (hSAinj : Set.InjOn SA (Set.Icc 1 n)) :
    Set.InjOn (GagieRIndex.Locate.textPos n SA) ↑(Finset.Icc 1 n) := by
  intro x hx y hy hxy
  rw [Finset.mem_coe] at hx hy
  obtain ⟨h1x, hxn⟩ := Finset.mem_Icc.mp hx
  obtain ⟨h1y, hyn⟩ := Finset.mem_Icc.mp hy
  obtain ⟨hSAx1, hSAxn⟩ := hSA1 x h1x hxn
  obtain ⟨hSAy1, hSAyn⟩ := hSA1 y h1y hyn
  have hmemx : x ∈ Set.Icc 1 n := Set.mem_Icc.mpr ⟨h1x, hxn⟩
  have hmemy : y ∈ Set.Icc 1 n := Set.mem_Icc.mpr ⟨h1y, hyn⟩
  unfold GagieRIndex.Locate.textPos at hxy
  by_cases hxx : SA x = 1 <;> by_cases hyy : SA y = 1
  · rw [if_pos hxx, if_pos hyy] at hxy
    have hSx : SA x = SA y := by rw [hxx, hyy]
    exact hSAinj hmemx hmemy hSx
  · rw [if_pos hxx, if_neg hyy] at hxy
    omega
  · rw [if_neg hxx, if_pos hyy] at hxy
    omega
  · rw [if_neg hxx, if_neg hyy] at hxy
    have hSxy : SA x = SA y := by omega
    exact hSAinj hmemx hmemy hSxy

/-- `BWT[p]` is the character at text position `textPos p`. -/
theorem bwt_eq (p : ℕ) :
    GagieRIndex.Locate.bwt n T SA p = T (GagieRIndex.Locate.textPos n SA p) := by
  unfold GagieRIndex.Locate.bwt GagieRIndex.Locate.textPos
  by_cases h : SA p = 1 <;> simp [h]

/-- The image of `[1,n]` under `textPos` is all of `[1,n]` (finite injectivity). -/
theorem textPos_image (h1n : 1 ≤ n)
    (hSA1 : ∀ p, 1 ≤ p → p ≤ n → 1 ≤ SA p ∧ SA p ≤ n)
    (hSAinj : Set.InjOn SA (Set.Icc 1 n)) :
    (Finset.Icc 1 n).image (GagieRIndex.Locate.textPos n SA) = Finset.Icc 1 n := by
  have hsub : (Finset.Icc 1 n).image (GagieRIndex.Locate.textPos n SA) ⊆ Finset.Icc 1 n := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    exact textPos_mem_Icc n SA h1n hSA1 hp
  have hcard : ((Finset.Icc 1 n).image (GagieRIndex.Locate.textPos n SA)).card =
      (Finset.Icc 1 n).card :=
    Finset.card_image_of_injOn (textPos_injOn n SA h1n hSA1 hSAinj)
  apply Finset.eq_of_subset_of_card_le hsub
  exact le_of_eq hcard.symm

/-- Main proof: the last BWT occurrence of `T i` sits at a run end, whose
`textPos` is a sampled position carrying `T i`. -/
theorem sampled_character_main (σ : ℕ) (hT : GagieRIndex.Locate.IsText n σ T)
    (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ∃ i' ∈ GagieRIndex.Locate.sampled n T SA, T i' = T i := by
  obtain ⟨h1n, -, -, -⟩ := hT
  obtain ⟨hSA1, hSAinj, -⟩ := hSA
  have himg := textPos_image n SA h1n hSA1 hSAinj
  have hiimg : i ∈ (Finset.Icc 1 n).image (GagieRIndex.Locate.textPos n SA) := by
    rw [himg]; exact Finset.mem_Icc.mpr ⟨hi, hin⟩
  obtain ⟨p₀, hp₀, hp₀i⟩ := Finset.mem_image.mp hiimg
  -- `S`: BWT positions carrying the character `T i`; nonempty via `p₀`.
  set S := (Finset.Icc 1 n).filter
    (fun p => GagieRIndex.Locate.bwt n T SA p = T i) with hSdef
  have hne : S.Nonempty := by
    refine ⟨p₀, ?_⟩
    rw [hSdef]
    refine Finset.mem_filter.mpr ⟨hp₀, ?_⟩
    rw [bwt_eq n T SA p₀, hp₀i]
  -- `q`: the last such position.
  set q := S.max' hne with hqdef
  have hqS : q ∈ S := S.max'_mem hne
  have hqmem : q ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hqS).1
  have hqbwt : GagieRIndex.Locate.bwt n T SA q = T i := (Finset.mem_filter.mp hqS).2
  obtain ⟨h1q, hqn⟩ := Finset.mem_Icc.mp hqmem
  -- A last occurrence is a run end: otherwise `q + 1` would be a later occurrence.
  have hrunend : GagieRIndex.Locate.IsRunEnd n T SA q := by
    refine ⟨h1q, hqn, ?_⟩
    by_cases hqn' : q = n
    · exact Or.inl hqn'
    · refine Or.inr ?_
      intro hcon
      have hq1mem : q + 1 ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hq1S : q + 1 ∈ S := by
        rw [hSdef]
        refine Finset.mem_filter.mpr ⟨hq1mem, ?_⟩
        rw [hcon, hqbwt]
      have hle : q + 1 ≤ q := Finset.le_max' S (q + 1) hq1S
      omega
  have hqfilter : q ∈ (Finset.Icc 1 n).filter
      (fun p => GagieRIndex.Locate.IsRunStart n T SA p ∨
        GagieRIndex.Locate.IsRunEnd n T SA p) :=
    Finset.mem_filter.mpr ⟨hqmem, Or.inr hrunend⟩
  have hqsampled : GagieRIndex.Locate.textPos n SA q ∈
      GagieRIndex.Locate.sampled n T SA := by
    unfold GagieRIndex.Locate.sampled
    exact Finset.mem_image.mpr ⟨q, hqfilter, rfl⟩
  exact ⟨GagieRIndex.Locate.textPos n SA q, hqsampled,
    by rw [← bwt_eq n T SA q]; exact hqbwt⟩

end SampledCharAux

theorem solution (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ∃ i' ∈ GagieRIndex.Locate.sampled n T SA, T i' = T i :=
  SampledCharAux.sampled_character_main n T SA σ hT hSA i hi hin

theorem GagieRIndex.Kmers.sampled_character (n σ : ℕ) (T SA : ℕ → ℕ)
    (hT : GagieRIndex.Locate.IsText n σ T) (hSA : GagieRIndex.Locate.IsSuffixArray n T SA)
    (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
    ∃ i' ∈ GagieRIndex.Locate.sampled n T SA, T i' = T i :=
  solution n σ T SA hT hSA i hi hin
