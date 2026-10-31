-- Prove2me | solution 1 for FiniteEnergyPlane.tendstoZeroCInfty_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-30T11:06:08.111351+00:00
-- url     : https://prove2.me/submissions/51c710cf-2fc9-45f9-a88a-2ed176a2876c

import Definitions.Def_FiniteEnergyPlane_Asymptotics
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod

open scoped ContDiff

namespace FiniteEnergyPlane

theorem tendstoZeroCInfty_fderiv_aux {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : TendstoZeroCInfty f) : TendstoZeroCInfty (fderiv ℝ f) := by
  obtain ⟨⟨s₀, hs⟩, hd⟩ := hf
  refine ⟨⟨s₀, hs.fderiv_of_isOpen (isOpen_Ioi.prod isOpen_univ) (by simp)⟩, fun m e he => ?_⟩
  obtain ⟨s₁, h1⟩ := hd (m + 1) e he
  exact ⟨s₁, fun s hs t => by rw [norm_iteratedFDeriv_fderiv]; exact h1 s hs t⟩

theorem tendstoZeroCInfty_prodMk_aux {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : ℝ × ℝ → F} {g : ℝ × ℝ → G}
    (hf : TendstoZeroCInfty f) (hg : TendstoZeroCInfty g) :
    TendstoZeroCInfty (fun p : ℝ × ℝ => (f p, g p)) := by
  obtain ⟨⟨a, ha⟩, hf'⟩ := hf
  obtain ⟨⟨b, hb⟩, hg'⟩ := hg
  have hU : IsOpen (Set.Ioi (max a b) ×ˢ (Set.univ : Set ℝ)) := isOpen_Ioi.prod isOpen_univ
  have hsa : Set.Ioi (max a b) ×ˢ (Set.univ : Set ℝ) ⊆ Set.Ioi a ×ˢ Set.univ :=
    Set.prod_mono (Set.Ioi_subset_Ioi (le_max_left _ _)) le_rfl
  have hsb : Set.Ioi (max a b) ×ˢ (Set.univ : Set ℝ) ⊆ Set.Ioi b ×ˢ Set.univ :=
    Set.prod_mono (Set.Ioi_subset_Ioi (le_max_right _ _)) le_rfl
  refine ⟨⟨max a b, (ha.mono hsa).prodMk (hb.mono hsb)⟩, fun m e he => ?_⟩
  obtain ⟨s1, h1⟩ := hf' m e he
  obtain ⟨s2, h2⟩ := hg' m e he
  refine ⟨max (max s1 s2) (max a b + 1), fun s hs t => ?_⟩
  have hmem : (s, t) ∈ Set.Ioi (max a b) ×ˢ (Set.univ : Set ℝ) :=
    ⟨by simp only [Set.mem_Ioi]; linarith [le_max_right (max s1 s2) (max a b + 1)], trivial⟩
  have hfa : ContDiffAt ℝ ∞ f (s, t) := (ha.mono hsa).contDiffAt (hU.mem_nhds hmem)
  have hga : ContDiffAt ℝ ∞ g (s, t) := (hb.mono hsb).contDiffAt (hU.mem_nhds hmem)
  rw [iteratedFDeriv_prodMk hfa hga (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤)),
    ContinuousMultilinearMap.opNorm_prod]
  exact max_le (h1 s (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hs) t)
    (h2 s (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hs) t)

end FiniteEnergyPlane

open FiniteEnergyPlane

theorem solution {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ × ℝ → F} (hf : TendstoZeroCInfty f) : TendstoZeroCInfty (fderiv ℝ f) :=
  tendstoZeroCInfty_fderiv_aux hf
