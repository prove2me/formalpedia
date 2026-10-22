-- Prove2me | solution 1 for BirkhoffGlobalSection.smooth_isotopy_contact_upgrade
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-02T21:58:20.168974+00:00
-- url     : https://prove2.me/submissions/dae8d64b-ac90-412c-818d-e5c3a58dd041
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Definitions.Def_BirkhoffGlobalSection_SphereDiffeoIsotopy
import Theorems.Thm_BirkhoffGlobalSection_equivariant_diffeomorphism_smooth_isotopy
import Theorems.Thm_BirkhoffGlobalSection_smooth_diffeo_isotopy_contact_upgrade

open BirkhoffGlobalSection

open scoped ContDiff

theorem solution
    (F : EquivariantSphereContactomorphism)
    (Gto : ℝ → Phase → Phase)
    (hGsmooth : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere,
      ContDiffAt ℝ ∞ (fun p : ℝ × Phase => Gto p.1 p.2) (t, y))
    (hGmaps : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Set.MapsTo (Gto t) unitThreeSphere unitThreeSphere)
    (hGanti : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ unitThreeSphere,
      Gto t (-y) = -Gto t y)
    (hGstart : ∀ y ∈ unitThreeSphere, Gto 0 y = y)
    (hGfinish : ∀ y ∈ unitThreeSphere, Gto 1 y = F.toFun y) :
    Nonempty (EquivariantSphereContactIsotopy F) := by
  obtain ⟨H⟩ := equivariant_diffeomorphism_smooth_isotopy F
  exact smooth_diffeo_isotopy_contact_upgrade F H
