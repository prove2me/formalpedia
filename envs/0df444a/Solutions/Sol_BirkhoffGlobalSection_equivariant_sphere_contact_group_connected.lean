-- Prove2me | solution 1 for BirkhoffGlobalSection.equivariant_sphere_contact_group_connected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @caleb
-- created : 2026-10-01T01:09:46.251684+00:00
-- url     : https://prove2.me/submissions/0548c704-05d4-4af5-ad0e-2179a37f3a25
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_BirkhoffGlobalSection_SphereContact
import Theorems.Thm_BirkhoffGlobalSection_equivariant_contactomorphism_smooth_isotopy
import Theorems.Thm_BirkhoffGlobalSection_smooth_isotopy_contact_upgrade

open BirkhoffGlobalSection

theorem solution (F : EquivariantSphereContactomorphism) :
    Nonempty (EquivariantSphereContactIsotopy F) := by
  obtain ⟨Gto, hsmooth, hmaps, hanti, hstart, hfinish⟩ :=
    equivariant_contactomorphism_smooth_isotopy F
  exact smooth_isotopy_contact_upgrade F Gto
    hsmooth hmaps hanti hstart hfinish
