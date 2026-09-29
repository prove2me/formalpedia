-- Prove2me | solution 1 for BraidsLinksMCG.braid_perm_hom
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-14T11:58:48.637067+00:00
-- url     : https://prove2.me/submissions/d79b9362-601d-4620-a83b-3dea803ec879

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

open BraidsLinksMCG in
theorem solution (n : ℕ) :
    ∃ pi : ArtinBraidGroup n →* Equiv.Perm (Fin n),
      ∀ i : Fin (n - 1), pi (sigma i) = Equiv.swap (strandIdx i) (strandIdxSucc i) := by
  have hrel : ∀ r ∈ braidRels n,
      (FreeGroup.lift fun i : Fin (n - 1) =>
        Equiv.swap (strandIdx i) (strandIdxSucc i)) r = 1 := by
    rintro r (⟨i, j, hij, rfl⟩ | ⟨i, j, hij, rfl⟩)
    · have hi := i.isLt
      have hj := j.isLt
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of]
      have h1 : Equiv.swap (Equiv.swap (strandIdx i) (strandIdxSucc i) (strandIdx j))
            (Equiv.swap (strandIdx i) (strandIdxSucc i) (strandIdxSucc j))
          = Equiv.swap (strandIdx i) (strandIdxSucc i) *
              Equiv.swap (strandIdx j) (strandIdxSucc j) *
              (Equiv.swap (strandIdx i) (strandIdxSucc i))⁻¹ :=
        Equiv.swap_apply_apply _ _ _
      rw [Equiv.swap_apply_of_ne_of_ne (by simp [strandIdx, Fin.ext_iff]; omega)
            (by simp [strandIdx, strandIdxSucc, Fin.ext_iff]; omega),
          Equiv.swap_apply_of_ne_of_ne (by simp [strandIdx, strandIdxSucc, Fin.ext_iff]; omega)
            (by simp [strandIdxSucc, Fin.ext_iff]; omega)] at h1
      rw [← h1, mul_inv_cancel]
    · have hi := i.isLt
      have hj := j.isLt
      have hbc : strandIdx j = strandIdxSucc i := by
        simp [strandIdx, strandIdxSucc, hij]
      simp only [map_mul, map_inv, FreeGroup.lift_apply_of, hbc]
      set a := strandIdx i with ha
      set b := strandIdxSucc i with hb
      set d := strandIdxSucc j with hd
      have hda : d ≠ a := by simp [ha, hd, strandIdx, strandIdxSucc, Fin.ext_iff]; omega
      have hdb : d ≠ b := by simp [hb, hd, strandIdxSucc, Fin.ext_iff]; omega
      have hab : a ≠ b := by simp [ha, hb, strandIdx, strandIdxSucc, Fin.ext_iff]
      have e1 : Equiv.swap a b * Equiv.swap b d * Equiv.swap a b = Equiv.swap a d := by
        have h := Equiv.swap_apply_apply (Equiv.swap a b) b d
        rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne hda hdb, Equiv.swap_inv] at h
        exact h.symm
      have e2 : Equiv.swap b d * Equiv.swap a b * Equiv.swap b d = Equiv.swap a d := by
        have h := Equiv.swap_apply_apply (Equiv.swap b d) a b
        rw [Equiv.swap_apply_of_ne_of_ne hab (fun hc => hda hc.symm),
          Equiv.swap_apply_left, Equiv.swap_inv] at h
        exact h.symm
      rw [e1, e2, mul_inv_cancel]
  refine ⟨PresentedGroup.toGroup hrel, ?_⟩
  intro i
  exact PresentedGroup.toGroup.of hrel
