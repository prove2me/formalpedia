-- Prove2me | solution 1 for BlockSSM.free_orbit_vector
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-12T12:52:14.677097+00:00
-- url     : https://prove2.me/submissions/f7ffe8f8-03f5-426f-b7a6-7513a6018f5b

import Mathlib

set_option autoImplicit false

/-- A faithful representation of a finite group over `ℂ` has a vector with trivial stabilizer,
because a finite union of proper subspaces cannot cover the space. -/
theorem solution {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ H V) (hρ : Function.Injective ρ) :
    ∃ v : V, Function.Injective fun h : H => ρ h v := by
  classical
  haveI : Fintype H := Fintype.ofFinite H
  let fix : H → Submodule ℂ V := fun h => LinearMap.ker (ρ h - 1)
  have hproper : ∀ h : H, h ≠ 1 → fix h ≠ ⊤ := by
    intro h hne htop
    have hzero : ρ h - 1 = 0 := by
      ext v
      have hv : v ∈ fix h := by rw [htop]; exact Submodule.mem_top
      simpa [fix, LinearMap.mem_ker] using hv
    have hρh : ρ h = 1 := sub_eq_zero.mp hzero
    have h1 : ρ h = ρ 1 := by simpa using hρh
    exact hne (hρ h1)
  let s : Finset (Submodule ℂ V) := (Finset.univ.erase (1 : H)).image fix
  have htop : (⊤ : Submodule ℂ V) ∉ s := by
    intro hmem
    obtain ⟨h, hh, hEq⟩ := Finset.mem_image.mp hmem
    exact hproper h (Finset.mem_erase.mp hh).1 hEq
  have hunion : ⋃ p ∈ s, (p : Set V) ≠ Set.univ := by
    intro hcov
    exact htop (Subspace.top_mem_of_biUnion_eq_univ hcov)
  obtain ⟨v, hv⟩ := (Set.ne_univ_iff_exists_notMem _).mp hunion
  refine ⟨v, ?_⟩
  intro h h' heq
  change ρ h v = ρ h' v at heq
  have hfix : v ∈ fix (h'⁻¹ * h) := by
    show (ρ (h'⁻¹ * h) - 1) v = 0
    rw [LinearMap.sub_apply, sub_eq_zero]
    calc ρ (h'⁻¹ * h) v = ρ h'⁻¹ (ρ h v) := by
          rw [map_mul]
          rfl
      _ = ρ h'⁻¹ (ρ h' v) := by rw [heq]
      _ = ρ (h'⁻¹ * h') v := by
          rw [map_mul]
          rfl
      _ = ρ 1 v := by rw [inv_mul_cancel]
      _ = v := by rw [map_one]; rfl
  have key : h'⁻¹ * h = 1 := by
    by_contra hne
    have hmem : fix (h'⁻¹ * h) ∈ s := by
      refine Finset.mem_image.mpr ⟨h'⁻¹ * h, ?_, rfl⟩
      rw [Finset.mem_erase]
      exact ⟨hne, Finset.mem_univ _⟩
    exact hv (Set.mem_iUnion₂.mpr ⟨fix (h'⁻¹ * h), hmem, hfix⟩)
  have hh : h' = h := inv_mul_eq_one.mp key
  exact hh.symm
