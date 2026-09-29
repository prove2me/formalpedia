-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FockOfFock.lpFiniteModes_sum_repr
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:24:16.57213+00:00
-- url     : https://prove2.me/submissions/933d59a8-c2b6-4283-a9af-1a0e03925b3e

-- Adapted from Leonardo Pedro, timepiece commit61595bc, Apache-2.0.
-- https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterNavierStokesFockSpace.lean
import Definitions.Def_ChapterNavierStokesFockSpace
import Mathlib
set_option autoImplicit false
open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FockOfFock
open BookProof.NavierStokesFlow.FullEsa BookProof.NavierStokesFlow.LpNat

section
variable {ι : Type*}
private theorem lpBasis_coe [DecidableEq ι] (i j : ι) :
    (((lpBasis i : lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j
      = if j = i then 1 else 0 := by
  by_cases h : j = i
  · subst h; simp [lpBasis, lp.single_apply]
  · simp [lpBasis, lp.single_apply, h]

end

theorem solution {ι : Type*} [DecidableEq ι] (f : lpFiniteModes ι) :
    f = ∑ i ∈ f.2.toFinset, (((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i) • lpBasis i := by
  ext j
  have hcoe : (((∑ i ∈ f.2.toFinset, (((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i) • lpBasis i :
      lpFiniteModes ι) : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j
      = ∑ i ∈ f.2.toFinset,
          (((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) i) * (if j = i then 1 else 0) := by
    classical
    induction f.2.toFinset using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha]
        simp only [Submodule.coe_add, lp.coeFn_add, Pi.add_apply, Submodule.coe_smul,
          lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lpBasis_coe] at *
        rw [ih]
  rw [hcoe]
  by_cases hj : j ∈ f.2.toFinset
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · intro hcon; exact absurd hj hcon
  · have hzero : ((f : lp (fun _ : ι => ℂ) 2) : ι → ℂ) j = 0 := by
      by_contra hne
      exact hj (f.2.mem_toFinset.mpr hne)
    rw [hzero]
    refine (Finset.sum_eq_zero fun i hi => ?_).symm
    by_cases hij : j = i
    · exact absurd (hij ▸ hi) hj
    · simp [hij]


#print axioms solution
