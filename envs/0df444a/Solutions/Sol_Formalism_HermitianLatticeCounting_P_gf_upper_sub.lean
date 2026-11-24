-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gf_upper_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:55:51.808666+00:00
-- url     : https://prove2.me/submissions/71d6699d-f9a9-4627-ba7f-31c88dc2b004

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.ExpansionTerms Finset Matrix
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {R : Type*} [CommRing R] {d : ℕ} {α β β' : Type*} [Fintype α] (ρ : α → Fin d)
    (hinj : Function.Injective ρ) (hdown : ∀ a x, x ≤ ρ a → ∃ b, ρ b = x)
    (u : Matrix (Fin d) (Fin d) R) (hu : IsUpperUnitriangular u) (M : Matrix β (Fin d) R) (κ : β' → β) :
    (M * u).submatrix κ ρ = M.submatrix κ ρ * u.submatrix ρ ρ := by
  unfold IsUpperUnitriangular at hu
  ext c a
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have e1 := Finset.sum_image (s := Finset.univ) (g := ρ)
    (f := fun x => M (κ c) x * u x (ρ a)) (fun b _ b' _ h => hinj h)
  rw [← e1]
  refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
  have hlt : ρ a < x := by
    by_contra hle
    push_neg at hle
    obtain ⟨b, hb⟩ := hdown a x hle
    exact hx (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩)
  rw [hu.2 _ _ hlt, mul_zero]
end Formalism.HermitianLatticeCounting.P
