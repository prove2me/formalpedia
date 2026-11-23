-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gf_lower_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:07:43.046817+00:00
-- url     : https://prove2.me/submissions/6f829b3b-8694-4322-89bb-e9ba12ed80e4

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
    (l : Matrix (Fin d) (Fin d) R) (hl : IsLowerUnitriangular l) (M : Matrix (Fin d) β R) (κ : β' → β) :
    (l * M).submatrix ρ κ = l.submatrix ρ ρ * M.submatrix ρ κ := by
  unfold IsLowerUnitriangular at hl
  ext a c
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have e1 := Finset.sum_image (s := Finset.univ) (g := ρ)
    (f := fun x => l (ρ a) x * M x (κ c)) (fun b _ b' _ h => hinj h)
  rw [← e1]
  refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
  have hlt : ρ a < x := by
    by_contra hle
    push_neg at hle
    obtain ⟨b, hb⟩ := hdown a x hle
    exact hx (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩)
  rw [hl.2 _ _ hlt, zero_mul]
end Formalism.HermitianLatticeCounting.P
