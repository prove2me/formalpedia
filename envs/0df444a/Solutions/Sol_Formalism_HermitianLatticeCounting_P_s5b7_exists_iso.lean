-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s5b7_exists_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:09:50.55208+00:00
-- url     : https://prove2.me/submissions/633bc28a-d66a-4080-bf75-21d0de8af78d

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (d : ℕ) (u : EuclideanSpace ℂ (Fin (d + 1))) (hu : ‖u‖ = 1) :
    ∃ Φ : EuclideanSpace ℂ (Fin (d + 1)) ≃ₗᵢ[ℂ] WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)),
      Φ u = WithLp.toLp 2 (1, 0) := by
  have key : ∀ (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
      (_ : finrank ℂ W = d + 1) (x : W) (_ : ‖x‖ = 1),
      ∃ b : OrthonormalBasis (Fin (d + 1)) ℂ W, b 0 = x := by
    intro W _ _ _ hW x hx
    have ho : Orthonormal ℂ (({0} : Set (Fin (d + 1))).domRestrict (fun _ => x)) := by
      rw [orthonormal_iff_ite]
      intro i j
      have : i = j := Subsingleton.elim i j
      subst this
      simp [inner_self_eq_norm_sq_to_K, hx]
    obtain ⟨b, hb⟩ := ho.exists_orthonormalBasis_extension_of_card_eq (by simpa using hW)
    exact ⟨b, hb 0 rfl⟩
  obtain ⟨b, hb⟩ := key _ (by simp) u hu
  obtain ⟨b', hb'⟩ := key (WithLp 2 (ℂ × EuclideanSpace ℂ (Fin d)))
    (by
      rw [(WithLp.linearEquiv 2 ℂ (ℂ × EuclideanSpace ℂ (Fin d))).finrank_eq]
      simp [add_comm])
    (WithLp.toLp 2 (1, 0)) (by simp)
  refine ⟨b.repr.trans b'.repr.symm, ?_⟩
  rw [← hb, ← hb']
  simp
end Formalism.HermitianLatticeCounting.P
