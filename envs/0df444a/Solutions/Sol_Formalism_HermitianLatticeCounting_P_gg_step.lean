-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.gg_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:02:43.152776+00:00
-- url     : https://prove2.me/submissions/8d4af55b-0b18-4e6b-aee0-d061d5e06f64

import Definitions.Def_Formalism_FlagUnipotentLattices_UnipotentStabiliserCharacterisation
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegrableOnIoiTruncatedPowerMoment
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gg_antidiag_det

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
theorem _root_.solution {d : ℕ} {R : Type*} [CommRing R] (Z : Matrix (Fin d) (Fin d) R) (q s : ℕ) (t : R)
    (hqs : q + s ≤ d)
    (h0 : ∀ i j : Fin d, q ≤ (i : ℕ) → (i : ℕ) < q + s → (j : ℕ) < q → Z i j = 0)
    (hD : ∀ i j : Fin d, q ≤ (i : ℕ) → (i : ℕ) < q + s → q ≤ (j : ℕ) → (j : ℕ) < q + s →
      Z i j = if (i : ℕ) + (j : ℕ) + 1 = 2 * q + s then t else 0) :
    leadingPrincipalMinor Z (q + s) = leadingPrincipalMinor Z q * ((-1) ^ (s.choose 2) * t ^ s) := by
  unfold leadingPrincipalMinor
  rw [Matrix.twoBlockTriangular_det _ (fun x : {i : Fin d // (i : ℕ) < q + s} => (x.1 : ℕ) < q)]
  · congr 1
    · let e : {i : Fin d // (i : ℕ) < q} ≃
          {x : {i : Fin d // (i : ℕ) < q + s} // (x.1 : ℕ) < q} :=
        { toFun := fun i => ⟨⟨i.1, by have := i.2; omega⟩, i.2⟩
          invFun := fun x => ⟨x.1.1, x.2⟩
          left_inv := fun i => rfl
          right_inv := fun x => rfl }
      rw [← Matrix.det_submatrix_equiv_self e]
      rfl
    · let e : Fin s ≃ {x : {i : Fin d // (i : ℕ) < q + s} // ¬ (x.1 : ℕ) < q} :=
        { toFun := fun i => ⟨⟨⟨q + i, by have := i.2; omega⟩, by have := i.2; simp⟩, by simp⟩
          invFun := fun x => ⟨(x.1.1 : ℕ) - q, by have := x.1.2; have := x.2; omega⟩
          left_inv := fun i => by ext; simp
          right_inv := fun x => by
            have := x.2
            ext
            simp
            omega }
      rw [← Matrix.det_submatrix_equiv_self e, ← gg_antidiag_det]
      congr 1
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.toSquareBlockProp_def, Matrix.of_apply, e,
        Equiv.coe_fn_mk]
      rw [hD _ _ (by simp) (by simp) (by simp) (by simp)]
      congr 1
      exact propext ⟨fun h => by simp at h; omega, fun h => by simp; omega⟩
  · intro i hi j hj
    exact h0 i.1 j.1 (not_lt.mp hi) i.2 hj
end Formalism.HermitianLatticeCounting.P
