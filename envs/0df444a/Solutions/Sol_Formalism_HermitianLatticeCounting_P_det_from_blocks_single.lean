-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.det_from_blocks_single
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:16:48.163232+00:00
-- url     : https://prove2.me/submissions/686e70fa-5027-4aea-89b4-54c41a57dd72

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductPlacesInequalitySq
import Definitions.Def_Formalism_HyperbolicPlaceProducts_SecondLevelArithmeticNorm
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LocalIntegralStructure
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_from_blocks_single_regular

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Matrix Polynomial
variable {R : Type} [CommRing R]
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (r : ℕ) (W Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (l : Fin (r + 1))
    (t t' : R) :
    (fromBlocks W ((-t) • Matrix.single l l (1 : R)) ((-t') • Matrix.single l l (1 : R)) Z).det =
      W.det * Z.det - t * t' * W.adjugate l l * Z.adjugate l l := by
  let φ : R[X] →+* R := Polynomial.evalRingHom (0 : R)
  have hW : φ.mapMatrix (charmatrix (-W)) = W := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [φ, charmatrix_apply]
    · simp [φ, charmatrix_apply, hab]
  have hZ : φ.mapMatrix (C.mapMatrix Z) = Z := by
    ext a b; simp [φ]
  have hs : ∀ c : R, φ.mapMatrix ((-(C c)) • Matrix.single l l (1 : R[X])) =
      (-c) • Matrix.single l l (1 : R) := by
    intro c; ext a b
    by_cases h : l = a ∧ l = b
    · obtain ⟨rfl, rfl⟩ := h; simp [φ]
    · simp [φ, Matrix.single_apply, h]
  have key := det_from_blocks_single_regular r (charmatrix (-W)) (C.mapMatrix Z) l (C t) (C t')
    (charpoly_monic (-W)).isRegular
  have key2 := congrArg φ key
  rw [RingHom.map_det, RingHom.mapMatrix_apply, fromBlocks_map] at key2
  simp only [← RingHom.mapMatrix_apply] at key2
  rw [hW, hZ, hs, hs] at key2
  rw [key2]
  have ha : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) R[X],
      φ (M.adjugate l l) = (φ.mapMatrix M).adjugate l l := by
    intro M; rw [← RingHom.map_adjugate]; rfl
  simp only [map_sub, map_mul, RingHom.map_det, ha, hW, hZ]
  simp [φ]
end Formalism.HermitianLatticeCounting.P
