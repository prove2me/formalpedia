-- Prove2me | solution 1 for Formalism.UG.P.satake_mem_glint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:08.489927+00:00
-- url     : https://prove2.me/submissions/397b7708-5d85-45ff-816b-53da2144f508

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {L : Type} [Field L] (O : Subring L) {n : ℕ}
variable {O}
variable (O)
namespace Formalism.UG.P
theorem _root_.solution (g : GL (Fin n) L)
    (h1 : ∀ a b, (g : Matrix (Fin n) (Fin n) L) a b ∈ O)
    (h2 : ∀ a b, ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b ∈ O) :
    g ∈ GLint (Fin n) O := by
  let φ : Matrix (Fin n) (Fin n) O →+* Matrix (Fin n) (Fin n) L := O.subtype.mapMatrix
  have hφ : Function.Injective φ := fun x y h =>
    Matrix.ext fun i j => Subtype.ext (congrFun (congrFun h i) j)
  let M : Matrix (Fin n) (Fin n) O := fun a b => ⟨(g : Matrix (Fin n) (Fin n) L) a b, h1 a b⟩
  let M' : Matrix (Fin n) (Fin n) O :=
    fun a b => ⟨((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b, h2 a b⟩
  have hM : φ M = (g : Matrix (Fin n) (Fin n) L) := rfl
  have hM' : φ M' = ((g⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := rfl
  have e1 : M * M' = 1 :=
    hφ (by rw [map_mul, map_one, hM, hM', ← Units.val_mul, mul_inv_cancel, Units.val_one])
  have e2 : M' * M = 1 :=
    hφ (by rw [map_mul, map_one, hM, hM', ← Units.val_mul, inv_mul_cancel, Units.val_one])
  unfold Formalism.UG.GLint
  exact MonoidHom.mem_range.2 ⟨⟨M, M', e1, e2⟩, Units.ext rfl⟩
end Formalism.UG.P
