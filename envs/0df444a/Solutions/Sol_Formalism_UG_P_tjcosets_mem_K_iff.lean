-- Prove2me | solution 1 for Formalism.UG.P.tjcosets_mem_K_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:51:20.735092+00:00
-- url     : https://prove2.me/submissions/d24b211b-cfb8-4b42-bc17-22974f9732ed

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsFF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_TjcosetsLoc

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
variable {L : Type} [Field L]
variable (O : Subring L) [IsLocalRing O]
variable {O}
namespace Formalism.UG.P
theorem _root_.solution (n : ℕ) (U : GL (Fin n) L) :
    U ∈ GLint (Fin n) O ↔ (∀ a b, (U : Matrix (Fin n) (Fin n) L) a b ∈ O) ∧
      (∀ a b, ((U⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b ∈ O) := by
  unfold GLint
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨g, rfl⟩
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · exact ((g : Matrix (Fin n) (Fin n) O) a b).2
    · rw [← map_inv]
      exact (((g⁻¹ : GL (Fin n) O) : Matrix (Fin n) (Fin n) O) a b).2
  · rintro ⟨h1, h2⟩
    let M : Matrix (Fin n) (Fin n) O := fun a b => ⟨(U : Matrix (Fin n) (Fin n) L) a b, h1 a b⟩
    let N : Matrix (Fin n) (Fin n) O :=
      fun a b => ⟨((U⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b, h2 a b⟩
    have hM : M.map O.subtype = (U : Matrix (Fin n) (Fin n) L) := by ext a b; rfl
    have hN : N.map O.subtype = ((U⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) := by ext a b; rfl
    have inj : Function.Injective (fun P : Matrix (Fin n) (Fin n) O => P.map O.subtype) :=
      fun P Q h => by ext a b; exact congrFun (congrFun h a) b
    have hMN : M * N = 1 := inj (by
      show (M * N).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
      rw [Matrix.map_mul, hM, hN, U.mul_inv]
      exact (map_one (RingHom.mapMatrix O.subtype)).symm)
    have hNM : N * M = 1 := inj (by
      show (N * M).map O.subtype = (1 : Matrix (Fin n) (Fin n) O).map O.subtype
      rw [Matrix.map_mul, hM, hN, U.inv_mul]
      exact (map_one (RingHom.mapMatrix O.subtype)).symm)
    exact ⟨⟨M, N, hMN, hNM⟩, Units.ext hM⟩
end Formalism.UG.P
