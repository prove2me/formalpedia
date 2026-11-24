-- Prove2me | solution 1 for Formalism.UG.P.gLoc_int_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:50:09.02259+00:00
-- url     : https://prove2.me/submissions/f4bb5449-7cf9-485d-80ca-fc33fa00fb51

import Definitions.Def_Formalism_SatakeDualWeyl_StatementG
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Transport
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_LocalAlgebraInertPrime
import Theorems.Thm_Formalism_UG_P_gLoc_bc_coe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {A L : Type} [CommRing A] [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (e : A ≃+* L) (T : Subring A) (O : Subring L) (hT : ∀ x, x ∈ T ↔ e x ∈ O)
    (g : GL n A) :
    g ∈ (bc (n := n) T.subtype).range ↔ bc (e : A →+* L) g ∈ (bc (n := n) O.subtype).range := by
  have key : ∀ {B : Type} [CommRing B] (S : Subring B) (u : GL n B),
      u ∈ (bc (n := n) S.subtype).range ↔ (∀ i j, (u : Matrix n n B) i j ∈ S) ∧
        (∀ i j, ((u⁻¹ : GL n B) : Matrix n n B) i j ∈ S) := by
    intro B _ S u
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · simp [bc]
      · rw [← map_inv]
        simp [bc]
    · rintro ⟨h1, h2⟩
      have hinj : Function.Injective (RingHom.mapMatrix S.subtype : Matrix n n S → Matrix n n B) :=
        Matrix.map_injective Subtype.val_injective
      let Am : Matrix n n S := Matrix.of fun i j => ⟨(u : Matrix n n B) i j, h1 i j⟩
      let Bm : Matrix n n S := Matrix.of fun i j => ⟨((u⁻¹ : GL n B) : Matrix n n B) i j, h2 i j⟩
      have hA : RingHom.mapMatrix S.subtype Am = (u : Matrix n n B) := by ext i j; rfl
      have hB : RingHom.mapMatrix S.subtype Bm = ((u⁻¹ : GL n B) : Matrix n n B) := by ext i j; rfl
      refine ⟨⟨Am, Bm, hinj ?_, hinj ?_⟩, ?_⟩
      · rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      · rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]
      · ext i j
        rfl
  rw [key T g, key O (bc (e : A →+* L) g), ← map_inv]
  simp only [gLoc_bc_coe, Matrix.map_apply, RingEquiv.coe_toRingHom, ← hT]
end Formalism.UG.P
