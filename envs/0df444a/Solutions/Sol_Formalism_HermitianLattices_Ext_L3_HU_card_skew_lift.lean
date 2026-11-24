-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.HU.card_skew_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:53.024675+00:00
-- url     : https://prove2.me/submissions/c2e948dc-57e5-4e84-bcbc-c2ecf906d713

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensitySixth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsAddConjTransposeEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsSkewValue
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_preimage
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_card_uniform
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_entSub
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_HermitianSublattices_mem_hermSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply



set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.HU
open HermitianSublattices idealPowerSpanBounds
variable {A A' : Type*} [CommRing A] [StarRing A] [CommRing A'] [StarRing A']
variable {m : Type*} [Fintype m] [DecidableEq m]
namespace Formalism.HermitianLattices.Ext.L3.HU
theorem _root_.solution [Finite A] (π : A →+* A') (hπ : Function.Surjective π)
    (hπs : ∀ a, π (star a) = star (π a)) (H : Matrix m m A) (hH : Hᴴ = H)
    (hS : ∀ S ∈ hermSub m (RingHom.ker π), ∃ Y : Matrix m m A, H * Y + Yᴴ * H = S) :
    Nat.card {Y : Matrix m m A // H * Y + Yᴴ * H = 0} * Nat.card (hermSub m (RingHom.ker π)) =
      Nat.card (entSub m m (RingHom.ker π)) *
        Nat.card {Y' : Matrix m m A' // H.map π * Y' + Y'ᴴ * H.map π = 0} := by
  have hgH : ∀ Y : Matrix m m A, (H * Y + Yᴴ * H)ᴴ = H * Y + Yᴴ * H := by
    intro Y
    rw [conjTranspose_add, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH,
      add_comm]
  have h1 := card_uniform (⊤ : AddSubgroup (Matrix m m A)) (hermSub m (RingHom.ker π))
    (fun Y : Matrix m m A => H * Y + Yᴴ * H) (fun _ => True) (fun _ _ _ => Iff.rfl) (by
      intro X _ _
      refine ⟨AddMonoidHom.mk' (fun Y => H * Y.1 + Y.1ᴴ * H) (fun a b => by
        simp only [AddSubgroup.coe_add, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]; abel),
        ?_, ?_⟩
      · intro Y
        show H * (X + Y.1) + (X + Y.1)ᴴ * H = H * X + Xᴴ * H + (H * Y.1 + Y.1ᴴ * H)
        simp only [conjTranspose_add, Matrix.mul_add, Matrix.add_mul]
        abel
      · intro S hS'
        obtain ⟨Y, h⟩ := hS S hS'
        exact ⟨⟨Y, trivial⟩, h⟩)
  have e0 : {Y : Matrix m m A // H * Y + Yᴴ * H = 0} ≃
      {Y : Matrix m m A // True ∧ H * Y + Yᴴ * H = 0} :=
    Equiv.subtypeEquivRight fun X => by rw [true_and]
  rw [Nat.card_congr e0, ← h1]
  have hsurj : Function.Surjective (π.toAddMonoidHom.mapMatrix (m := m) (n := m)) := by
    intro X'
    choose f hf using hπ
    exact ⟨X'.map f, by ext i j; simp [hf]⟩
  have h2 := card_preimage (π.toAddMonoidHom.mapMatrix (m := m) (n := m)) hsurj
    (fun Y' => H.map π * Y' + Y'ᴴ * H.map π = 0)
  have hker : (π.toAddMonoidHom.mapMatrix (m := m) (n := m)).ker = entSub m m (RingHom.ker π) := by
    ext X
    rw [AddMonoidHom.mem_ker, mem_entSub]
    constructor
    · intro h i j
      have := congrFun (congrFun h i) j
      exact this
    · intro h
      ext i j
      exact h i j
  rw [← hker, ← h2]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun X => ?_)
  show _ ↔ H.map π * X.map π + (X.map π)ᴴ * H.map π = 0
  have hm : H.map π * X.map π + (X.map π)ᴴ * H.map π = (H * X + Xᴴ * H).map π := by
    rw [Matrix.map_add π (map_add π), Matrix.map_mul, Matrix.map_mul,
      conjTranspose_map π (fun a => hπs a)]
  rw [hm, mem_hermSub, true_and]
  constructor
  · rintro ⟨-, h3⟩
    ext i j
    exact h3 i j
  · intro h3
    exact ⟨hgH X, fun i j => congrFun (congrFun h3 i) j⟩
end Formalism.HermitianLattices.Ext.L3.HU
