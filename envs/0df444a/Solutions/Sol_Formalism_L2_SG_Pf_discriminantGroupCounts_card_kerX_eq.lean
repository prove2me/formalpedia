-- Prove2me | solution 1 for Formalism.L2.SG.Pf.discriminantGroupCounts.card_kerX_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:26:42.576801+00:00
-- url     : https://prove2.me/submissions/48953df1-6b53-461b-8e22-2f77de4601af

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_OneAddFormEqIff
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_DiagMulMulDiagApply
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_mem_tSet_iff
import Theorems.Thm_Formalism_L2_SG_Pf_discriminantGroupCounts_card_ker_eq_card_hermD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.HermitianLattices.Ext.L3
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.discriminantGroupCounts
variable {A : Type*} [CommRing A] [StarRing A]
variable {m : Type*} [Fintype m] [DecidableEq m]
variable {d : m → A}
namespace Formalism.L2.SG.Pf.discriminantGroupCounts
theorem _root_.solution [Finite A] (hd : ∀ i, star (d i) = d i) {θ e : A}
    (he : (θ - star θ) * e = 1)
    (hsq : ∀ i j, Nat.card {a : A // d i * a * d j = 0} =
      Nat.card {a : A // a * d i = 0} * Nat.card {a : A // a * d j = 0}) (N : ℕ)
    (hN : ∀ T ∈ tSet d, Nat.card {Y : Matrix m m A // phiH (diagonal d) Y = T} = N) :
    Nat.card {X : Matrix m m A // Xᴴ * diagonal d * X = diagonal d ∧ ∃ Y, X = 1 + Y * diagonal d} =
      N := by
  classical
  haveI : Fintype A := Fintype.ofFinite A
  unfold phiH at hN
  have hHs : (diagonal d)ᴴ = diagonal d := by
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact hd i
  have key : ∀ Y : Matrix m m A, (1 + Y * diagonal d)ᴴ * diagonal d * (1 + Y * diagonal d) =
      diagonal d + diagonal d * (Y + Yᴴ + Yᴴ * diagonal d * Y) * diagonal d := by
    intro Y
    simp only [conjTranspose_add, conjTranspose_one, conjTranspose_mul, hHs]
    noncomm_ring
  have herm : ∀ Y : Matrix m m A,
      (Y + Yᴴ + Yᴴ * diagonal d * Y)ᴴ = Y + Yᴴ + Yᴴ * diagonal d * Y := by
    intro Y
    simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose, hHs]
    noncomm_ring
  have cond : ∀ Y : Matrix m m A,
      (1 + Y * diagonal d)ᴴ * diagonal d * (1 + Y * diagonal d) = diagonal d ↔
        (Y + Yᴴ + Yᴴ * diagonal d * Y) ∈ tSet d := by
    intro Y
    rw [key]
    simp only [tSet, Set.mem_setOf_eq]
    constructor
    · intro h
      refine ⟨herm Y, ?_⟩
      have h' := congrArg (fun Z => Z - diagonal d) h
      simpa using h'
    · rintro ⟨-, h⟩
      rw [h, add_zero]
  let YS := {Y : Matrix m m A // Y + Yᴴ + Yᴴ * diagonal d * Y ∈ tSet d}
  let XS := {X : Matrix m m A // Xᴴ * diagonal d * X = diagonal d ∧ ∃ Y, X = 1 + Y * diagonal d}
  let KS := (AddMonoidHom.mulRight (diagonal d)).ker
  let Φ : YS → XS := fun Y => ⟨1 + Y.1 * diagonal d, (cond Y.1).2 Y.2, Y.1, rfl⟩
  let sec : XS → YS := fun X => ⟨Classical.choose X.2.2, (cond _).1 (by
    rw [← Classical.choose_spec X.2.2]
    exact X.2.1)⟩
  have hsec : ∀ X : XS, X.1 = 1 + (sec X).1 * diagonal d := fun X => Classical.choose_spec X.2.2
  have hΦ : ∀ (X : XS) (k : KS) (h : ((sec X).1 + k.1) + ((sec X).1 + k.1)ᴴ +
      ((sec X).1 + k.1)ᴴ * diagonal d * ((sec X).1 + k.1) ∈ tSet d), Φ ⟨(sec X).1 + k.1, h⟩ = X := by
    intro X k h
    apply Subtype.ext
    have hk : k.1 * diagonal d = 0 := k.2
    show 1 + ((sec X).1 + k.1) * diagonal d = X.1
    rw [add_mul, hk, add_zero, hsec X]
  let e : YS ≃ XS × KS :=
    { toFun := fun Y => (Φ Y, ⟨Y.1 - (sec (Φ Y)).1, by
        show (Y.1 - (sec (Φ Y)).1) * diagonal d = 0
        have h1 := hsec (Φ Y)
        have h2 : (Φ Y).1 = 1 + Y.1 * diagonal d := rfl
        rw [h2] at h1
        rw [sub_mul]
        have h3 := add_left_cancel h1
        rw [h3, sub_self]⟩)
      invFun := fun p => ⟨(sec p.1).1 + p.2.1, (cond _).1 (by
        have hk : p.2.1 * diagonal d = 0 := p.2.2
        rw [add_mul, hk, add_zero, ← hsec p.1]
        exact p.1.2.1)⟩
      left_inv := fun Y => by
        apply Subtype.ext
        show (sec (Φ Y)).1 + (Y.1 - (sec (Φ Y)).1) = Y.1
        abel
      right_inv := fun p => by
        obtain ⟨X, k⟩ := p
        have hX := hΦ X k
        refine Prod.ext (hX _) ?_
        apply Subtype.ext
        show (sec X).1 + k.1 - (sec (Φ ⟨(sec X).1 + k.1, _⟩)).1 = k.1
        rw [hX]
        abel }
  have hY : Nat.card YS = Nat.card XS * Nat.card KS := by
    rw [Nat.card_congr e, Nat.card_prod]
  let g : YS → tSet d := fun Y => ⟨_, Y.2⟩
  have hfib : ∀ T : tSet d, Nat.card {Y : YS // g Y = T} = N := by
    intro T
    rw [← hN T.1 T.2]
    exact Nat.card_congr
      { toFun := fun Y => ⟨Y.1.1, congrArg Subtype.val Y.2⟩
        invFun := fun Y => ⟨⟨Y.1, by rw [Y.2]; exact T.2⟩, Subtype.ext Y.2⟩
        left_inv := fun Y => rfl
        right_inv := fun Y => rfl }
  have hY2 : Nat.card YS = Nat.card (tSet d) * N := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv g), Nat.card_sigma]
    simp only [hfib, Finset.sum_const, smul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card]
  have hT : Nat.card (tSet d) = Nat.card KS := by
    rw [card_ker_eq_card_hermD hd he hsq]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun T => mem_tSet_iff d T))
  have hpos : 0 < Nat.card KS := Nat.card_pos
  rw [hY2, hT, mul_comm (Nat.card KS) N] at hY
  exact (Nat.eq_of_mul_eq_mul_right hpos hY).symm
end Formalism.L2.SG.Pf.discriminantGroupCounts
