-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.L3.hermitianFormColumns.card_vec_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:31.99804+00:00
-- url     : https://prove2.me/submissions/c372c4be-7812-4c2f-be9e-dcd43c5e7bac

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LocalDensityEighth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsNotMemOfSol
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_hermitianFormColumns_form_col
import Theorems.Thm_Formalism_H_dualEquiv_apply
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_star_def
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_reductionMapsOfForms_card_rep_succ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.H.dualEquiv_apply


section
open NumberField Module Matrix
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
section col
variable {A : Type*} [CommRing A] [StarRing A] {m : Type} [Fintype m] [DecidableEq m]
end col
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
private theorem conjTranspose_mul_mul_col_eq_const_iff_fm {A : Type*} [CommRing A] [StarRing A] (Hq : Matrix m m A) (t : A)
    (X : Matrix m Unit A) :
    Xᴴ * Hq * X = Matrix.of (fun _ _ => t) ↔ fm Hq (fun i => X i ()) (fun i => X i ()) = t := by
  have hX : X = colU (fun i => X i ()) := by
    ext i u
    rfl
  constructor
  · intro h
    have h1 := congrFun (congrFun h ()) ()
    rw [hX, form_col] at h1
    exact h1
  · intro h
    ext a b
    rw [hX, form_col]
    exact h
section star
variable {A : Type*} [CommRing A] [StarRing A]
end star
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
end
end

set_option autoImplicit false
open NumberField Module Matrix
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
open HermitianSublattices idealPowerSpanBounds traceDeterminantCongruences reductionMapsOfForms
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable [Fact (IsFixF K F)]
variable {m : Type} [Fintype m] [DecidableEq m]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
namespace Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
theorem _root_.solution (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (H : Matrix m m (𝓞 K)) (hH : Hᴴ = H) (n : 𝓞 F) {k j : ℕ}
    (hj : k + 1 ≤ 2 * j) (p' : (m → 𝓞 K ⧸ extP K 𝔭 ^ k) → Prop)
    (hinv : ∀ x y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ j) →
      (p' (fun i => mkk K 𝔭 k ((x + y) i)) ↔ p' (fun i => mkk K 𝔭 k (x i))))
    (RC : ∀ x : m → 𝓞 K, p' (fun i => mkk K 𝔭 k (x i)) → fm H x x - ι n ∈ extP K 𝔭 ^ k →
      ∀ s ∈ extP K 𝔭 ^ k, star s - s ∈ extP K 𝔭 ^ (k + 1) →
      ∃ y : m → 𝓞 K, (∀ a, y a ∈ extP K 𝔭 ^ j) ∧ fm H x y + fm H y x - s ∈ extP K 𝔭 ^ (k + 1)) :
    Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // p' (fun i => piQ K 𝔭 k (x i)) ∧
        fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} * Ideal.absNorm 𝔭 =
      Ideal.absNorm 𝔭 ^ (2 * Fintype.card m) *
        Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // p' x ∧
          fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} := by
  have hF : IsFixF K F := Fact.out
  obtain ⟨T, hTdef⟩ : ∃ T : Matrix Unit Unit (𝓞 K), T = Matrix.of (fun _ _ => ι n) := ⟨_, rfl⟩
  have hT : Tᴴ = T := by
    rw [hTdef]
    refine Matrix.ext fun a b => ?_
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [idealPowerSpanBounds.star_def]
    exact conjO_map hF n
  have RC'' : ∀ X : Matrix m Unit (𝓞 K), (fun X => p' (fun i => X i ())) (X.map (mkk K 𝔭 k)) →
      (∀ a b, (Xᴴ * H * X - T) a b ∈ extP K 𝔭 ^ k) → ∀ S : Matrix Unit Unit (𝓞 K),
      (∀ a b, S a b ∈ extP K 𝔭 ^ k) → (∀ a b, (Sᴴ - S) a b ∈ extP K 𝔭 ^ (k + 1)) →
      ∃ Y : Matrix m Unit (𝓞 K), (∀ a b, Y a b ∈ extP K 𝔭 ^ j) ∧
        ∀ a b, (Xᴴ * H * Y + Yᴴ * H * X - S) a b ∈ extP K 𝔭 ^ (k + 1) := by
    intro X hp hX S hS hS'
    have hXc : X = colU (fun i => X i ()) := by
      ext i u
      rfl
    have hx : fm H (fun i => X i ()) (fun i => X i ()) - ι n ∈ extP K 𝔭 ^ k := by
      have h1 := hX () ()
      rw [Matrix.sub_apply, hXc, form_col, hTdef, Matrix.of_apply] at h1
      exact h1
    obtain ⟨y, hy, hy'⟩ := RC (fun i => X i ()) hp hx (S () ()) (hS () ()) (hS' () ())
    refine ⟨colU y, fun a b => hy a, fun a b => ?_⟩
    rw [Matrix.sub_apply, Matrix.add_apply, hXc, form_col, form_col]
    exact hy'
  have h := card_rep_succ (m := m) (r := Unit) hK h𝔭 H hH T hT hj (fun X => p' (fun i => X i ()))
    (fun X Y hY => hinv (fun i => X i ()) (fun i => Y i ()) (fun a => hY a ())) RC''
  have c1 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ (k + 1) // p' (fun i => piQ K 𝔭 k (x i)) ∧
        fm (H.map (mkk K 𝔭 (k + 1))) x x = mkk K 𝔭 (k + 1) (ι n)} =
      Nat.card {X : Matrix m Unit (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) //
        (fun X => p' (fun i => X i ())) (X.map (piQ K 𝔭 k)) ∧
        Xᴴ * H.map (mkk K 𝔭 (k + 1)) * X = T.map (mkk K 𝔭 (k + 1))} := by
    rw [hTdef]
    exact Nat.card_congr (Equiv.subtypeEquiv colU (fun x => and_congr Iff.rfl
      (conjTranspose_mul_mul_col_eq_const_iff_fm (H.map (mkk K 𝔭 (k + 1))) (mkk K 𝔭 (k + 1) (ι n)) (colU x)).symm))
  have c2 : Nat.card {x : m → 𝓞 K ⧸ extP K 𝔭 ^ k // p' x ∧
        fm (H.map (mkk K 𝔭 k)) x x = mkk K 𝔭 k (ι n)} =
      Nat.card {X : Matrix m Unit (𝓞 K ⧸ extP K 𝔭 ^ k) // (fun X => p' (fun i => X i ())) X ∧
        Xᴴ * H.map (mkk K 𝔭 k) * X = T.map (mkk K 𝔭 k)} := by
    rw [hTdef]
    exact Nat.card_congr (Equiv.subtypeEquiv colU (fun x => and_congr Iff.rfl
      (conjTranspose_mul_mul_col_eq_const_iff_fm (H.map (mkk K 𝔭 k)) (mkk K 𝔭 k (ι n)) (colU x)).symm))
  rw [c1, c2]
  simp only [Fintype.card_unit, mul_one, pow_one] at h
  exact h
end Formalism.HermitianLattices.Ext.L3.hermitianFormColumns
