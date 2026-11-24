-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.normalFormDegenerateImpossible
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:46.311917+00:00
-- url     : https://prove2.me/submissions/8421960c-7ac7-47d7-a2f5-4bf2bdddb743

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_B_swap0
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_perp_X
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_X_iso
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gram_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_eq
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_swap
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_zeroL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
namespace Formalism.HermitianLatticeCounting.P
section Base
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
private theorem HermSpace_B_add_right (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B x (y + z) = H.B x y + H.B x z :=
  map_add _ _ _
private theorem HermSpace_B_smul_right_eq_star_mul (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (c : K) (x y : V) : H.B x (c • y) = star c * H.B x y := by
  rw [LinearMap.map_smulₛₗ, smul_eq_mul, starRingEnd_apply]
end Base
section Base2
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Base2
section CaseA
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ}
end CaseA
section Gram
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Gram
section V0
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end V0
section Sig
variable {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
end Sig
section Perp
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
end Perp
section DetBlocks
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
end DetBlocks
section Lift
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
end Lift
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S6
open scoped BigOperators
open Matrix
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NFCaseC := by
  intro K V _ _ _ _ H r F F' hA hA' hm hDr hg
  have hD : Formalism.HermitianLatticeCounting.S6.Dl F F' (r + 1) le_rfl = 0 := by
    unfold Formalism.HermitianLatticeCounting.S6.Gval at hg
    rw [hDr, star_zero, mul_zero, mul_zero, sub_zero] at hg
    rcases mul_eq_zero.1 hg with h | h
    · exact h
    · exact star_eq_zero.1 h
  have hD' : (Matrix.of fun a b : Fin (r + 1) =>
      H.B (F'.e (Fin.castLE le_rfl a)) (F.e (Fin.castLE le_rfl b))).det = 0 := by
    rw [← Dl_eq, Dl_swap, hD, star_zero]
  obtain ⟨c, hc, hcb⟩ := gram_zero H
    (fun a : Fin (r + 1) => F'.e (Fin.castLE le_rfl a)) (fun b : Fin (r + 1) => F.e (Fin.castLE le_rfl b)) hD'
  obtain ⟨y', hy'def⟩ : ∃ y' : V, y' = ∑ a : Fin (r + 1), c a • F'.e (Fin.castLE le_rfl a) := ⟨_, rfl⟩
  have hy' : ∀ a : Fin (r + 1), H.B (F.e a) y' = 0 := fun a => by
    rw [hy'def]
    exact B_swap0 H (hcb a)
  have hsplit : y' = (∑ a : Fin r, c a.castSucc • F'.e a.castSucc) + c (Fin.last r) • F'.z := by
    rw [hy'def, Fin.sum_univ_castSucc]
    rfl
  have hx₀' : ∑ a : Fin r, c a.castSucc • F'.e a.castSucc ∈ F'.X :=
    Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ((e_mem_X F') a)
  have hβ : c (Fin.last r) ≠ 0 := by
    intro h0
    rw [h0, zero_smul, add_zero] at hsplit
    have hyI' : y' ∈ F'.X := by rw [hsplit]; exact hx₀'
    have hyI : y' ∈ F.X := hA y' hy' ((X_iso F') hyI' hyI')
    have hy0 : y' = 0 := by
      have hmem : y' ∈ Formalism.HermitianLatticeCounting.S6.II F F' := Submodule.mem_inf.2 ⟨hyI, hyI'⟩
      rw [hm] at hmem
      exact (Submodule.mem_bot K).1 hmem
    have hind := Fintype.linearIndependent_iff.1 F'.indep (fun a => c a.castSucc)
      (by have h5 := hsplit.symm.trans hy0; simpa using h5)
    apply hc
    funext a
    induction a using Fin.lastCases with
    | last => exact h0
    | cast b => exact hind b
  obtain ⟨x, hx, hx0, hxu⟩ := Dl_zeroL F F' (le_refl r) hDr
  have hγ : H.B x F'.z ≠ 0 := by
    intro hγ
    have hxF' : x ∈ F'.X := by
      apply hA' x
      · intro a
        apply B_swap0 H
        induction a using Fin.lastCases with
        | last => exact hγ
        | cast b => exact hxu _ ((e_mem_X F') b)
      · exact (X_iso F) hx hx
    have hmem : x ∈ Formalism.HermitianLatticeCounting.S6.II F F' := Submodule.mem_inf.2 ⟨hx, hxF'⟩
    rw [hm] at hmem
    exact hx0 ((Submodule.mem_bot K).1 hmem)
  have h1 : H.B x y' = 0 := (perp_X F) (fun b => hy' b.castSucc) x hx
  rw [hsplit, HermSpace_B_add_right, HermSpace_B_smul_right_eq_star_mul, hxu _ hx₀', zero_add] at h1
  exact (mul_ne_zero (star_ne_zero.2 hβ) hγ) h1
end Formalism.HermitianLatticeCounting.P
