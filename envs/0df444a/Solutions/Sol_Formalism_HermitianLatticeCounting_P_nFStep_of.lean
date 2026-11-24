-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.nFStep_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:42.95983+00:00
-- url     : https://prove2.me/submissions/c57982b8-ff94-4930-8420-447fc6873513

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_e_mem_Xa
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
private theorem HermSpace_B_sub_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (x y z : V) : H.B (x - y) z = H.B x z - H.B y z := by
  rw [map_sub, LinearMap.sub_apply]
private theorem HermSpace_B_smul_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (c : K) (x y : V) : H.B (c • x) y = c * H.B x y := by
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul]
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
theorem _root_.solution (hY1 : Formalism.HermitianLatticeCounting.S6.Y1) (hPP : Formalism.HermitianLatticeCounting.S6.PerpPerp) : Formalism.HermitianLatticeCounting.S6.NFStep := by
  intro K V _ _ _ _ _ H r F F' x a a' al al' hμ hrel hx hxa hxa'
  apply hPP K V H (F.Xa (a.val + 1) ⊔ F'.Xa (a'.val + 1))
  intro v hv
  have hvF : ∀ b : Fin r, b ≤ a → H.B (F.e b.castSucc) v = 0 := fun b hb =>
    hv _ (Submodule.mem_sup_left ((e_mem_Xa F) b (by have := Fin.le_iff_val_le_val.1 hb; omega)))
  have hvF' : ∀ b : Fin r, b ≤ a' → H.B (F'.e b.castSucc) v = 0 := fun b hb =>
    hv _ (Submodule.mem_sup_right ((e_mem_Xa F') b (by have := Fin.le_iff_val_le_val.1 hb; omega)))
  obtain ⟨d, hd_def⟩ : ∃ d : K, d = al * H.B (F.e a.succ) v - al' * H.B (F'.e a'.succ) v := ⟨_, rfl⟩
  have key : ∀ t : K, t * d + star (t * d) = 0 := by
    intro t
    have hvt : ∀ b : Fin r, b ≤ a → H.B (F.e b.castSucc) (star t • v) = 0 := fun b hb => by
      rw [HermSpace_B_smul_right_eq_star_mul, hvF b hb, mul_zero]
    have hvt' : ∀ b : Fin r, b ≤ a' → H.B (F'.e b.castSucc) (star t • v) = 0 := fun b hb => by
      rw [HermSpace_B_smul_right_eq_star_mul, hvF' b hb, mul_zero]
    obtain ⟨-, -, hL, hc⟩ := hY1 K V H r F x (star t • v) a al hxa hvt
    obtain ⟨-, -, hL', hc'⟩ := hY1 K V H r F' x (star t • v) a' al' hxa' hvt'
    have h1 := hrel _ hL hL' _ _ hc hc'
    simp only [HermSpace_B_smul_right_eq_star_mul, star_star, star_mul', star_add] at h1
    rw [hd_def]
    simp only [star_mul', star_sub]
    linear_combination h1
  obtain ⟨μ, hμ⟩ := hμ
  have hd : d = 0 := by
    have h1 := key (μ * star d)
    have h2 : (μ + star μ) * (star d * d) = 0 := by
      simp only [star_mul', star_star] at h1
      linear_combination h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hμ
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact star_eq_zero.1 h4
      · exact h4
  rw [HermSpace_B_sub_left, HermSpace_B_smul_left, HermSpace_B_smul_left, ← hd_def, hd]
end Formalism.HermitianLatticeCounting.P
