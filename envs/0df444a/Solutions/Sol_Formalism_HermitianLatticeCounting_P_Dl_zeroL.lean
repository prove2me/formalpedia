-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.Dl_zeroL
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:14:26.964529+00:00
-- url     : https://prove2.me/submissions/a5e203a3-746e-4998-8061-ffb24d0e8414

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_indep_le
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_mem_Xa_iff
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_gram_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Dl_eq
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
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  {H : HermSpace K V} {r : ℕ}
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution (F F' : FlagD H r) {j : ℕ} (hj : j ≤ r) (hD : Dl F F' j (hj.trans (Nat.le_succ r)) = 0) :
    ∃ x ∈ F.Xa j, x ≠ 0 ∧ ∀ u ∈ F'.Xa j, H.B x u = 0 := by
  rw [Dl_eq] at hD
  obtain ⟨c, hc, hcb⟩ := gram_zero H
    (fun a : Fin j => F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a))
    (fun b : Fin j => F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b)) hD
  refine ⟨_, ((mem_Xa_iff F) hj).2 ⟨c, rfl⟩, ?_, ?_⟩
  · intro h0
    apply hc
    funext a
    exact Fintype.linearIndependent_iff.1 ((indep_le F) hj) c h0 a
  · intro u hu
    obtain ⟨d, rfl⟩ := ((mem_Xa_iff F') hj).1 hu
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => by rw [HermSpace_B_smul_right_eq_star_mul, hcb b, mul_zero]
end Formalism.HermitianLatticeCounting.P
