-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.existsScalarOfGramDefectZero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:36.132325+00:00
-- url     : https://prove2.me/submissions/97635660-ac52-4b87-a11a-8c62ba7c4094

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_normalFormMinorNeZero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_reverseCS_gen
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_mem_perpS
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
private theorem HermSpace_B_zero_left (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (y : V) : H.B 0 y = 0 := by
  rw [map_zero, LinearMap.zero_apply]
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
theorem _root_.solution : Formalism.HermitianLatticeCounting.S6.NFCaseBConcl := by
  intro K V _ _ _ _ σ H r F F' hσ hT hT' hsig hD hg
  obtain ⟨x, hx, x', hx', h1, h2, h3, h4, -, h6⟩ := normalFormMinorNeZero K V H r F F' hD
  obtain ⟨z₀, hz₀, hz₀n, hpos⟩ := id hsig
  have hDD : Formalism.HermitianLatticeCounting.S6.Dl F F' r (Nat.le_succ r) * star (Formalism.HermitianLatticeCounting.S6.Dl F F' r (Nat.le_succ r)) ≠ 0 :=
    mul_ne_zero hD (star_ne_zero.2 hD)
  have hβ : H.B (F.z - x) (F'.z - x') * star (H.B (F.z - x) (F'.z - x')) =
      F.T * F'.T := by
    rw [hg] at h6
    have h7 := (mul_eq_zero.1 h6.symm).resolve_left hDD
    linear_combination h7
  have hmemA : ∀ y : V, (∀ w ∈ F.X ⊔ F'.X, H.B w y = 0) →
      y ∈ perpS H (F.X ⊔ F'.X) :=
    fun y hy => (mem_perpS H _ y).2 hy
  obtain ⟨-, heq⟩ := reverseCS_gen σ H.B hσ H.herm
    (perpS H (F.X ⊔ F'.X)) ⊥
    (fun n hn u _ => by rw [(Submodule.mem_bot K).1 hn, HermSpace_B_zero_left]) z₀ (hmemA _ hz₀)
    (fun w hw h5 h7 => hpos w ((mem_perpS H _ w).1 hw) h5
      (fun h0 => h7 (by rw [h0]; exact Submodule.zero_mem _)))
    (F.z - x) (hmemA _ h1) (by rw [h3, map_neg, Complex.neg_re]; linarith)
    (F'.z - x') (hmemA _ h2)
  obtain ⟨c, hc⟩ := heq (by rw [h3, h4, hβ]; ring)
  refine ⟨c, ?_⟩
  have hc0 : F'.z - x' - c • (F.z - x) = 0 := (Submodule.mem_bot K).1 hc
  have e : F'.z - c • F.z = (F'.z - x' - c • (F.z - x)) + (x' - c • x) := by
    rw [smul_sub]
    abel
  rw [e, hc0, zero_add]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right hx') (Submodule.mem_sup_left (Submodule.smul_mem _ _ hx))
end Formalism.HermitianLatticeCounting.P
