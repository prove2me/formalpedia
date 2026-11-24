-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.level_exists
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:31.841096+00:00
-- url     : https://prove2.me/submissions/5ce1fc71-530b-4345-8a35-5890e6b8f852

import Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ExistsHasLeadingCoeffOfMemSpanBelow
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_zero
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_Xa_succ
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
private theorem FlagD_exists_level_lt_of_mem_Xa_of_ne_zero (F : Formalism.HermitianLatticeCounting.S6.FlagD H r) : ∀ n : ℕ, n ≤ r → ∀ x : V, x ∈ F.Xa n → x ≠ 0 →
    ∃ (a : Fin r) (al : K), a.val < n ∧ F.HasLevel x a al := by
  intro n
  induction n with
  | zero =>
    intro _ x hx h0
    rw [(Xa_zero F)] at hx
    exact absurd ((Submodule.mem_bot K).1 hx) h0
  | succ n ih =>
    intro hn x hx h0
    have hnr : n < r := by omega
    have hsb : F.Xa (n + 1) = F.Xa n ⊔ K ∙ F.e (⟨n, hnr⟩ : Fin r).castSucc :=
      (Xa_succ F) ⟨n, hnr⟩
    rw [hsb] at hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
    by_cases hc : c = 0
    · subst hc
      have hy0 : y ≠ 0 := by simpa using h0
      obtain ⟨a, al, ha, hl⟩ := ih (by omega) y hy hy0
      refine ⟨a, al, by omega, ?_⟩
      simpa using hl
    · refine ⟨⟨n, hnr⟩, c, by simp, ?_⟩
      unfold Formalism.HermitianLatticeCounting.S6.FlagD.HasLevel
      exact ⟨hc, by simpa using hy⟩
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
theorem _root_.solution (F : FlagD H r) {x : V} (hx : x ∈ F.X) (h0 : x ≠ 0) :
    ∃ (a : Fin r) (al : K), F.HasLevel x a al := by
  obtain ⟨a, al, -, h⟩ := FlagD_exists_level_lt_of_mem_Xa_of_ne_zero F r le_rfl x hx h0
  exact ⟨a, al, h⟩
end Formalism.HermitianLatticeCounting.P
