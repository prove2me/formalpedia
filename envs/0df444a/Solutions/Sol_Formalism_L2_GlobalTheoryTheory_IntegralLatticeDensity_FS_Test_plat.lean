-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Test.plat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:36.358704+00:00
-- url     : https://prove2.me/submissions/6df86288-7464-4102-89cc-114d06f0ebe0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Test_herm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {c : K →+* K} {h : V → V → K} {O : Subring K} {L : AddSubgroup V} {p : ℕ}
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Test
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Test
theorem _root_.solution : PLat (RingHom.id ℚ) (fun x y : ℚ => x * y) (Int.castRingHom ℚ).range (Int.castAddHom ℚ).range 3 where
  herm := herm
  prime := Nat.prime_three
  cO t ht := ht
  smul := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨a * b, by simp⟩
  int := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨a * b, by simp⟩
  unim x h := by
    obtain ⟨a, ha⟩ := h 1 ⟨1, by simp⟩
    exact ⟨a, by simpa using ha⟩
  full x := ⟨x.den, x.den_pos, ⟨x.num, by simp [Rat.den_mul_eq_num]⟩⟩
  nat := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a.natAbs * a.natAbs, ?_⟩
    push_cast
    rw [Nat.cast_natAbs]
    push_cast
    simp
  crit := by
    refine ⟨1, one_mem _, ?_⟩
    rintro _ ⟨a, rfl⟩ ⟨k, hk⟩ -
    refine ⟨((a - k : ℤ) : ℚ), ⟨a - k, rfl⟩, ?_⟩
    simp only [eq_intCast, RingHom.id_apply, Nat.cast_ofNat] at hk ⊢
    push_cast
    linarith
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Test
