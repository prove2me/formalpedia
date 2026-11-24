-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:24:45.735803+00:00
-- url     : https://prove2.me/submissions/50b3a604-7c6d-4fdd-8d80-1bc4bcca1232

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_PLat_proj
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_PLat_pair_div

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
variable (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} {n : ι → ℕ} (G : Good h L p v n)
  (hdiv : ∀ y ∈ L, (∀ i, h y (v i) = 0) → ∃ k : ℕ, h y y = (p : K) * k)
include P G hdiv
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace PLat
theorem _root_.solution (y : V) (hy : y ∈ L) (hy' : ∀ i, h y (v i) = 0) :
    (p : K)⁻¹ • y ∈ L ∧ ∀ i, h ((p : K)⁻¹ • y) (v i) = 0 := by
  have H := P.herm
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast P.prime.ne_zero
  refine ⟨P.unim _ fun x hx => ?_, fun i => by rw [H.smul_left, hy' i, mul_zero]⟩
  obtain ⟨x', hx'L, hx'o, N, hcop, -, -, hform⟩ := P.proj G x hx
  obtain ⟨t', ht', e⟩ := P.pair_div G hdiv x' y hx'L hx'o hy hy'
  rw [hform y hy'] at e
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have habK : (a : K) * (N : K) + (b : K) * (p : K) = 1 := by exact_mod_cast hab
  have e2 : h x y = (p : K) * ((a : K) * t' + (b : K) * h x y) := by
    linear_combination (a : K) * e - (h x y) * habK
  have hmem : (a : K) * t' + (b : K) * h x y ∈ O :=
    O.add_mem (O.mul_mem (intCast_mem O a) ht') (O.mul_mem (intCast_mem O b) (P.int _ hx _ hy))
  rw [H.smul_left, H.symm x y, e2, map_mul, map_natCast, ← mul_assoc, inv_mul_cancel₀ hp0, one_mul]
  exact P.cO _ hmem
end PLat
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
