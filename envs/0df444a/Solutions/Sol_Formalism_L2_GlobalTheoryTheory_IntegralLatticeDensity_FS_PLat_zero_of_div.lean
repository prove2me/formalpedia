-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.zero_of_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:36:45.400135+00:00
-- url     : https://prove2.me/submissions/b3bcad82-6bde-4cff-b200-ebbcbd507b66

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_PLat_div

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
theorem _root_.solution : ∀ (m : ℕ) (y : V), y ∈ L → (∀ i, h y (v i) = 0) → h y y = (m : K) → y = 0 := by
  have H := P.herm
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast P.prime.ne_zero
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro y hy hy' hm
    by_contra hne
    obtain ⟨h1, h2⟩ := P.div G hdiv y hy hy'
    obtain ⟨m', hm'⟩ := P.nat _ h1
    have e : h ((p : K)⁻¹ • y) ((p : K)⁻¹ • y) = (p : K)⁻¹ * ((p : K)⁻¹ * (m : K)) := by
      rw [H.smul_left, H.symm ((p : K)⁻¹ • y) y, H.smul_left, hm, map_mul, map_inv₀, map_natCast, map_natCast]
    have e2 : (m' : K) * (p : K) * (p : K) = (m : K) := by
      rw [← hm', e]; field_simp
    have e3 : m' * p * p = m := by exact_mod_cast e2
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero] at hm
      exact (H.pos y hne).1 hm
    have hp2 := P.prime.two_le
    have hlt : m' < m := by
      have hm'0 : 0 < m' := by
        rcases Nat.eq_zero_or_pos m' with h0 | h0
        · rw [h0] at e3; simp at e3; exact absurd e3.symm hm0
        · exact h0
      calc m' < m' * 2 * 2 := by omega
        _ ≤ m' * p * p := Nat.mul_le_mul (Nat.mul_le_mul_left _ hp2) hp2
        _ = m := e3
    have := ih m' hlt _ h1 h2 hm'
    rcases smul_eq_zero.1 this with h0 | h0
    · exact inv_ne_zero hp0 h0
    · exact hne h0
end PLat
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
