-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.fam
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:53:02.453173+00:00
-- url     : https://prove2.me/submissions/52ae1b22-824a-4637-a52e-4b43bbb386c4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_PLat_proj
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_PLat_zero_of_div
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_ortho_symm


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
namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
namespace PLat
theorem _root_.solution (P : PLat c h O L p) (m : ℕ) (hm : m ≤ finrank K V) :
    ∃ (v : Fin m → V) (n : Fin m → ℕ), Good h L p v n := by
  have H := P.herm
  induction m with
  | zero => exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ m ih =>
    obtain ⟨v, n, G⟩ := ih (Nat.le_of_succ_le hm)
    have hne : Submodule.span K (Set.range v) ≠ ⊤ := by
      intro e
      have h1 := finrank_range_le_card (R := K) v
      rw [Set.finrank, e, finrank_top, Fintype.card_fin] at h1
      omega
    obtain ⟨x, hx⟩ : ∃ x, x ∉ Submodule.span K (Set.range v) := by
      by_contra hcon
      push Not at hcon
      exact hne (Submodule.eq_top_iff'.2 hcon)
    obtain ⟨k, hk, hkx⟩ := P.full x
    obtain ⟨x', hx'L, hx'o, N, -, hN, hspan, -⟩ := P.proj G _ hkx
    have hx'0 : x' ≠ 0 := by
      intro e
      rw [e, sub_zero, smul_smul] at hspan
      have hc : (N : K) * (k : K) ≠ 0 := mul_ne_zero (by exact_mod_cast hN) (by exact_mod_cast hk.ne')
      have := Submodule.smul_mem _ ((N : K) * (k : K))⁻¹ hspan
      rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
      exact hx this
    by_cases hex : ∃ y ∈ L, (∀ i, h y (v i) = 0) ∧ ∃ ny : ℕ, h y y = (ny : K) ∧ ¬ p ∣ ny
    · obtain ⟨y, hyL, hyo, ny, hny, hpy⟩ := hex
      obtain ⟨gL, gn, gp, go⟩ := G
      refine ⟨Fin.cons y v, Fin.cons ny n, ?_, ?_, ?_, ?_⟩
      · intro i; refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hyL
        · simpa using gL i
      · intro i; refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hny
        · simpa using gn i
      · intro i; refine Fin.cases ?_ (fun i => ?_) i
        · simpa using hpy
        · simpa using gp i
      · intro i j
        refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
        · intro e; exact absurd rfl e
        · intro _; simpa using hyo j
        · intro _; simpa using H.ortho_symm (hyo i)
        · intro e
          have : i ≠ j := fun e' => e (congrArg Fin.succ e')
          simpa using go i j this
    · exfalso
      have hdiv : ∀ y ∈ L, (∀ i, h y (v i) = 0) → ∃ k : ℕ, h y y = (p : K) * k := by
        intro y hy hy'
        obtain ⟨ny, hny⟩ := P.nat y hy
        by_cases hd : p ∣ ny
        · obtain ⟨k, rfl⟩ := hd
          exact ⟨k, by rw [hny]; push_cast; ring⟩
        · exact absurd ⟨y, hy, hy', ny, hny, hd⟩ hex
      obtain ⟨nx, hnx⟩ := P.nat x' hx'L
      exact hx'0 (P.zero_of_div G hdiv nx x' hx'L hx'o hnx)
end PLat
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
