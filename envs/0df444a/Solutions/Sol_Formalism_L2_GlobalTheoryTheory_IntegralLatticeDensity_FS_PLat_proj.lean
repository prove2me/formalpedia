-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.PLat.proj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:16:15.415455+00:00
-- url     : https://prove2.me/submissions/ce3cf00c-a6d2-42bf-afd3-a81fabd3d410

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
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
theorem _root_.solution (P : PLat c h O L p) {ι : Type} [Fintype ι] [DecidableEq ι] {v : ι → V} {n : ι → ℕ}
    (G : Good h L p v n) (x : V) (hx : x ∈ L) :
    ∃ x' ∈ L, (∀ j, h x' (v j) = 0) ∧ ∃ N : ℕ, Nat.Coprime N p ∧ N ≠ 0 ∧
      ((N : K) • x - x' ∈ Submodule.span K (Set.range v)) ∧
      ∀ y, (∀ i, h y (v i) = 0) → h x' y = (N : K) * h x y := by
  obtain ⟨gL, gn, gp, go⟩ := G
  have H := P.herm
  set S : V := ∑ i, (((∏ j ∈ Finset.univ.erase i, n j : ℕ) : K) * h x (v i)) • v i with hS
  have hSL : S ∈ L := AddSubgroup.sum_mem _ fun i _ =>
    P.smul _ (O.mul_mem (natCast_mem O _) (P.int _ hx _ (gL i))) _ (gL i)
  refine ⟨((∏ j, n j : ℕ) : K) • x - S, L.sub_mem (P.smul _ (natCast_mem O _) _ hx) hSL, ?_, ∏ j, n j, ?_, ?_, ?_, ?_⟩
  · intro j
    have e1 : h (((∏ j, n j : ℕ) : K) • x - S) (v j) = H.hl (v j) (((∏ j, n j : ℕ) : K) • x - S) := rfl
    rw [e1, map_sub, map_smul, hS, map_sum, Finset.sum_eq_single j]
    · rw [map_smul]
      show ((∏ j, n j : ℕ) : K) • h x (v j)
        - (((∏ i ∈ Finset.univ.erase j, n i : ℕ) : K) * h x (v j)) • h (v j) (v j) = 0
      rw [gn j, ← Finset.mul_prod_erase Finset.univ n (Finset.mem_univ j)]
      simp only [smul_eq_mul]
      push_cast; ring
    · intro i _ hij
      rw [map_smul]
      show _ • h (v i) (v j) = 0
      rw [go i j hij, smul_zero]
    · intro hj; exact absurd (Finset.mem_univ j) hj
  · exact Nat.Coprime.prod_left fun i _ => ((Nat.Prime.coprime_iff_not_dvd P.prime).2 (gp i)).symm
  · exact Finset.prod_ne_zero_iff.2 fun i _ hi => gp i (hi ▸ dvd_zero p)
  · rw [sub_sub_cancel]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro y hy
    have e1 : h (((∏ j, n j : ℕ) : K) • x - S) y = H.hl y (((∏ j, n j : ℕ) : K) • x - S) := rfl
    rw [e1, map_sub, map_smul, hS, map_sum, Finset.sum_eq_zero, sub_zero]
    · rfl
    · intro i _
      rw [map_smul]
      show _ • h (v i) y = 0
      rw [H.ortho_symm (hy i), smul_zero]
end PLat
end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
