-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.BN.cp_eq_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:23:13.754142+00:00
-- url     : https://prove2.me/submissions/67a95da2-92c4-4de9-822f-4890f8caf248

import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbittAlg
import Definitions.Def_Lemmata_ScalarExtension_Scal
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZBrauerNesbitt
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_cp_mem_closure
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_exponents_eq
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_Z_BN_lin_indep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z Formalism.IrreducibleCountingLemmas.Z.BN
namespace Formalism.IrreducibleCountingLemmas.Z.BN
theorem _root_.solution {K A : Type} [Field K] [IsAlgClosed K] [Ring A] [Algebra K A]
    (Γ : Set A) (hΓ : Submodule.span K Γ = ⊤) (V W : Type) [AddCommGroup V]
    [Module K V] [Module A V] [IsScalarTower K A V] [FiniteDimensional K V] [AddCommGroup W]
    [Module K W] [Module A W] [IsScalarTower K A W] [FiniteDimensional K W]
    (h : ∀ g ∈ Γ, cp K V g = cp K W g) : (cp K V : A → K[X]) = cp K W := by
  classical
  have hV := cp_mem_closure (k := K) (A := A) V
  have hW := cp_mem_closure (k := K) (A := A) W
  rw [Submonoid.mem_closure_iff_exists_finset_subset] at hV hW
  obtain ⟨a, t1, ht1, ha, hVa⟩ := hV
  obtain ⟨b, t2, ht2, hb, hWb⟩ := hW
  have ht : (↑(t1 ∪ t2) : Set (A → K[X])) ⊆ simpleCps K A := by
    intro F hF
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hF) with h | h
    · exact ht1 h
    · exact ht2 h
  have hVa' : ∏ F ∈ t1 ∪ t2, F ^ a F = cp K V := by
    rw [← hVa]; symm
    refine Finset.prod_subset Finset.subset_union_left ?_
    intro F _ hF
    have : a F = 0 := by
      by_contra h0
      exact hF (ha h0)
    simp [this]
  have hWb' : ∏ F ∈ t1 ∪ t2, F ^ b F = cp K W := by
    rw [← hWb]; symm
    refine Finset.prod_subset Finset.subset_union_right ?_
    intro F _ hF
    have : b F = 0 := by
      by_contra h0
      exact hF (hb h0)
    simp [this]
  have hlin : ∀ F ∈ t1 ∪ t2, ∃ T : A →ₗ[K] K, ∀ x, (F x).nextCoeff = T x := by
    intro F hF
    obtain ⟨S, _, _, _, _, _, _, rfl⟩ := ht (Finset.mem_coe.2 hF)
    exact ⟨-(LinearMap.trace K S ∘ₗ (Algebra.lsmul K K S).toLinearMap), fun x => by
      rw [nextCoeff_cp]; rfl⟩
  have key : ∀ F ∈ t1 ∪ t2, a F = b F := by
    apply exponents_eq (Γ := Γ) (t1 ∪ t2) (fun F g => F g.1)
    · intro F hF g
      obtain ⟨S, _, _, _, _, _, _, rfl⟩ := ht (Finset.mem_coe.2 hF)
      exact LinearMap.charpoly_monic _
    · intro c hc
      apply lin_indep (t1 ∪ t2) ht c
      intro x
      have hx : x ∈ Submodule.span K Γ := hΓ ▸ Submodule.mem_top
      induction hx using Submodule.span_induction with
      | mem x hx => exact hc ⟨x, hx⟩
      | zero =>
        refine Finset.sum_eq_zero fun F hF => ?_
        obtain ⟨T, hT⟩ := hlin F hF
        rw [hT, map_zero, mul_zero]
      | add x y _ _ hx hy =>
        have hxy : ∑ F ∈ t1 ∪ t2, c F * (F (x + y)).nextCoeff =
            ∑ F ∈ t1 ∪ t2, c F * (F x).nextCoeff + ∑ F ∈ t1 ∪ t2, c F * (F y).nextCoeff := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun F hF => ?_
          obtain ⟨T, hT⟩ := hlin F hF
          rw [hT, hT, hT, map_add, mul_add]
        rw [hxy, hx, hy, add_zero]
      | smul r x _ hx =>
        have hrx : ∑ F ∈ t1 ∪ t2, c F * (F (r • x)).nextCoeff =
            r * ∑ F ∈ t1 ∪ t2, c F * (F x).nextCoeff := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun F hF => ?_
          obtain ⟨T, hT⟩ := hlin F hF
          rw [hT, hT, map_smul, smul_eq_mul]; ring
        rw [hrx, hx, mul_zero]
    · intro g
      have := h g.1 g.2
      rw [← hVa', ← hWb'] at this
      simpa [Finset.prod_apply, Pi.pow_apply] using this
  rw [← hVa', ← hWb']
  exact Finset.prod_congr rfl (fun F hF => by rw [key F hF])
end Formalism.IrreducibleCountingLemmas.Z.BN
