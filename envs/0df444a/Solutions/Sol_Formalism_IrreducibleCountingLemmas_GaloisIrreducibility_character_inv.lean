-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.character_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T09:59:39.234128+00:00
-- url     : https://prove2.me/submissions/7c0fe669-ed01-417a-b4f1-dc13c0ced4fe

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_GaloisIrreducibility
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_IRRCentralIdemSelfAdjoint
import Theorems.Thm_Formalism_IrreducibleCountingLemmas_GaloisIrreducibility_trace_of_diag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
theorem _root_.solution {G V : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) (g : G) :
    ρ.character g⁻¹ = (starRingEnd ℂ) (ρ.character g) := by
  classical
  set s : Module.End ℂ V := ρ g with hs
  set n := orderOf g with hn
  have hn0 : 0 < n := orderOf_pos g
  have hsn : s ^ n = 1 := by rw [hs, ← map_pow, hn, pow_orderOf_eq_one, map_one]
  have hsq : Squarefree (Polynomial.X ^ n - 1 : Polynomial ℂ) :=
    (Polynomial.X_pow_sub_one_separable_iff.mpr (by exact_mod_cast hn0.ne')).squarefree
  have hss : s.IsSemisimple :=
    Module.End.isSemisimple_of_squarefree_aeval_eq_zero hsq (by simp [hsn])
  let eigenDecomp := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    s.eigenspaces_iSupIndep hss.iSup_eigenspace_eq_top
  let I := (ν : ℂ) × Fin (finrank ℂ (s.eigenspace ν))
  let v : Basis I ℂ V := eigenDecomp.collectedBasis fun μ ↦ finBasis ℂ (s.eigenspace μ)
  have : Fintype I := FiniteDimensional.fintypeBasisIndex v
  let μ : I → ℂ := Sigma.fst
  have hsv (i : I) : s (v i) = μ i • v i :=
    Module.End.mem_eigenspace_iff.mp (eigenDecomp.collectedBasis_mem _ i)
  have hpow : ∀ (i : I) (k : ℕ), (s ^ k) (v i) = μ i ^ k • v i := by
    intro i k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, hsv, map_smul, ih, smul_smul, pow_succ, mul_comm]
  have hμn : ∀ i, μ i ^ n = 1 := by
    intro i
    have h1 := hpow i n
    rw [hsn, Module.End.one_apply] at h1
    have h2 : (μ i ^ n - 1) • v i = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · exact sub_eq_zero.mp h3
    · exact absurd h3 (v.ne_zero i)
  have hμ0 : ∀ i, μ i ≠ 0 := by
    intro i h0
    have := hμn i
    rw [h0, zero_pow hn0.ne'] at this
    exact zero_ne_one this
  have hinv : ∀ i, ρ g⁻¹ (v i) = (starRingEnd ℂ) (μ i) • v i := by
    intro i
    have h1 : ρ g⁻¹ (s (v i)) = v i := by
      rw [hs, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [hsv, map_smul] at h1
    have h2 : (μ i)⁻¹ = (starRingEnd ℂ) (μ i) :=
      Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one (hμn i) hn0.ne')
    rw [← h2]
    calc ρ g⁻¹ (v i) = (μ i)⁻¹ • (μ i • ρ g⁻¹ (v i)) := by
          rw [smul_smul, inv_mul_cancel₀ (hμ0 i), one_smul]
      _ = (μ i)⁻¹ • v i := by rw [h1]
  unfold Representation.character
  rw [trace_of_diag v (ρ g⁻¹) _ hinv, trace_of_diag v (ρ g) μ hsv, map_sum]
end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
