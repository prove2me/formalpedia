-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.cardQuadruplesProdLe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:58:26.715654+00:00
-- url     : https://prove2.me/submissions/65a15d10-2f4d-43df-a602-8bf22ffb42ba

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : QuadCount := by
  intro De hDe
  obtain ⟨N, hN⟩ : ∃ N, N = ⌊De⌋₊ := ⟨_, rfl⟩
  have hsub : {q : Fin 4 → ℕ | (∀ i, 1 ≤ q i) ∧ ((∏ i, q i : ℕ) : ℝ) ≤ De} ⊆
      ↑(Fintype.piFinset (fun _ : Fin 4 => Finset.Icc 1 N)) := by
    intro q hq
    obtain ⟨h1, h2⟩ := hq
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_Icc]
    refine ⟨h1 i, ?_⟩
    rw [hN]
    apply Nat.le_floor
    have hpos : 0 < ∏ j, q j := Finset.prod_pos (fun j _ => h1 j)
    have hqi : q i ≤ ∏ j, q j := Nat.le_of_dvd hpos (Finset.dvd_prod_of_mem q (Finset.mem_univ i))
    exact le_trans (by exact_mod_cast hqi) h2
  refine ⟨(Fintype.piFinset (fun _ : Fin 4 => Finset.Icc 1 N)).finite_toSet.subset hsub, ?_⟩
  have hcard : ({q : Fin 4 → ℕ | (∀ i, 1 ≤ q i) ∧ ((∏ i, q i : ℕ) : ℝ) ≤ De}).ncard ≤
      (Fintype.piFinset (fun _ : Fin 4 => Finset.Icc 1 N)).card := by
    rw [← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Fintype.card_piFinset, Finset.prod_const, Nat.card_Icc, Finset.card_univ,
    Fintype.card_fin, Nat.add_sub_cancel] at hcard
  have hNDe : (N:ℝ) ≤ De := by rw [hN]; exact Nat.floor_le (by linarith)
  calc (({q : Fin 4 → ℕ | (∀ i, 1 ≤ q i) ∧ ((∏ i, q i : ℕ) : ℝ) ≤ De}).ncard : ℝ)
        ≤ ((N ^ 4 : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (N:ℝ) ^ 4 := by push_cast; try ring
    _ ≤ De ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hNDe 4
end Formalism.HermitianLatticeCounting.P
