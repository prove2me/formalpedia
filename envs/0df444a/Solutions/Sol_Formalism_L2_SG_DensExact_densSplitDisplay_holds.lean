-- Prove2me | solution 1 for Formalism.L2.SG.DensExact.densSplitDisplay_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:21:19.297619+00:00
-- url     : https://prove2.me/submissions/a1631ee8-a8fd-44e6-b25d-1ef56f011f55

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.L2.SG.DensExact
private theorem prod_range_sub_eq_prod_Ico (f : ℕ → ℝ) : ∀ (k N : ℕ), k ≤ N →
    ∏ i ∈ range k, f (N - i) = ∏ j ∈ Ico (N + 1 - k) (N + 1), f j := by
  intro k
  induction k with
  | zero => intro N _; simp
  | succ k ih =>
    intro N hN
    rw [prod_range_succ, ih N (by omega)]
    have h1 : N + 1 - (k + 1) < N + 1 := by omega
    rw [prod_eq_prod_Ico_succ_bot h1]
    have e1 : N + 1 - (k + 1) + 1 = N + 1 - k := by omega
    have e2 : N + 1 - (k + 1) = N - k := by omega
    rw [e1, e2]
    ring
end Formalism.L2.SG.DensExact
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.DensExact
namespace Formalism.L2.SG.DensExact
theorem _root_.solution : DensSplitDisplay := by
  intro q n m c _ hmc
  have h1 : ∏ i ∈ range m, (1 - ((q : ℝ) ^ (n - i))⁻¹) =
      ∏ j ∈ Ico (n - m + 1) (n + 1), (1 - ((q : ℝ) ^ j)⁻¹) := by
    rw [show n - m + 1 = n + 1 - m by omega]
    exact prod_range_sub_eq_prod_Ico (fun j => 1 - ((q : ℝ) ^ j)⁻¹) m n (by omega)
  have h2 : ∏ i ∈ range c, (1 - ((q : ℝ) ^ (n - m - i))⁻¹) =
      ∏ j ∈ Ico (n - m + 1 - c) (n - m + 1), (1 - ((q : ℝ) ^ j)⁻¹) :=
    prod_range_sub_eq_prod_Ico (fun j => 1 - ((q : ℝ) ^ j)⁻¹) c (n - m) (by omega)
  have hD : densProd q 1 n m c =
      ∏ j ∈ Ico (n - m + 1 - c) (n + 1), (1 - ((q : ℝ) ^ j)⁻¹) := by
    unfold densProd
    have hI : Icc (n + 1 - (m + c)) n = Ico (n - m + 1 - c) (n + 1) := by
      ext x; simp only [mem_Icc, mem_Ico]; omega
    rw [hI]
    exact prod_congr rfl (fun i _ => by simp)
  rw [h1, h2, hD, ← prod_Ico_consecutive (fun j => 1 - ((q : ℝ) ^ j)⁻¹)
    (by omega : n - m + 1 - c ≤ n - m + 1) (by omega : n - m + 1 ≤ n + 1)]
  ring
end Formalism.L2.SG.DensExact
