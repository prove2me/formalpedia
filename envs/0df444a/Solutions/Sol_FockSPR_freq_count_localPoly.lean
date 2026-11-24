-- Prove2me | solution 1 for FockSPR.freq_count_localPoly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:45:45.972827+00:00
-- url     : https://prove2.me/submissions/15ca97bf-2bd4-4316-981d-bfd92aff853d

module
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_Constant_Internal_BlockDecomposition
public import Theorems.Thm_FockSPR_freqBlock_card
section
@[expose] public section
open Finset Nat Real MeasureTheory
noncomputable section
namespace FockSPR
private lemma sum_odd_Icc_eq (a : ℕ) :
    ∀ n : ℕ, (Finset.Icc a (a + n)).sum (fun ℓ => 2 * ℓ + 1) =
      (a + n + 1) ^ 2 - a ^ 2 := by
  intro n; induction n with
  | zero => simp [Finset.Icc_self]; ring_nf; omega
  | succ n ih =>
    rw [show a + (n + 1) = (a + n) + 1 from by omega]
    rw [Finset.sum_Icc_succ_top (by omega)]; rw [ih]; ring_nf; omega
end FockSPR
end
end
end

set_option autoImplicit true
@[expose] public section
public section
open Finset Nat Real MeasureTheory
noncomputable section
open FockSPR
namespace FockSPR
theorem _root_.solution {M j : ℕ} (hM : 1 ≤ M) (hj : M + 1 ≤ j) :
    (Finset.Icc (max 1 (j - M)) (j + M)).sum
      (fun ℓ => (freqBlock ℓ).card) =
      (2 * M + 1) * (2 * j + 1) := by
  rw [show max 1 (j - M) = j - M from by omega]
  simp_rw [freqBlock_card]
  rw [show j + M = (j - M) + (2 * M) from by omega,
      sum_odd_Icc_eq (j - M) (2 * M),
      show j - M + 2 * M + 1 = j + M + 1 from by omega]
  have hle : (j - M) ^ 2 ≤ (j + M + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  zify [hle, show M ≤ j from by omega]; ring
end FockSPR
