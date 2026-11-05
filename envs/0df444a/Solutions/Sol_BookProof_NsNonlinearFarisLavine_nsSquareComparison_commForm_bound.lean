-- Prove2me | solution 1 for BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-04T23:17:58.049122+00:00
-- url     : https://prove2.me/submissions/8f7db7ae-e778-47d6-92a5-b4d58c1e5808

-- Generated from ChapterNsNonlinearFarisLavine.lean — solution of BookProof.NsNonlinearFarisLavine.nsSquareComparison_commForm_bound
import Mathlib
import Definitions.Def_ChapterNsNonlinearFarisLavine
import Theorems.Thm_BookProof_NsNonlinearFarisLavine_nsSquareComparison_quadForm
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterA4
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterHermiteProductCore
open BookProof.NsNonlinearFarisLavine




open MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine
open BookProof.NsKoopman
open BookProof.HermiteProductCore

noncomputable section

variable {d : ℕ} (S : NsSystem d)

variable {d : ℕ} (S : NsSystem d)

set_option maxHeartbeats 1000000 in
theorem solution {L : ℝ} (hL : ∀ i, S.lam i ≤ L) (hL0 : 0 ≤ L)
    (x : polyGaussCore (d := d)) :
    |commForm (nsKoopmanOp S) (nsSquareComparison S) x|
      ≤ (2 * S.nu * L) * quadForm (nsSquareComparison S) x := by

  have hcf : commForm (nsKoopmanOp S) (nsSquareComparison S) x
      = commForm (nsKoopmanOp S) (nsEnergyOp (d := d)) x :=
    commForm_square_comparison (nsKoopmanCore S) _ (nsKoopmanOp_symmetricOn S) x
  rw [hcf]
  refine le_trans (commForm_kvn_energy_bound S hL hL0 x) ?_
  have hc : 0 ≤ 2 * S.nu * L := mul_nonneg (by linarith [S.nu_nonneg]) hL0
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [nsSquareComparison_quadForm]
  nlinarith [sq_nonneg ‖nsKoopmanOp S x‖]
