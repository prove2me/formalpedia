-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.unitaryOrderRatioBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:41.645961+00:00
-- url     : https://prove2.me/submissions/6cbd8f66-66af-40a6-8dfe-db7ec834b416

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
theorem _root_.solution : ThetaBound := by
  intro j e η q hej hq hη
  have hfac : ∀ i ∈ Finset.Icc (j - e + 1) j,
      0 < 1 - η ^ i * (q ^ i)⁻¹ ∧ 1 - η ^ i * (q ^ i)⁻¹ ≤ 3 / 2 := by
    intro i hi
    have hi1 : 1 ≤ i := by simp only [Finset.mem_Icc] at hi; omega
    have hqi : 2 ≤ q ^ i := by
      calc (2:ℝ) ≤ q := hq
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ i := pow_le_pow_right₀ (by linarith) hi1
    have hx0 : 0 < (q ^ i)⁻¹ := inv_pos.mpr (by linarith)
    have hx : (q ^ i)⁻¹ ≤ 1 / 2 := by
      have := inv_anti₀ (by norm_num : (0:ℝ) < 2) hqi
      linarith [show (2:ℝ)⁻¹ = 1 / 2 by norm_num]
    have hs : η ^ i = 1 ∨ η ^ i = -1 := by
      rcases hη with rfl | rfl
      · left; exact one_pow i
      · exact neg_one_pow_eq_or ℝ i
    rcases hs with h | h <;> rw [h] <;> constructor <;> linarith
  unfold Formalism.HermitianLatticeCounting.LatticeSumBounds.theta
  have hcard : (Finset.Icc (j - e + 1) j).card = e := by rw [Nat.card_Icc]; omega
  have hle : ∏ i ∈ Finset.Icc (j - e + 1) j, (1 - η ^ i * (q ^ i)⁻¹) ≤ (3 / 2) ^ e := by
    calc ∏ i ∈ Finset.Icc (j - e + 1) j, (1 - η ^ i * (q ^ i)⁻¹)
          ≤ ∏ _i ∈ Finset.Icc (j - e + 1) j, (3 / 2 : ℝ) :=
          Finset.prod_le_prod (fun i hi => (hfac i hi).1.le) (fun i hi => (hfac i hi).2)
      _ = (3 / 2) ^ e := by rw [Finset.prod_const, hcard]
  refine ⟨Finset.prod_pos (fun i hi => (hfac i hi).1), hle, hle.trans ?_⟩
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) e
end Formalism.HermitianLatticeCounting.P
