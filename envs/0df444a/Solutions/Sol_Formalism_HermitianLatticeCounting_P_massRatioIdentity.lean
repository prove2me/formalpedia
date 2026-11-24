-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.massRatioIdentity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:37.48905+00:00
-- url     : https://prove2.me/submissions/2bc72cc6-bc4e-4b06-a8ff-d1adb1922cfa

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
theorem _root_.solution : XiIdentity := by
  intro mass mj k s hmj hm2 hrec hs hk
  have step : ∀ a n, 2 ≤ a → mass (a + n) = mass a * ∏ i ∈ Finset.Ioc a (a + n), mj i := by
    intro a n ha
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← add_assoc, Finset.prod_Ioc_succ_top (show a ≤ a + n by omega),
        hrec (a + n + 1) (by omega), Nat.add_sub_cancel, ih]
      ring
  have pos : ∀ n, 2 ≤ n → 0 < mass n := by
    intro n hn
    obtain ⟨d, rfl⟩ : ∃ d, n = 2 + d := ⟨n - 2, by omega⟩
    rw [step 2 d le_rfl]
    exact mul_pos hm2 (Finset.prod_pos (fun i _ => hmj i))
  have h1 : mass s = mass 2 * ∏ i ∈ Finset.Ioc 2 s, mj i := by
    obtain ⟨d, rfl⟩ : ∃ d, s = 2 + d := ⟨s - 2, by omega⟩
    exact step 2 d le_rfl
  have h2 : mass k = mass (k - s) * ∏ i ∈ Finset.Ioc (k - s) k, mj i := by
    have := step (k - s) s (by omega)
    rwa [Nat.sub_add_cancel (by omega)] at this
  have hks := pos (k - s) (by omega)
  have hP : 0 < ∏ i ∈ Finset.Ioc (k - s) k, mj i := Finset.prod_pos (fun i _ => hmj i)
  rw [h2, h1, div_eq_div_iff (mul_pos hks hP).ne' hP.ne']
  ring
end Formalism.HermitianLatticeCounting.P
