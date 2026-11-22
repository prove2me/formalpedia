-- Prove2me | solution 1 for Formalism.CountingSumsFrames.multiDeg_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:45:53.259819+00:00
-- url     : https://prove2.me/submissions/f31a9d99-98dd-4def-a677-db6c891ba796

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) : ({m | MultiDeg (r := r) LL m} : Set (Fin N × Fin r →₀ ℕ)).Finite := by
  classical
  let bnd : Fin N × Fin r →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => LL.total)
  refine (Set.finite_Iic bnd).subset ?_
  intro m hm
  rw [Set.mem_Iic, Finsupp.le_def]
  intro a
  have h1 : m a ≤ ∑ c, m (a.1, c) :=
    Finset.single_le_sum (f := fun c => m (a.1, c)) (fun _ _ => Nat.zero_le _) (mem_univ a.2)
  have h2 : LL.deg a.1 ≤ LL.total :=
    Finset.single_le_sum (f := fun i => LL.deg i) (fun _ _ => Nat.zero_le _) (mem_univ a.1)
  have h3 : bnd a = LL.total := by simp [bnd]
  rw [h3]
  rw [hm a.1] at h1
  omega
end Formalism.CountingSumsFrames
