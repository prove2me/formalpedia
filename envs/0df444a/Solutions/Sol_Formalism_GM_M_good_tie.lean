-- Prove2me | solution 1 for Formalism.GM.M.good_tie
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:24:58.227437+00:00
-- url     : https://prove2.me/submissions/c5106fcb-a03d-414f-9153-d5977fc9c503

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
import Theorems.Thm_Formalism_GM_M_scalS_inj
import Theorems.Thm_Formalism_GM_M_scalZ_ne_scalS

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M
open MvPolynomial Finset SSD
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable {t : ℕ}
namespace Formalism.GM.M
theorem _root_.solution (i : Fin (t + 1)) (e : MvPolynomial (BVar N r t) ℚ_[p]) (he : SFree (scalS N r t) e) :
    Good (scalS N r t) (X (scalZ N r t i) * X (scalS N r t i) + e) (Pi.single i 1)
      (Finsupp.single (scalZ N r t i) 1 + Finsupp.single (scalS N r t i) 1) := by
  refine ⟨?_, ?_⟩
  · funext k
    simp only [sd, Finsupp.add_apply, Finsupp.single_apply]
    rw [if_neg (scalZ_ne_scalS i k)]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg (fun h' => h (scalS_inj h')), Pi.single_apply, if_neg (Ne.symm h)]; rfl
  · have : X (scalZ N r t i) * X (scalS N r t i) + e -
        monomial (Finsupp.single (scalZ N r t i) 1 + Finsupp.single (scalS N r t i) 1) (1 : ℚ_[p]) = e := by
      rw [X, X, monomial_mul, mul_one, add_sub_cancel_left]
    rw [this]
    intro m hm
    rw [he m hm]
    refine ⟨fun k => Nat.zero_le _, fun h => ?_⟩
    have := congrFun h i
    simp at this
end Formalism.GM.M
