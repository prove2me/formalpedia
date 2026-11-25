-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.G0.almost_everywhere_spherical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:57.369252+00:00
-- url     : https://prove2.me/submissions/317bb590-4386-4bbd-9b42-20c83cf943a6

import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ElementarySymmetricExpBound
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_ManyOrbits
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_LePowOddOfFloorLogbLe
import Definitions.Def_Formalism_ThetaLogCoordinates_ProductIdealMonotone_ProductIdealProofs_ElementarySymmetricExpBound
import Theorems.Thm_Formalism_InvariantFactorPaths_G0_max_eq_add_pp
import Theorems.Thm_Formalism_InvariantFactorPaths_G0_monoOp_eq_smul
import Theorems.Thm_Formalism_InvariantFactorPaths_G0_fil_pow_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical Pointwise
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G0
open Formalism.G0
namespace Formalism.InvariantFactorPaths.G0
theorem _root_.solution : AlmostEverywhereSpherical := by
  intro R X Z _ _ _ _ _ π vπ V m M y Sv K Fil g Pr g0 rest hanti hπ hS hE F hF
  have key : ∀ E : Fin V → Bool, M.map (monoOp π y m Sv E) ≤
      (Fil ((∑ j, ∑ v, max (g v j - Pr v j) (g0 v j)) + rest)).comap K := by
    intro E
    rintro _ ⟨x, hx, rfl⟩
    rw [Submodule.mem_comap, monoOp_eq_smul, LinearMap.smul_apply, map_smul]
    have h1 := fil_pow_smul π vπ Fil hπ (∑ v, if E v = true then 0 else Sv v) _ _ (hE E x hx)
    refine hanti ?_ h1

    have hsplit : ∀ j, ∑ v, max (g v j - Pr v j) (g0 v j) =
        (∑ v with E v = true, max (g v j - Pr v j) (g0 v j)) + ∑ v with E v = false, g0 v j
          + ∑ v with E v = false, pp (g v j - Pr v j - g0 v j) := by
      intro j
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => E v = true)]
      simp only [Bool.not_eq_true]
      rw [add_assoc, ← Finset.sum_add_distrib]
      congr 1
      exact Finset.sum_congr rfl fun v _ => max_eq_add_pp _ _
    have hpp : ∑ j, ∑ v with E v = false, pp (g v j - Pr v j - g0 v j) ≤
        vπ * ((∑ v, if E v = true then 0 else Sv v : ℕ) : ℝ) := by
      rw [Finset.sum_comm]
      calc ∑ v with E v = false, ∑ j, pp (g v j - Pr v j - g0 v j)
          ≤ ∑ v with E v = false, vπ * (Sv v : ℝ) := Finset.sum_le_sum fun v _ => hS v
        _ = vπ * ((∑ v, if E v = true then 0 else Sv v : ℕ) : ℝ) := by
          rw [← Finset.mul_sum, Finset.sum_filter]
          congr 1
          push_cast
          refine Finset.sum_congr rfl fun v _ => ?_
          cases E v <;> simp
    simp only [hsplit, Finset.sum_add_distrib]
    linarith
  exact iSup_le key hF
end Formalism.InvariantFactorPaths.G0
