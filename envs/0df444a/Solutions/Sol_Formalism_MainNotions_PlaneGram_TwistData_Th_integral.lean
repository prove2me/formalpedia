-- Prove2me | solution 1 for Formalism.MainNotions.PlaneGram.TwistData.Th_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:38:15.048545+00:00
-- url     : https://prove2.me/submissions/2f227a6b-2c8f-4756-ab51-749695e70c73

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_pullE_deg
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Th_monomial
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_monomial__f1d6e36a6b91
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_mul__6cb3f7e6a827
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_smul__67d1bab69c28
import Theorems.Thm_P2M_Formalism_MainNotions_PlaneGram_integral_sum__e111d2e1e1a9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)
variable {ι : Type} [Fintype ι]
variable (cc : (Fin (D.nB j + D.r) × Fin D.r →₀ ℕ) → ι → K) (PP : ι → MvPolynomial (D.ML × Fin D.r) K)
namespace Formalism.MainNotions.PlaneGram.TwistData
theorem _root_.solution {v : AddValuation K (WithTop ℚ)}
    (hccint : ∀ lam, (∀ k, ldeg lam k = D.dO (D.eA j k)) → ∀ b, 0 ≤ v (cc lam b))
    (hPP : ∀ b, Integral v (PP b)) (ζ : D.EM) (hζ : D.PreE j ζ) :
    Integral v (D.Th j cc PP (monomial ζ 1)) := by
  rw [Th_monomial]
  apply integral_mul' (integral_monomial' _ (by simp))
  apply integral_sum'
  intro b _
  exact integral_smul' (hccint _ (D.pullE_deg j ζ hζ) b) (hPP b)
end Formalism.MainNotions.PlaneGram.TwistData
