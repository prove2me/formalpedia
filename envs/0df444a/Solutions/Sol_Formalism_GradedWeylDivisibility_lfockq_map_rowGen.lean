-- Prove2me | solution 1 for Formalism.GradedWeylDivisibility.lfockq_map_rowGen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:28:54.006809+00:00
-- url     : https://prove2.me/submissions/9aaee6a8-50fe-4f3e-876a-9ca2c316aa9b

import Definitions.Def_Formalism_GradedWeylDivisibility_StatementB
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockqLemmas
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockRowAdj
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQRowDivAdj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.REAL
noncomputable section
open Formalism Formalism.GradedWeylDivisibility
namespace Formalism.GradedWeylDivisibility
theorem _root_.solution {r n : ℕ} (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) ℚ) :
    rowGen ℂ a b (map (Rat.castHom ℂ) f) =
      Polynomial.map (map (Rat.castHom ℂ)) (rowGen ℚ a b f) := by
  have h : ((rowGen ℂ a b).toRingHom.comp (map (Rat.castHom ℂ)) :
      MvPolynomial (Fin r × Fin n) ℚ →+* Polynomial (MvPolynomial (Fin r × Fin n) ℂ)) =
      (Polynomial.mapRingHom (map (Rat.castHom ℂ))).comp (rowGen ℚ a b).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro q
      simp [rowGen]
    · intro v
      simp only [rowGen, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, MvPolynomial.map_X, MvPolynomial.aeval_X, Polynomial.coe_mapRingHom]
      split_ifs <;> simp
  exact RingHom.congr_fun h f
end Formalism.GradedWeylDivisibility
