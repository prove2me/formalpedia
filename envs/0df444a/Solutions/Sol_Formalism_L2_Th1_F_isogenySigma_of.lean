-- Prove2me | solution 1 for Formalism.L2.Th1.F.isogenySigma_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:40:54.751893+00:00
-- url     : https://prove2.me/submissions/d1eb5955-eb2d-435f-b9f2-ad8846e7ed9c

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_TranslateProduct
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_IsogenySigma
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_exists_const
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_const_eq_one
import Theorems.Thm_Formalism_L2_Th1_F_IsogenySigmaQuotient_fac_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F
open IsogenySigmaQuotient
namespace Formalism.L2.Th1.F
theorem _root_.solution (hN : EllipticNoPole) (hord : SigmaOrder) (hsa : SgStarAdd)
    (hq : SgStarQuasi) (hb : SgStarBasic) (hcard : KerRepsCard) (he : SigmaEntire) :
    IsogenySigma := by
  intro L α S hα hst hS z hz
  have hc := hcard L α S hα hst hS
  have hS' : ∀ P ∈ S, P ∉ L.lattice := fun P hP => (hS.1 P hP).2
  obtain ⟨c, hc'⟩ := exists_const L α S hN hord he hb hq hα hst hS hc
  have h1 := const_eq_one L α S hb hα hS' c hc'
  subst h1
  have h := hc' z
  simp only [num, den, one_mul] at h
  rw [h, Finset.prod_congr rfl (fun P hP => fac_eq L hb hsa P z (hS' P hP) hz), Finset.prod_mul_distrib,
    Finset.prod_const]
  ring
end Formalism.L2.Th1.F
