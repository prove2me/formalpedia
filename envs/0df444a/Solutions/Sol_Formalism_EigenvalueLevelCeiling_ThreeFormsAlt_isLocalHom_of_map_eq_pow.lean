-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ThreeFormsAlt.isLocalHom_of_map_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:32:45.788804+00:00
-- url     : https://prove2.me/submissions/b1abb217-b6f9-4130-90f4-f5f31b8af0a7

import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementL
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_IdxRules
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_LocBasic
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ImageLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_IdxChange
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_ThreeForms

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain Formalism.HermitianLatticesTheory
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
open Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
open IsLocalRing
namespace Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
theorem _root_.solution (O O' : Type) [CommRing O] [IsLocalRing O] [CommRing O']
    [IsLocalRing O'] [Algebra O O'] (e : ℕ) (he : e ≠ 0)
    (h : Ideal.map (algebraMap O O') (maximalIdeal O) = maximalIdeal O' ^ e) :
    IsLocalHom (algebraMap O O') := by
  constructor
  intro a ha
  by_contra hna
  have hm : a ∈ maximalIdeal O := hna
  have h1 : algebraMap O O' a ∈ maximalIdeal O' ^ e := h ▸ Ideal.mem_map_of_mem _ hm
  exact (mem_maximalIdeal _).mp (Ideal.pow_le_self he h1) ha
end Formalism.EigenvalueLevelCeiling.ThreeFormsAlt
