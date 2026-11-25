-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieLD.mapLaT_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:43:01.252057+00:00
-- url     : https://prove2.me/submissions/5c5bf037-f60e-49dc-bdd6-c00018982867

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QCoreSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_LengthBaseChange
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_TieLDB
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_LenDescentOfLengthBaseChangeLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open Formalism.L2.Pj.QAt.TieLD
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
open scoped TensorProduct
attribute [local instance] TieLDA.modT TieLDA.modR
variable {K K₁ : Type} [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Algebra K K₁]
attribute [local instance] algCT
attribute [local instance] locT
attribute [local instance] dvrT
attribute [local instance] dvrLa
attribute [local instance] algLaK
attribute [local instance] towerLaK
attribute [local instance] fracLaK
namespace Formalism.L2.Pj.QAt.TieLD
theorem _root_.solution (la : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 K₁))
    (hw : LiesOver w la) (r : Localization.AtPrime la.asIdeal) :
    ((mapLaT la w hw r : Tw w) : K₁) =
      algebraMap K K₁ (algebraMap (Localization.AtPrime la.asIdeal) K r) := by
  have key : (Tw w).subtype.comp (mapLaT la w hw) =
      (algebraMap K K₁).comp (algebraMap (Localization.AtPrime la.asIdeal) K) := by
    apply IsLocalization.ringHom_ext la.asIdeal.primeCompl
    ext x
    simp only [RingHom.comp_apply, mapLaT, IsLocalization.map_eq]
    rw [← IsScalarTower.algebraMap_apply (𝓞 K) (Localization.AtPrime la.asIdeal) K]
    first
      | rfl
      | simp
      | (norm_cast; simp)
      | exact (trivial : True)
  exact RingHom.congr_fun key r
end Formalism.L2.Pj.QAt.TieLD
