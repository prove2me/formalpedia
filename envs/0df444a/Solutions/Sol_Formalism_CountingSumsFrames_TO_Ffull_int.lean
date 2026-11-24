-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.Ffull_int
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:46:28.853654+00:00
-- url     : https://prove2.me/submissions/83edec9c-c859-4b22-baab-87b438675824

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_intPol_rename
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_Ffull_eq
import Theorems.Thm_Formalism_GM_extendMapsTo


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity Formalism.GM.TM MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero N] [NeZero r] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t) (ρ : Fin r)
  (hρ : (ρ : ℕ) = r - 1) (n : Fin T.t → ℕ) (hS : ((LL.setTies T n).takeD (T.pos i + 1)).total ≤ n i)
include hadm hS
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (f : MvPolynomial (Fin (T.pos i + 1) × Fin r) ℚ_[p])
    (hf : f ∈ PolZ p r ((LL.setTies T n).takeD (T.pos i + 1))) :
    T.Ffull p (LL.setTies T n) i ρ (n i) f ∈ IntPol p (Fin N × Fin r) := by
  obtain ⟨hP, hI⟩ := Submodule.mem_inf.mp hf
  have h1 := (Formalism.GM.extendMapsTo p (T.pos i + 1) r _ ρ (n i) hS f hP).2.2 hI
  rw [Ffull_eq]
  exact intPol_rename _ h1
end Formalism.CountingSumsFrames.TO
