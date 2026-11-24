-- Prove2me | solution 1 for Formalism.CountingSumsFrames.TO.piPsi_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:01:36.963995+00:00
-- url     : https://prove2.me/submissions/399e7ba7-040c-4f28-a867-74a46e20a186

import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_TieOps
import Theorems.Thm_Formalism_CountingSumsFrames_TO_psi_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames Formalism.CountingSumsFrames.TO
open Formalism.GM Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
variable [NeZero r] (L : Letters N) (j0 e : ℕ) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
  (Pi φ : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p])
  (hPi : IsProjC L j0 e J M Pi) (hφ : IsEqC L j0 J M φ)
include hPi
namespace Formalism.CountingSumsFrames.TO
theorem _root_.solution (x : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Pi (psi p L j0 x) ∈ Cset p L j0 J M :=
  Submodule.mem_inf.mpr ⟨hPi.pol (Lz L j0) rfl _ (psi_mem L j0 x), (Submodule.mem_iInf _).mpr fun k => hPi.ycond _ k⟩
end Formalism.CountingSumsFrames.TO
