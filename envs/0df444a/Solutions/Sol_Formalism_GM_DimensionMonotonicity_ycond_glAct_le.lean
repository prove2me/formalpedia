-- Prove2me | solution 1 for Formalism.GM.DimensionMonotonicity.ycond_glAct_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:37.720475+00:00
-- url     : https://prove2.me/submissions/f1695b8a-68f4-4a6c-833a-2bc1bb8f1858

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_WeightSpaceDimensionMonotone
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_ycond_of_comm
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_glAct_split
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_midAct_comm
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_midAct_wh
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.GM.DimensionMonotonicity
open Finset
namespace GlW
variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
variable {r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
namespace GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open Finset
namespace GlW
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} (G : GlW K V r)
end GlW
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
section Ops
variable {K : Type} [CommRing K] {σ : Type} [DecidableEq σ]
end Ops
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
section W
variable {K : Type} [CommRing K] {σ : Type} [DecidableEq σ] {M : Type} [AddCommGroup M]
end W
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
private theorem ycond_stable_lemma_2 [NeZero r] (LL : Letters N) (J : ℕ) (M : WithTop ℤ) :
    GlStable p LL J (YCond p (r := r) LL J M) := by
  intro c d x hx
  have hle : YCond p (r := r) LL J M ≤ (YCond p (r := r) LL J M).comap (glAct p LL J c d) := by
    unfold YCond
    apply sSup_le
    intro S hS y hy
    exact le_sSup hS (hS.2 c d y hy)
  exact hle hx
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
section Comparison₂
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
end Comparison₂
section Tie2
variable [NeZero N] (LL : Letters N) (T : TieData) (hadm : T.Admissible LL) (i : Fin T.t)
include hadm
end Tie2
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
end Formalism.GM.DimensionMonotonicity
namespace Formalism.GM
end Formalism.GM
end

set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.DimensionMonotonicity
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.GM.DimensionMonotonicity
theorem _root_.solution [NeZero r] (LL : Letters N) {J j0 : ℕ} (hJ : J ≤ j0) (M : WithTop ℤ) (c d : Fin r)
    {F : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hF : F ∈ YCond p LL J M) :
    glAct p LL j0 c d F ∈ YCond p LL J M := by
  rw [glAct_split LL hJ c d, LinearMap.add_apply]
  exact Submodule.add_mem _ (ycond_stable_lemma_2 LL J M c d F hF)
    (ycond_of_comm LL J M (midAct p LL J j0 c d) (fun c' d' G => midAct_comm LL J j0 c d c' d' G)
      (fun ν G hG => midAct_wh LL J j0 c d hG) F hF)
end Formalism.GM.DimensionMonotonicity
