-- Prove2me | solution 1 for Formalism.HN.DualPolygon.exists_int_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:40:13.352357+00:00
-- url     : https://prove2.me/submissions/950f0fb2-01a2-4b39-9280-e6f5571527dd

import Definitions.Def_Formalism_HarderNarasimhan_QuotRealize
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PlaceSplit
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Duality
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ExistsSmulMemOfFinrankEq
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.HN Formalism.HN.DualPolygon
open Formalism.HN
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
omit [Fintype ι] [DecidableEq ι]
namespace Formalism.HN.DualPolygon
theorem _root_.solution {n : ℕ} (A : Submodule (𝓞 K) V) (e : Basis (Fin n) K V)
    (he : ∀ i, e i ∈ A) (w : V) : ∃ c : ℤ, c ≠ 0 ∧ ((c : K)) • w ∈ A := by
  classical
  obtain ⟨y, hy, hint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image fun i => e.repr w i)
  refine ⟨y, hy, ?_⟩
  rw [← e.sum_repr w, Finset.smul_sum]
  apply Submodule.sum_mem
  intro i _
  have hi : IsIntegral ℤ (y • e.repr w i) :=
    hint _ (Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩)
  let r : 𝓞 K := ⟨y • e.repr w i, hi⟩
  have hr : ((y : K)) • (e.repr w i • e i) = r • e i := by
    rw [← algebraMap_smul K r, smul_smul]
    congr 1
    show (y : K) * e.repr w i = y • e.repr w i
    rw [zsmul_eq_mul]
  rw [hr]
  exact Submodule.smul_mem _ _ (he i)
end Formalism.HN.DualPolygon
