-- Prove2me | solution 1 for Formalism.L2.Geo.Rec.DualLatticeEmbeddings.span_Mz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:11:56.016641+00:00
-- url     : https://prove2.me/submissions/5b62b4ea-be1e-4582-a2cf-dbcdabfcf522

import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_GelfandTransference_EnergyIdentity
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_ExistsStarMulSelf
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_RealizationNorms_SumUliftFinsetFinTwoExpand
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_finrank_amb
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_exists_int_smul_mem
import Theorems.Thm_Formalism_L2_Geo_Rec_DualLatticeEmbeddings_mem_Mz
import Theorems.Thm_Formalism_HN_PlaceLattice_linIndep_real


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open NumberField NumberField.InfinitePlace Module Matrix
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Rec Formalism.L2.Geo.Rec.DualLatticeEmbeddings
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
variable [StarRing K]
namespace Formalism.L2.Geo.Rec.DualLatticeEmbeddings
theorem _root_.solution [IsTotallyComplex K] (Xf : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ)
    (hXf : ∀ v, IsUnit (Xf v).det)
    (X : Submodule (𝓞 K) (Fin n → K)) (hX : Submodule.span K (X : Set (Fin n → K)) = ⊤) :
    Submodule.span ℝ (Mz Xf X : Set (Amb K n)) = ⊤ := by
  classical
  choose N hN0 hNX using fun k : Fin n => exists_int_smul_mem X hX (Pi.basisFun K (Fin n) k)
  let c : ℤ := ∏ k, N k
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hN0 k
  have hcK : (c : K) ≠ 0 := Int.cast_ne_zero.2 hc0
  have hli := Formalism.HN.PlaceLattice.linIndep_real (Pi.basisFun K (Fin n)) Xf hXf (c : K) hcK
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 K) × Fin n) = finrank ℝ (Amb K n) := by
    rw [finrank_amb, Fintype.card_prod, ← finrank_eq_card_chooseBasisIndex, RingOfIntegers.rank,
      Fintype.card_fin]
  have htop := hli.span_eq_top_of_card_eq_finrank' hcard
  rw [eq_top_iff, ← htop]
  refine Submodule.span_mono ?_
  rintro _ ⟨⟨m, k⟩, rfl⟩
  rw [SetLike.mem_coe, mem_Mz]
  refine ⟨_, ?_, rfl⟩
  have h1 : (c : K) • (Pi.basisFun K (Fin n) k) = (∏ j ∈ Finset.univ.erase k, N j) • (N k • Pi.basisFun K (Fin n) k) := by
    rw [smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ k), Int.cast_smul_eq_zsmul]
  rw [integralBasis_apply, algebraMap_smul, h1]
  exact X.smul_mem _ (X.toAddSubgroup.zsmul_mem (hNX k) _)
end Formalism.L2.Geo.Rec.DualLatticeEmbeddings
