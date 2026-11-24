-- Prove2me | solution 1 for Formalism.WeaklyAdmissibleFiltrations.trivialIsCrystalline_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:42:11.157089+00:00
-- url     : https://prove2.me/submissions/6890e974-8005-4376-be04-83c85dd4f381

import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CocyclesFunctorial
import Definitions.Def_Formalism_WeaklyAdmissibleFiltrations_CrystallineStableLifts_TrivCrys
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
section TrivCrysProof
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
include PD in
private theorem trivCrys_nontrivial_B : Nontrivial B := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  apply PD.not_mem_filtration_two
  rw [Subsingleton.elim PD.t 0, map_zero]
  exact zero_mem _
private theorem trivCrys_act_tmul (g : G) (l : LL) (b : B) :
    actVB PD (1 : Representation LL G LL) g (l ⊗ₜ[Qp] b) = l ⊗ₜ[Qp] PD.actB g b := by
  simp [actVB]
private theorem trivCrys_range_le (g : G) (y : LL ⊗[Qp] K₀) :
    actVB PD (1 : Representation LL G LL) g (trivCrysMap (LL := LL) (B := B) y) =
      trivCrysMap (LL := LL) (B := B) y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    simp only [trivCrysMap, trivCrysIncl, AlgebraTensorModule.lTensor_tmul, LinearMap.restrictScalars_apply,
      Algebra.linearMap_apply, trivCrys_act_tmul]
    rw [AlgEquiv.commutes]
  | add y z hy hz => rw [map_add, map_add, hy, hz]
variable [FiniteDimensional Qp LL]
private theorem trivCrysCoord_tmul (b : Basis (Fin (finrank Qp LL)) Qp LL) (i) (l : LL) (c : B) :
    trivCrysCoord (B := B) b i (l ⊗ₜ[Qp] c) = b.coord i l • c := by
  simp [trivCrysCoord]
private theorem trivCrys_decomp (b : Basis (Fin (finrank Qp LL)) Qp LL) (x : LL ⊗[Qp] B) :
    x = ∑ i, b i ⊗ₜ[Qp] trivCrysCoord (B := B) b i x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    simp only [trivCrysCoord_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Basis.coord_apply]
    rw [← TensorProduct.sum_tmul, Basis.sum_repr]
  | add y z hy hz =>
    conv_lhs => rw [hy, hz]
    rw [← Finset.sum_add_distrib]
    simp only [map_add, TensorProduct.tmul_add]
private theorem trivCrysCoord_act (b : Basis (Fin (finrank Qp LL)) Qp LL) (i) (g : G)
    (x : LL ⊗[Qp] B) :
    trivCrysCoord (B := B) b i (actVB PD (1 : Representation LL G LL) g x) =
      PD.actB g (trivCrysCoord (B := B) b i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l c =>
    rw [trivCrys_act_tmul, trivCrysCoord_tmul, trivCrysCoord_tmul]
    exact (((PD.actB g).toAlgHom.toLinearMap).restrictScalars Qp).map_smul _ _ |>.symm
  | add y z hy hz => simp only [map_add, hy, hz]
private theorem trivCrys_Dcris_eq :
    Dcris PD (1 : Representation LL G LL) = LinearMap.range (trivCrysMap (LL := LL) (K₀ := K₀) (B := B)) := by
  apply le_antisymm
  · intro x hx
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero] at hx
    let b := Module.finBasis Qp LL
    have hc : ∀ i, ∃ c : K₀, algebraMap K₀ B c = trivCrysCoord (B := B) b i x := by
      intro i
      apply PD.invB
      intro g
      rw [← trivCrysCoord_act PD b i g x, hx g]
    choose c hc using hc
    refine ⟨∑ i, b i ⊗ₜ[Qp] c i, ?_⟩
    rw [map_sum, trivCrys_decomp b x]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [trivCrysMap, trivCrysIncl, AlgebraTensorModule.lTensor_tmul, LinearMap.restrictScalars_apply,
      Algebra.linearMap_apply, hc i]
  · rintro _ ⟨y, rfl⟩
    simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
      sub_eq_zero]
    exact fun g => trivCrys_range_le PD g y
include PD in
private theorem trivCrysMap_injective :
    Function.Injective (trivCrysMap (Qp := Qp) (LL := LL) (K₀ := K₀) (B := B)) := by
  haveI := trivCrys_nontrivial_B PD
  have hi : Function.Injective (trivCrysIncl (Qp := Qp) (K₀ := K₀) (B := B)) :=
    (algebraMap K₀ B).injective
  have h2 := Module.Flat.lTensor_preserves_injective_linearMap (M := LL) _ hi
  exact h2
end TrivCrysProof
end Formalism.WeaklyAdmissibleFiltrations
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.WeaklyAdmissibleFiltrations
open Module TensorProduct
namespace Formalism.WeaklyAdmissibleFiltrations
theorem _root_.solution : TrivCrys := by
  intro G _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ PD LL _ _ _ _
  unfold IsCrys
  rw [trivCrys_Dcris_eq PD (LL := LL), LinearMap.finrank_range_of_inj (trivCrysMap_injective PD),
    Module.finrank_baseChange, Module.finrank_self, mul_one]
end Formalism.WeaklyAdmissibleFiltrations
