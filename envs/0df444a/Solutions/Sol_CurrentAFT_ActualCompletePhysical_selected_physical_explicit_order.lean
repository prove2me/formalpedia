-- Prove2me | solution 1 for CurrentAFT.ActualCompletePhysical.selected_physical_explicit_order
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T21:38:42.48071+00:00
-- url     : https://prove2.me/submissions/809a5cb8-6767-48a8-9d48-106128e159a8

import Definitions.Def_InfoLossLAR_NativeBundle_12
import Mathlib
namespace AFT
end AFT
namespace AFT.V7Calibration
end AFT.V7Calibration
namespace P2M8f8f5b7e
end P2M8f8f5b7e
section
namespace AFT
open scoped BigOperators
namespace TrimmedSlice
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h21 (modulus boundary shift color : ℤ) :
    _root_.AFT.TrimmedSlice.law modulus boundary shift (modulus - 1 - color) = _root_.AFT.TrimmedSlice.law modulus boundary (-shift) color := by
  have hm : modulus - 1 - color ∈ _root_.AFT.TrimmedSlice.slice modulus boundary shift ↔ color ∈ _root_.AFT.TrimmedSlice.slice modulus boundary (-shift) := by
    simp only [_root_.AFT.TrimmedSlice.mem_slice]
    omega
  simp only [_root_.AFT.TrimmedSlice.law, hm, _root_.AFT.TrimmedSlice.slice_card, abs_neg]
open _root_.P2M8f8f5b7e renaming h21 → _p2mH21
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h20 (start color : ℤ) (width : ℕ) :
    _root_.AFT.intervalAnchorLaw (_root_.AFT.TrimmedSlice.reflectedStart start width) width (-color) = _root_.AFT.intervalAnchorLaw start width color := by
  have hm : -color ∈ _root_.AFT.anchorInterval (_root_.AFT.TrimmedSlice.reflectedStart start width) width ↔ color ∈ _root_.AFT.anchorInterval start width := by
    simp only [_root_.AFT.anchorInterval, Finset.mem_Ico, _root_.AFT.TrimmedSlice.reflectedStart]
    omega
  simp only [_root_.AFT.intervalAnchorLaw, hm]
open _root_.P2M8f8f5b7e renaming h20 → _p2mH20
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h19 (modulus boundary start source color : ℤ) (width : ℕ) :
    _root_.AFT.TrimmedSlice.averagedLaw modulus boundary start source width (modulus - 1 - color) =
      _root_.AFT.TrimmedSlice.averagedLaw modulus boundary (_root_.AFT.TrimmedSlice.reflectedStart start width) (-source) width color := by
  unfold _root_.AFT.TrimmedSlice.averagedLaw _root_.AFT.TrimmedSlice.intervalMixture
  apply Finset.sum_bij (fun offset _ => -offset)
  · intro offset ho
    simp only [_root_.AFT.anchorInterval, Finset.mem_Ico, _root_.AFT.TrimmedSlice.reflectedStart] at ho ⊢
    omega
  · intro a _ b _ hab
    omega
  · intro offset ho
    refine ⟨-offset, ?_, by omega⟩
    simp only [_root_.AFT.anchorInterval, Finset.mem_Ico, _root_.AFT.TrimmedSlice.reflectedStart] at ho ⊢
    omega
  · intro offset _
    dsimp only
    rw [_p2mH20, _p2mH21]
    congr 2
    ring
open _root_.P2M8f8f5b7e renaming h19 → _p2mH19
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h22 {τ : Type*} [Fintype τ]
    (modulus boundary : ℤ) (width : ℕ) (starts targets sources : τ → ℤ) (weights : τ → ℝ)
    (reverse : τ ≃ τ) (hw : ∀ index, weights (reverse index) = weights index)
    (hs : ∀ index, sources (reverse index) = -sources index)
    (ha : ∀ index, targets (reverse index) = _root_.AFT.TrimmedSlice.reflectedStart (starts index) width) (color : ℤ) :
    _root_.AFT.TrimmedSlice.mixedLaw modulus boundary starts sources weights width (modulus - 1 - color) =
      _root_.AFT.TrimmedSlice.mixedLaw modulus boundary targets sources weights width color := by
  unfold _root_.AFT.TrimmedSlice.mixedLaw
  calc
    _ = ∑ index, weights (reverse index) * _root_.AFT.TrimmedSlice.averagedLaw modulus boundary
        (targets (reverse index)) (sources (reverse index)) width color := by
      apply Finset.sum_congr rfl
      intro index _
      rw [hw, ha, hs, _p2mH19]
    _ = _ := Equiv.sum_comp reverse (fun index => weights index *
      _root_.AFT.TrimmedSlice.averagedLaw modulus boundary (targets index) (sources index) width color)
open _root_.P2M8f8f5b7e renaming h22 → _p2mH22
end TrimmedSlice
open _root_.P2M8f8f5b7e renaming h19 → _p2mH19
open _root_.P2M8f8f5b7e renaming h20 → _p2mH20
open _root_.P2M8f8f5b7e renaming h21 → _p2mH21
open _root_.P2M8f8f5b7e renaming h22 → _p2mH22
namespace V7Calibration
end V7Calibration
end AFT
open _root_.P2M8f8f5b7e renaming h19 → _p2mH19
open _root_.P2M8f8f5b7e renaming h20 → _p2mH20
open _root_.P2M8f8f5b7e renaming h21 → _p2mH21
open _root_.P2M8f8f5b7e renaming h22 → _p2mH22
end
open _root_.P2M8f8f5b7e renaming h19 → _p2mH19
open _root_.P2M8f8f5b7e renaming h20 → _p2mH20
open _root_.P2M8f8f5b7e renaming h21 → _p2mH21
open _root_.P2M8f8f5b7e renaming h22 → _p2mH22
namespace AFT.LocalTensors
end AFT.LocalTensors
namespace AFT.PhysicalBlockTensors
end AFT.PhysicalBlockTensors
namespace AFT.PhysicalBlockTensors.compensatedTripleMass
end AFT.PhysicalBlockTensors.compensatedTripleMass
namespace AFT.PhysicalBlockTensors.quadrupleEquiv
end AFT.PhysicalBlockTensors.quadrupleEquiv
namespace AFT.PhysicalBlockTensors.sharedSourceTriple
end AFT.PhysicalBlockTensors.sharedSourceTriple
namespace AFT.PhysicalBlockTensors.tripleEquiv
end AFT.PhysicalBlockTensors.tripleEquiv
namespace AFT.PhysicalBlockTensors.tripleMass
end AFT.PhysicalBlockTensors.tripleMass
namespace AFT.V7Calibration.actualExtraAnchorKernel
end AFT.V7Calibration.actualExtraAnchorKernel
namespace AFT.V7Calibration.actualMarkedSafeSeed
end AFT.V7Calibration.actualMarkedSafeSeed
namespace AFT.V7Calibration.blurredAnchorMean
end AFT.V7Calibration.blurredAnchorMean
namespace AFT.V7Calibration.extraAnchorSeed
end AFT.V7Calibration.extraAnchorSeed
section
namespace AFT.PhysicalBlockTensors
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.AFT.PhysicalBlockTensors.instDecidableEqFin_aFT_1
variable {Source Color : Type*} [Fintype Source] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h1 (source : _root_.AFT.FiniteDist Source)
    (pair : Source → _root_.AFT.FiniteDist (Color × Color))
    (body : Source → Color → Color → _root_.AFT.FiniteDist Color) (color : Color) :
    ((_root_.AFT.PhysicalBlockTensors.sharedSourceTriple source pair body).map (fun word => word 0)).weight color =
      ∑ second, (source.mix pair).weight (color, second) := by
  rw [_root_.AFT.PhysicalBlockTensors.sharedSourceTriple, _root_.AFT.FiniteDist.map_map, _root_.AFT.FiniteDist.map_weight]
  simp only [Fintype.sum_prod_type, _root_.AFT.PhysicalBlockTensors.tripleEquiv, Equiv.coe_fn_symm_mk, Fin.isValue, Matrix.cons_val_zero]
  change (∑ first, ∑ second, ∑ attached, if first = color then
    _root_.AFT.BlockDensity.attachedMass source pair body first second attached else 0) = _
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, _root_.AFT.BlockDensity.attachedMass_marginal,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
open _root_.P2M8f8f5b7e renaming h1 → _p2mH1
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h2 (source : _root_.AFT.FiniteDist Source)
    (pair : Source → _root_.AFT.FiniteDist (Color × Color))
    (body : Source → Color → Color → _root_.AFT.FiniteDist Color) (color : Color) :
    ((_root_.AFT.PhysicalBlockTensors.sharedSourceTriple source pair body).map (fun word => word 1)).weight color =
      ∑ first, (source.mix pair).weight (first, color) := by
  rw [_root_.AFT.PhysicalBlockTensors.sharedSourceTriple, _root_.AFT.FiniteDist.map_map, _root_.AFT.FiniteDist.map_weight]
  simp only [Fintype.sum_prod_type, _root_.AFT.PhysicalBlockTensors.tripleEquiv, Equiv.coe_fn_symm_mk, Fin.isValue,
    Matrix.cons_val_one, Matrix.cons_val_zero]
  change (∑ first, ∑ second, ∑ attached, if second = color then
    _root_.AFT.BlockDensity.attachedMass source pair body first second attached else 0) = _
  simp only [Finset.sum_ite_irrel, Finset.sum_const_zero, _root_.AFT.BlockDensity.attachedMass_marginal,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
open _root_.P2M8f8f5b7e renaming h2 → _p2mH2
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h0 (source : _root_.AFT.FiniteDist Source)
    (pair : Source → _root_.AFT.FiniteDist (Color × Color))
    (body : Source → Color → Color → _root_.AFT.FiniteDist Color) (color : Color) :
    ((_root_.AFT.PhysicalBlockTensors.sharedSourceTriple source pair body).map (fun word => word 2)).weight color =
      ∑ first, ∑ second, _root_.AFT.BlockDensity.attachedMass source pair body first second color := by
  rw [_root_.AFT.PhysicalBlockTensors.sharedSourceTriple, _root_.AFT.FiniteDist.map_map, _root_.AFT.FiniteDist.map_weight]
  simp only [Fintype.sum_prod_type, _root_.AFT.PhysicalBlockTensors.tripleEquiv, Equiv.coe_fn_symm_mk, Fin.isValue,
    Matrix.cons_val_two, _root_.AFT.BlockDensity.attachedLaw]
  change (∑ first, ∑ second, ∑ attached, if attached = color then
    _root_.AFT.BlockDensity.attachedMass source pair body first second attached else 0) = _
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
open _root_.P2M8f8f5b7e renaming h0 → _p2mH0
end
open _root_.P2M8f8f5b7e renaming h0 → _p2mH0
open _root_.P2M8f8f5b7e renaming h1 → _p2mH1
open _root_.P2M8f8f5b7e renaming h2 → _p2mH2
end AFT.PhysicalBlockTensors
open _root_.P2M8f8f5b7e renaming h0 → _p2mH0
open _root_.P2M8f8f5b7e renaming h1 → _p2mH1
open _root_.P2M8f8f5b7e renaming h2 → _p2mH2
end
open _root_.P2M8f8f5b7e renaming h0 → _p2mH0
open _root_.P2M8f8f5b7e renaming h1 → _p2mH1
open _root_.P2M8f8f5b7e renaming h2 → _p2mH2
namespace AFT.RepresentedPolynomial
end AFT.RepresentedPolynomial
namespace AFT.RepresentedPolynomial.inversePrimaryTable
end AFT.RepresentedPolynomial.inversePrimaryTable
namespace AFT.V7Calibration.bodyMeanOutsideInput
end AFT.V7Calibration.bodyMeanOutsideInput
namespace AFT.V7Calibration.bodyMeanSafeInput
end AFT.V7Calibration.bodyMeanSafeInput
namespace AFT.V7Calibration.bodyMeanTable
end AFT.V7Calibration.bodyMeanTable
namespace AFT.V7Calibration.extraAnchorMeanInput
end AFT.V7Calibration.extraAnchorMeanInput
namespace AFT.V7Calibration.fullBodyMeanInput
end AFT.V7Calibration.fullBodyMeanInput
namespace AFT.V7Calibration.pairMeanTable
end AFT.V7Calibration.pairMeanTable
namespace AFT.V7Calibration.rootMeanInput
end AFT.V7Calibration.rootMeanInput
section
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
variable {Color : Type*} [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h14 (reference profile : Color → ℝ) :
    _root_.AFT.RepresentedPolynomial.singleGenerating reference profile = _root_.AFT.RepresentedPolynomial.profileForm profile+
      MvPolynomial.C (∑ color,profile color)*(1-_root_.AFT.RepresentedPolynomial.profileForm reference) := by
  simp only [_root_.AFT.RepresentedPolynomial.singleGenerating,_root_.AFT.RepresentedPolynomial.centeredFactor,mul_sub,mul_add,mul_one,Finset.sum_sub_distrib,
    Finset.sum_add_distrib,← Finset.sum_mul,← map_sum,_root_.AFT.RepresentedPolynomial.profileForm_apply]
  ring
open _root_.P2M8f8f5b7e renaming h14 → _p2mH14
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h16 (reference profile : Color → ℝ) (hmass : ∑ color,profile color = 0) :
    _root_.AFT.RepresentedPolynomial.singleGenerating reference profile = _root_.AFT.RepresentedPolynomial.profileForm profile := by
  rw [_p2mH14,hmass,map_zero,zero_mul,add_zero]
open _root_.P2M8f8f5b7e renaming h16 → _p2mH16
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h15 (reference profile : Color → ℝ) (hmass : ∑ color,profile color = 1) :
    _root_.AFT.RepresentedPolynomial.singleGenerating reference profile = 1+_root_.AFT.RepresentedPolynomial.profileForm (profile-reference) := by
  rw [_p2mH14,hmass,map_one,one_mul,map_sub]
  ring
open _root_.P2M8f8f5b7e renaming h15 → _p2mH15
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h4 (first second : Color → Color → ℝ) :
    _root_.AFT.RepresentedPolynomial.pairForm (first+second) = _root_.AFT.RepresentedPolynomial.pairForm first+_root_.AFT.RepresentedPolynomial.pairForm second := by
  simp only [_root_.AFT.RepresentedPolynomial.pairForm,Pi.add_apply,map_add,add_mul,Finset.sum_add_distrib]
open _root_.P2M8f8f5b7e renaming h4 → _p2mH4
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h7 (first second : Color → Color → ℝ) :
    _root_.AFT.RepresentedPolynomial.pairForm (first-second) = _root_.AFT.RepresentedPolynomial.pairForm first-_root_.AFT.RepresentedPolynomial.pairForm second := by
  simp only [_root_.AFT.RepresentedPolynomial.pairForm,Pi.sub_apply,map_sub,sub_mul,Finset.sum_sub_distrib]
open _root_.P2M8f8f5b7e renaming h7 → _p2mH7
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h6 (scalar : ℝ) (mass : Color → Color → ℝ) :
    _root_.AFT.RepresentedPolynomial.pairForm (scalar • mass) = MvPolynomial.C scalar*_root_.AFT.RepresentedPolynomial.pairForm mass := by
  simp only [_root_.AFT.RepresentedPolynomial.pairForm,Pi.smul_apply,smul_eq_mul,map_mul,Finset.mul_sum,mul_assoc]
open _root_.P2M8f8f5b7e renaming h6 → _p2mH6
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h8 (first second : Color → ℝ) :
    _root_.AFT.RepresentedPolynomial.pairForm (fun a b => first a*second b) = _root_.AFT.RepresentedPolynomial.profileForm first*_root_.AFT.RepresentedPolynomial.profileForm second := by
  simp only [_root_.AFT.RepresentedPolynomial.pairForm,_root_.AFT.RepresentedPolynomial.profileForm_apply,map_mul]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring
open _root_.P2M8f8f5b7e renaming h8 → _p2mH8
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h5 (reference : Color → ℝ) (mass : Color → Color → ℝ) :
    _root_.AFT.RepresentedPolynomial.pairForm (_root_.AFT.SafePair.canonicalPair reference mass) = _root_.AFT.RepresentedPolynomial.pairForm mass-
      _root_.AFT.RepresentedPolynomial.profileForm reference*_root_.AFT.RepresentedPolynomial.profileForm (fun b => ∑ a,mass a b)-
      _root_.AFT.RepresentedPolynomial.profileForm (fun a => ∑ b,mass a b)*_root_.AFT.RepresentedPolynomial.profileForm reference+
      MvPolynomial.C (∑ a,∑ b,mass a b)*_root_.AFT.RepresentedPolynomial.profileForm reference^2 := by
  have heq : _root_.AFT.SafePair.canonicalPair reference mass = mass-
      (fun a b => reference a*(∑ x,mass x b))-
      (fun a b => (∑ y,mass a y)*reference b)+
      (∑ x,∑ y,mass x y) • (fun a b => reference a*reference b) := by
    funext a b
    simp only [_root_.AFT.SafePair.canonicalPair,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [heq,_p2mH4,_p2mH7,_p2mH7,_p2mH6]
  simp only [_p2mH8,pow_two]
open _root_.P2M8f8f5b7e renaming h5 → _p2mH5
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h10 (reference : Color → ℝ) (mass : Color → Color → ℝ) :
    _root_.AFT.RepresentedPolynomial.pairGenerating reference mass = _root_.AFT.RepresentedPolynomial.pairForm mass+
      _root_.AFT.RepresentedPolynomial.profileForm (fun a => ∑ b,mass a b)*(1-_root_.AFT.RepresentedPolynomial.profileForm reference)+
      _root_.AFT.RepresentedPolynomial.profileForm (fun b => ∑ a,mass a b)*(1-_root_.AFT.RepresentedPolynomial.profileForm reference)+
      MvPolynomial.C (∑ a,∑ b,mass a b)*(1-_root_.AFT.RepresentedPolynomial.profileForm reference)^2 := by
  let T : MvPolynomial Color ℝ := 1-_root_.AFT.RepresentedPolynomial.profileForm reference
  have hf (color : Color) : _root_.AFT.RepresentedPolynomial.centeredFactor reference color = MvPolynomial.X color+T := by
    unfold _root_.AFT.RepresentedPolynomial.centeredFactor T
    ring
  have hpoint (a b : Color) : MvPolynomial.C (mass a b)*(MvPolynomial.X a+T)*(MvPolynomial.X b+T) =
      MvPolynomial.C (mass a b)*MvPolynomial.X a*MvPolynomial.X b+
      MvPolynomial.C (mass a b)*MvPolynomial.X a*T+
      MvPolynomial.C (mass a b)*MvPolynomial.X b*T+MvPolynomial.C (mass a b)*T^2 := by ring
  unfold _root_.AFT.RepresentedPolynomial.pairGenerating
  simp_rw [hf,hpoint]
  simp only [Finset.sum_add_distrib]
  have hrow : (∑ a,∑ b,MvPolynomial.C (mass a b)*MvPolynomial.X a*T) =
      _root_.AFT.RepresentedPolynomial.profileForm (fun a => ∑ b,mass a b)*T := by
    simp only [_root_.AFT.RepresentedPolynomial.profileForm_apply,Finset.sum_mul,map_sum]
  have hcol : (∑ a,∑ b,MvPolynomial.C (mass a b)*MvPolynomial.X b*T) =
      _root_.AFT.RepresentedPolynomial.profileForm (fun b => ∑ a,mass a b)*T := by
    rw [Finset.sum_comm]
    simp only [_root_.AFT.RepresentedPolynomial.profileForm_apply,Finset.sum_mul,map_sum]
  have hconst : (∑ a,∑ b,MvPolynomial.C (mass a b)*T^2) =
      MvPolynomial.C (∑ a,∑ b,mass a b)*T^2 := by
    simp only [map_sum,Finset.sum_mul]
  rw [hrow,hcol,hconst]
  rfl
open _root_.P2M8f8f5b7e renaming h10 → _p2mH10
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h9 (reference : Color → ℝ) (mass : Color → Color → ℝ) :
    _root_.AFT.RepresentedPolynomial.pairGenerating reference mass = _root_.AFT.RepresentedPolynomial.pairForm (_root_.AFT.SafePair.canonicalPair reference mass)+
      _root_.AFT.RepresentedPolynomial.profileForm (fun a => (∑ b,mass a b)+(∑ b,mass b a)-
        2*(∑ x,∑ y,mass x y)*reference a)+MvPolynomial.C (∑ a,∑ b,mass a b) := by
  rw [_p2mH10,_p2mH5]
  have heq : (fun a => (∑ b,mass a b)+(∑ b,mass b a)-2*(∑ x,∑ y,mass x y)*reference a) =
      (fun a => ∑ b,mass a b)+(fun a => ∑ b,mass b a)-(2*(∑ x,∑ y,mass x y)) • reference := rfl
  rw [heq,map_sub,map_add,map_smul]
  simp only [MvPolynomial.smul_eq_C_mul,map_mul,map_ofNat]
  ring
open _root_.P2M8f8f5b7e renaming h9 → _p2mH9
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h17 (reference : Color → ℝ) (pair : Color → Color → ℝ) (single : Color → ℝ) :
    _root_.AFT.RepresentedPolynomial.tripleGenerating reference (fun a b c => pair a b*single c) =
      _root_.AFT.RepresentedPolynomial.pairGenerating reference pair*_root_.AFT.RepresentedPolynomial.singleGenerating reference single := by
  simp only [_root_.AFT.RepresentedPolynomial.tripleGenerating,_root_.AFT.RepresentedPolynomial.pairGenerating,_root_.AFT.RepresentedPolynomial.singleGenerating,map_mul]
  simp_rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring
open _root_.P2M8f8f5b7e renaming h17 → _p2mH17
end
open _root_.P2M8f8f5b7e renaming h4 → _p2mH4
open _root_.P2M8f8f5b7e renaming h5 → _p2mH5
open _root_.P2M8f8f5b7e renaming h6 → _p2mH6
open _root_.P2M8f8f5b7e renaming h7 → _p2mH7
open _root_.P2M8f8f5b7e renaming h8 → _p2mH8
open _root_.P2M8f8f5b7e renaming h9 → _p2mH9
open _root_.P2M8f8f5b7e renaming h10 → _p2mH10
open _root_.P2M8f8f5b7e renaming h14 → _p2mH14
open _root_.P2M8f8f5b7e renaming h15 → _p2mH15
open _root_.P2M8f8f5b7e renaming h16 → _p2mH16
open _root_.P2M8f8f5b7e renaming h17 → _p2mH17
end AFT.RepresentedPolynomial
open _root_.P2M8f8f5b7e renaming h4 → _p2mH4
open _root_.P2M8f8f5b7e renaming h5 → _p2mH5
open _root_.P2M8f8f5b7e renaming h6 → _p2mH6
open _root_.P2M8f8f5b7e renaming h7 → _p2mH7
open _root_.P2M8f8f5b7e renaming h8 → _p2mH8
open _root_.P2M8f8f5b7e renaming h9 → _p2mH9
open _root_.P2M8f8f5b7e renaming h10 → _p2mH10
open _root_.P2M8f8f5b7e renaming h14 → _p2mH14
open _root_.P2M8f8f5b7e renaming h15 → _p2mH15
open _root_.P2M8f8f5b7e renaming h16 → _p2mH16
open _root_.P2M8f8f5b7e renaming h17 → _p2mH17
end
open _root_.P2M8f8f5b7e renaming h4 → _p2mH4
open _root_.P2M8f8f5b7e renaming h5 → _p2mH5
open _root_.P2M8f8f5b7e renaming h6 → _p2mH6
open _root_.P2M8f8f5b7e renaming h7 → _p2mH7
open _root_.P2M8f8f5b7e renaming h8 → _p2mH8
open _root_.P2M8f8f5b7e renaming h9 → _p2mH9
open _root_.P2M8f8f5b7e renaming h10 → _p2mH10
open _root_.P2M8f8f5b7e renaming h14 → _p2mH14
open _root_.P2M8f8f5b7e renaming h15 → _p2mH15
open _root_.P2M8f8f5b7e renaming h16 → _p2mH16
open _root_.P2M8f8f5b7e renaming h17 → _p2mH17
namespace AFT.TensorChannel
end AFT.TensorChannel
namespace AFT.TensorChannel.apply
end AFT.TensorChannel.apply
namespace AFT.TensorChannel.apply.match_1
end AFT.TensorChannel.apply.match_1
section
namespace AFT.TensorChannel
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Input Output : Type*} [Fintype Input] [Fintype Output]
set_option maxRecDepth 8192
omit [Fintype Output] in
theorem _root_.P2M8f8f5b7e.h18 (law : _root_.AFT.FiniteDist Input) (kernel : Input → ℝ) :
    law.expectation (_root_.AFT.TensorChannel.center law kernel) = 0 := by
  simp only [_root_.AFT.TensorChannel.center, LinearMap.coe_mk, AddHom.coe_mk, _root_.AFT.FiniteDist.expectation_sub,
    _root_.AFT.FiniteDist.expectation_const, sub_self]
open _root_.P2M8f8f5b7e renaming h18 → AFT.TensorChannel.center_mean
open _root_.P2M8f8f5b7e renaming h18 → _p2mH18
end
open _root_.P2M8f8f5b7e renaming h18 → AFT.TensorChannel.center_mean
open _root_.P2M8f8f5b7e renaming h18 → _p2mH18
end AFT.TensorChannel
open _root_.P2M8f8f5b7e renaming h18 → AFT.TensorChannel.center_mean
open _root_.P2M8f8f5b7e renaming h18 → _p2mH18
end
open _root_.P2M8f8f5b7e renaming h18 → AFT.TensorChannel.center_mean
open _root_.P2M8f8f5b7e renaming h18 → _p2mH18
namespace AFT.Hoeffding
end AFT.Hoeffding
namespace AFT.LocalTensors.referenceExtend
end AFT.LocalTensors.referenceExtend
namespace AFT.LocalTensors.referenceRestrictedComponent
end AFT.LocalTensors.referenceRestrictedComponent
namespace AFT.MixedKernel
end AFT.MixedKernel
namespace AFT.MixedKernel.referenceProjection
end AFT.MixedKernel.referenceProjection
namespace AFT.RepresentedPolynomial.centeredFactor
end AFT.RepresentedPolynomial.centeredFactor
namespace AFT.RepresentedPolynomial.pairForm
end AFT.RepresentedPolynomial.pairForm
namespace AFT.RepresentedPolynomial.pairGenerating
end AFT.RepresentedPolynomial.pairGenerating
namespace AFT.RepresentedPolynomial.singleGenerating
end AFT.RepresentedPolynomial.singleGenerating
namespace AFT.RepresentedPolynomial.tripleForm
end AFT.RepresentedPolynomial.tripleForm
namespace AFT.RepresentedPolynomial.tripleGenerating
end AFT.RepresentedPolynomial.tripleGenerating
namespace AFT.V7Calibration.actualRootResponseCoefficient
end AFT.V7Calibration.actualRootResponseCoefficient
namespace AFT.V7Calibration.rootDefectResponseLinear
end AFT.V7Calibration.rootDefectResponseLinear
namespace AFT.V7Calibration.rootSetResponseLinear
end AFT.V7Calibration.rootSetResponseLinear
section
namespace AFT.RepresentedPolynomial
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Slot Color : Type*} [Fintype Slot] [DecidableEq Slot] [Fintype Color]
attribute [local instance] _root_.AFT.RepresentedPolynomial.referenceCoefficientSubtypeDecEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h11 (primary reference : _root_.AFT.FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (source : Color) :
    (∑ color,MvPolynomial.C (primary.weight color*_root_.AFT.MixedKernel.referenceAtom primary reference source color)*
      MvPolynomial.X color) = MvPolynomial.X source-_root_.AFT.RepresentedPolynomial.profileForm reference.weight := by
  have he (color : Color) : primary.weight color*_root_.AFT.MixedKernel.referenceAtom primary reference source color =
      (if source=color then 1 else 0)-reference.weight color := by
    rw [_root_.AFT.MixedKernel.referenceAtom_eq]
    field_simp [(hp color).ne']
  simp_rw [he]
  simp only [map_sub,sub_mul,Finset.sum_sub_distrib,_root_.AFT.RepresentedPolynomial.profileForm_apply]
  congr 1
  simp
open _root_.P2M8f8f5b7e renaming h11 → _p2mH11
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h13 (primary reference : _root_.AFT.FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (mass : (Slot → Color) → ℝ) (selected : Finset Slot) :
    _root_.AFT.RepresentedPolynomial.referenceCoefficientForm primary reference mass selected =
      ∑ source,MvPolynomial.C (mass source)*
        ∏ slot : selected,(MvPolynomial.X (source slot)-_root_.AFT.RepresentedPolynomial.profileForm reference.weight) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  unfold _root_.AFT.RepresentedPolynomial.referenceCoefficientForm _root_.AFT.LocalTensors.referenceRestrictedComponent
  simp only [Finset.sum_mul,map_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp only [map_mul,map_prod,mul_assoc]
  have he : (∑ word : selected → Color,
      (∏ slot : selected,MvPolynomial.C (_root_.AFT.MixedKernel.referenceAtom primary reference (source slot) (word slot)))*
        ((∏ slot,MvPolynomial.C (primary.weight (word slot)))*∏ slot,MvPolynomial.X (word slot))) =
      ∏ slot : selected,(MvPolynomial.X (source slot)-_root_.AFT.RepresentedPolynomial.profileForm reference.weight) := by
    simp_rw [← Finset.prod_mul_distrib]
    rw [← Fintype.prod_sum (fun slot : selected => fun color : Color =>
      MvPolynomial.C (_root_.AFT.MixedKernel.referenceAtom primary reference (source slot) color)*
        (MvPolynomial.C (primary.weight color)*MvPolynomial.X color))]
    apply Finset.prod_congr rfl
    intro slot _
    have hh := _p2mH11 primary reference hp (source slot)
    convert hh using 1
    apply Finset.sum_congr rfl
    intro color _
    rw [map_mul]
    ring
  rw [← Finset.mul_sum,he]
open _root_.P2M8f8f5b7e renaming h13 → _p2mH13
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h12 (primary reference : _root_.AFT.FiniteDist Color)
    (mass : (Slot → Color) → ℝ) :
    _root_.AFT.RepresentedPolynomial.referenceCoefficientForm primary reference mass ∅ = MvPolynomial.C (∑ source,mass source) := by
  simp [_root_.AFT.RepresentedPolynomial.referenceCoefficientForm,_root_.AFT.LocalTensors.referenceRestrictedComponent]
open _root_.P2M8f8f5b7e renaming h12 → _p2mH12
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h3 (primary reference : _root_.AFT.FiniteDist Color)
    (hp : ∀ color,0 < primary.weight color) (mass : (Slot → Color) → ℝ) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference.weight mass =
      ∑ selected : Finset Slot,_root_.AFT.RepresentedPolynomial.referenceCoefficientForm primary reference mass selected := by
  cases Subsingleton.elim (inferInstance : DecidableEq Slot) (Classical.decEq Slot)
  simp_rw [_p2mH13 primary reference hp]
  rw [Finset.sum_comm]
  simp only [_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear,LinearMap.coe_mk,AddHom.coe_mk,Algebra.smul_def,MvPolynomial.algebraMap_eq]
  change (∑ source,MvPolynomial.C (mass source)*∏ slot,_root_.AFT.RepresentedPolynomial.centeredFactor reference.weight (source slot)) = _
  apply Finset.sum_congr rfl
  intro source _
  rw [← Finset.mul_sum]
  congr 1
  have hh := Fintype.prod_add
    (fun slot => MvPolynomial.X (R := ℝ) (source slot)-_root_.AFT.RepresentedPolynomial.profileForm reference.weight)
    (fun _ : Slot => (1 : MvPolynomial Color ℝ))
  simp only [Finset.prod_const_one,mul_one] at hh
  calc
    _ = ∑ selected : Finset Slot,∏ slot ∈ selected,
        (MvPolynomial.X (source slot)-_root_.AFT.RepresentedPolynomial.profileForm reference.weight) := by
      convert hh using 1
      apply Finset.prod_congr rfl
      intro slot _
      unfold _root_.AFT.RepresentedPolynomial.centeredFactor
      ring
    _ = _ := by
      apply Finset.sum_congr rfl
      intro selected _
      exact (Finset.prod_coe_sort selected _).symm
open _root_.P2M8f8f5b7e renaming h3 → _p2mH3
end
open _root_.P2M8f8f5b7e renaming h3 → _p2mH3
open _root_.P2M8f8f5b7e renaming h11 → _p2mH11
open _root_.P2M8f8f5b7e renaming h12 → _p2mH12
open _root_.P2M8f8f5b7e renaming h13 → _p2mH13
end AFT.RepresentedPolynomial
open _root_.P2M8f8f5b7e renaming h3 → _p2mH3
open _root_.P2M8f8f5b7e renaming h11 → _p2mH11
open _root_.P2M8f8f5b7e renaming h12 → _p2mH12
open _root_.P2M8f8f5b7e renaming h13 → _p2mH13
end
open _root_.P2M8f8f5b7e renaming h3 → _p2mH3
open _root_.P2M8f8f5b7e renaming h11 → _p2mH11
open _root_.P2M8f8f5b7e renaming h12 → _p2mH12
open _root_.P2M8f8f5b7e renaming h13 → _p2mH13
namespace AFT.GaussianSource
end AFT.GaussianSource
namespace AFT.GaussianSource.windowNegate
end AFT.GaussianSource.windowNegate
namespace AFT.RootSlice
end AFT.RootSlice
namespace AFT.TrimmedSlice
end AFT.TrimmedSlice
namespace AFT.TrimmedSlice.reflectedStart
end AFT.TrimmedSlice.reflectedStart
namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.ProposalPrimary
end CurrentAFT.ProposalPrimary
namespace CurrentAFT.ProposalPrimary.anchorPrimaryLaw
end CurrentAFT.ProposalPrimary.anchorPrimaryLaw
namespace CurrentAFT.ProposalPrimary.centerProfile
end CurrentAFT.ProposalPrimary.centerProfile
namespace CurrentAFT.ProposalPrimary.finite_safe_law_weight
end CurrentAFT.ProposalPrimary.finite_safe_law_weight
section
namespace CurrentAFT.ProposalSymmetry
open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.sourceCutoff Parameters.safeMargin DiffuseProfiles.activation
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h230 (security : ℕ) (seed : _root_.CurrentAFT.DiffuseProfiles.ActualSeed security) :
    (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).weight (_root_.CurrentAFT.ProposalSymmetry.seedNegate security seed) = (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).weight seed := by
  simp only [_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw, _root_.CurrentAFT.ProposalSymmetry.seedNegate, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd, _root_.AFT.FiniteDist.prod_weight,
    _root_.CurrentAFT.DiffuseProfiles.edgeLaw, _root_.CurrentAFT.DiffuseProfiles.scalarLaw, _root_.AFT.GaussianSource.windowGaussian_reflection]
open _root_.P2M8f8f5b7e renaming h230 → _p2mH230
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h219 (security : ℕ) (seed : _root_.CurrentAFT.DiffuseProfiles.ActualSeed security) :
    _root_.CurrentAFT.DiffuseProfiles.actualBlur security (_root_.CurrentAFT.ProposalSymmetry.seedNegate security seed) = -_root_.CurrentAFT.DiffuseProfiles.actualBlur security seed := by
  simp only [_root_.CurrentAFT.DiffuseProfiles.actualBlur, _root_.CurrentAFT.ProposalSymmetry.seedNegate, Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    _root_.AFT.GaussianSource.windowNegateEquiv_val]
  ring
open _root_.P2M8f8f5b7e renaming h219 → _p2mH219
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h221 (security : ℕ) (seed : _root_.CurrentAFT.DiffuseProfiles.ActualSeed security) :
    _root_.CurrentAFT.DiffuseProfiles.actualSecond security (_root_.CurrentAFT.ProposalSymmetry.seedNegate security seed) = -_root_.CurrentAFT.DiffuseProfiles.actualSecond security seed := rfl
open _root_.P2M8f8f5b7e renaming h221 → _p2mH221
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h226 (modulus : ℕ) (color : Fin modulus) :
    (color.rev.val : ℤ) = (modulus : ℤ) - 1 - color.val := by
  simp only [Fin.val_rev]
  omega
open _root_.P2M8f8f5b7e renaming h226 → _p2mH226
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h225 (positive : Bool) (width : ℕ) (blur : ℤ) :
    _root_.CurrentAFT.DiffuseProfiles.intervalStart (!positive) width (-blur) =
      _root_.AFT.TrimmedSlice.reflectedStart (_root_.CurrentAFT.DiffuseProfiles.intervalStart positive width blur) width := by
  cases positive <;> simp only [Bool.not_false, Bool.not_true, _root_.CurrentAFT.DiffuseProfiles.intervalStart,
    Bool.false_eq_true, if_false, if_true, _root_.AFT.TrimmedSlice.reflectedStart] <;> ring
open _root_.P2M8f8f5b7e renaming h225 → _p2mH225
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h220 (security : ℕ) (positive : Bool)
    (color : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    _root_.CurrentAFT.DiffuseProfiles.actualProfile security positive color.rev = _root_.CurrentAFT.DiffuseProfiles.actualProfile security (!positive) color := by
  unfold _root_.CurrentAFT.DiffuseProfiles.actualProfile _root_.CurrentAFT.DiffuseProfiles.profile
  rw [_p2mH226]
  exact _p2mH22 _ _ _
    (fun seed => _root_.CurrentAFT.DiffuseProfiles.intervalStart positive (_root_.CurrentAFT.Parameters.anchorWidth security) (_root_.CurrentAFT.DiffuseProfiles.actualBlur security seed))
    (fun seed => _root_.CurrentAFT.DiffuseProfiles.intervalStart (!positive) (_root_.CurrentAFT.Parameters.anchorWidth security) (_root_.CurrentAFT.DiffuseProfiles.actualBlur security seed))
    (_root_.CurrentAFT.DiffuseProfiles.actualSecond security) (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).weight (_root_.CurrentAFT.ProposalSymmetry.seedNegate security)
    (_p2mH230 security) (_p2mH221 security)
    (fun seed => by rw [_p2mH219, _p2mH225]) _
open _root_.P2M8f8f5b7e renaming h220 → _p2mH220
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h229 (security : ℕ) (color : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    (_root_.CurrentAFT.ProposalPrimary.safeLaw security).weight color.rev = (_root_.CurrentAFT.ProposalPrimary.safeLaw security).weight color := by
  rw [_root_.CurrentAFT.ProposalPrimary.safeLaw, _root_.AFT.TrimmedSlice.finiteLaw_weight, _root_.AFT.TrimmedSlice.finiteLaw_weight,
    _p2mH226, _p2mH21, neg_zero]
open _root_.P2M8f8f5b7e renaming h229 → _p2mH229
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h231 (modulus : ℕ) [NeZero modulus] (shift : ℤ) :
    _root_.CurrentAFT.ProposalSymmetry.shiftColor modulus (-shift) = -_root_.CurrentAFT.ProposalSymmetry.shiftColor modulus shift := by
  simp only [_root_.CurrentAFT.ProposalSymmetry.shiftColor, Int.cast_neg, map_neg]
open _root_.P2M8f8f5b7e renaming h231 → _p2mH231
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h402 (modulus : ℕ) [NeZero modulus] (shift : ℤ) (color : Fin modulus) :
    ((ZMod.finEquiv modulus).toEquiv.trans
      ((Equiv.addRight (shift : ZMod modulus)).trans (ZMod.finEquiv modulus).toEquiv.symm)) color =
        color + _root_.CurrentAFT.ProposalSymmetry.shiftColor modulus shift := by
  apply (ZMod.finEquiv modulus).injective
  change (ZMod.finEquiv modulus)
      ((ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) color + (shift : ZMod modulus))) = _
  simp only [RingEquiv.apply_symm_apply, map_add, _root_.CurrentAFT.ProposalSymmetry.shiftColor]
open _root_.P2M8f8f5b7e renaming h402 → _p2mH402
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h232 (security : ℕ) (shift : ℤ) (color : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    _root_.CurrentAFT.ProposalPrimary.shiftEquiv security shift color = color + _root_.CurrentAFT.ProposalSymmetry.shiftColor (_root_.CurrentAFT.Parameters.modulus security) shift :=
  _p2mH402 _ _ _
open _root_.P2M8f8f5b7e renaming h232 → _p2mH232
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h234 (security : ℕ) (shift : ℤ) (color : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security shift).symm color = _root_.CurrentAFT.ProposalPrimary.shiftEquiv security (-shift) color := by
  apply (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security shift).injective
  rw [Equiv.apply_symm_apply]
  simp only [_p2mH232, _p2mH231]
  abel
open _root_.P2M8f8f5b7e renaming h234 → _p2mH234
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h233 (security : ℕ) (shift : ℤ) (color : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    _root_.CurrentAFT.ProposalPrimary.shiftEquiv security (-shift) color.rev = (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security shift color).rev := by
  simp only [_p2mH232, Fin.rev_add, _p2mH231, sub_eq_add_neg]
open _root_.P2M8f8f5b7e renaming h233 → _p2mH233
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h235 (security : ℕ) (shift : ℤ) (color : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (-shift)).symm color.rev = ((_root_.CurrentAFT.ProposalPrimary.shiftEquiv security shift).symm color).rev := by
  simp only [_p2mH234, neg_neg]
  simpa only [neg_neg] using _p2mH233 security (-shift) color
open _root_.P2M8f8f5b7e renaming h235 → _p2mH235
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h223 (security : ℕ) (includeScalar : Bool) (seed : _root_.CurrentAFT.DiffuseProfiles.ActualSeed security) :
    _root_.CurrentAFT.DiffuseProfiles.actualBlur security (_root_.CurrentAFT.ProposalSymmetry.seedNegate security seed) +
        (if includeScalar then _root_.CurrentAFT.DiffuseProfiles.actualSecond security (_root_.CurrentAFT.ProposalSymmetry.seedNegate security seed) else 0) =
      -(_root_.CurrentAFT.DiffuseProfiles.actualBlur security seed + if includeScalar then _root_.CurrentAFT.DiffuseProfiles.actualSecond security seed else 0) := by
  rw [_p2mH219, _p2mH221]
  cases includeScalar <;> simp only [Bool.false_eq_true, if_false, if_true] <;> ring
open _root_.P2M8f8f5b7e renaming h223 → _p2mH223
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h222 (security : ℕ) (includeScalar : Bool)
    (color : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    (_root_.CurrentAFT.ProposalPrimary.bodyLaw security includeScalar).weight color.rev = (_root_.CurrentAFT.ProposalPrimary.bodyLaw security includeScalar).weight color := by
  unfold _root_.CurrentAFT.ProposalPrimary.bodyLaw
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.map_equiv_weight]
  calc
    _ = ∑ seed, (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).weight (_root_.CurrentAFT.ProposalSymmetry.seedNegate security seed) *
        (_root_.CurrentAFT.ProposalPrimary.safeLaw security).weight ((_root_.CurrentAFT.ProposalPrimary.shiftEquiv security
          (_root_.CurrentAFT.DiffuseProfiles.actualBlur security (_root_.CurrentAFT.ProposalSymmetry.seedNegate security seed) +
            if includeScalar then _root_.CurrentAFT.DiffuseProfiles.actualSecond security (_root_.CurrentAFT.ProposalSymmetry.seedNegate security seed) else 0)).symm color.rev) :=
      ((_root_.CurrentAFT.ProposalSymmetry.seedNegate security).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro seed _
      rw [_p2mH230, _p2mH223, _p2mH235, _p2mH229]
open _root_.P2M8f8f5b7e renaming h222 → _p2mH222
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h224 (security : ℕ) (color : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    _root_.CurrentAFT.ProposalPrimary.diffuseMean security color.rev = _root_.CurrentAFT.ProposalPrimary.diffuseMean security color := by
  simp only [_root_.CurrentAFT.ProposalPrimary.diffuseMean, _p2mH220, Bool.not_true, Bool.not_false]
  ring
open _root_.P2M8f8f5b7e renaming h224 → _p2mH224
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h228 (security : ℕ) (color : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    _root_.CurrentAFT.ProposalPrimary.primaryProfile security color.rev = _root_.CurrentAFT.ProposalPrimary.primaryProfile security color := by
  simp only [_root_.CurrentAFT.ProposalPrimary.primaryProfile, _p2mH222, _p2mH224]
open _root_.P2M8f8f5b7e renaming h228 → _p2mH228
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h227 (security : ℕ) (color : Fin (_root_.CurrentAFT.Parameters.modulus security)) :
    (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color.rev = (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color :=
  _p2mH228 security color
open _root_.P2M8f8f5b7e renaming h227 → _p2mH227
end
open _root_.P2M8f8f5b7e renaming h219 → _p2mH219
open _root_.P2M8f8f5b7e renaming h220 → _p2mH220
open _root_.P2M8f8f5b7e renaming h221 → _p2mH221
open _root_.P2M8f8f5b7e renaming h222 → _p2mH222
open _root_.P2M8f8f5b7e renaming h223 → _p2mH223
open _root_.P2M8f8f5b7e renaming h224 → _p2mH224
open _root_.P2M8f8f5b7e renaming h225 → _p2mH225
open _root_.P2M8f8f5b7e renaming h226 → _p2mH226
open _root_.P2M8f8f5b7e renaming h227 → _p2mH227
open _root_.P2M8f8f5b7e renaming h228 → _p2mH228
open _root_.P2M8f8f5b7e renaming h229 → _p2mH229
open _root_.P2M8f8f5b7e renaming h230 → _p2mH230
open _root_.P2M8f8f5b7e renaming h231 → _p2mH231
open _root_.P2M8f8f5b7e renaming h232 → _p2mH232
open _root_.P2M8f8f5b7e renaming h233 → _p2mH233
open _root_.P2M8f8f5b7e renaming h234 → _p2mH234
open _root_.P2M8f8f5b7e renaming h235 → _p2mH235
open _root_.P2M8f8f5b7e renaming h402 → _p2mH402
end CurrentAFT.ProposalSymmetry
open _root_.P2M8f8f5b7e renaming h219 → _p2mH219
open _root_.P2M8f8f5b7e renaming h220 → _p2mH220
open _root_.P2M8f8f5b7e renaming h221 → _p2mH221
open _root_.P2M8f8f5b7e renaming h222 → _p2mH222
open _root_.P2M8f8f5b7e renaming h223 → _p2mH223
open _root_.P2M8f8f5b7e renaming h224 → _p2mH224
open _root_.P2M8f8f5b7e renaming h225 → _p2mH225
open _root_.P2M8f8f5b7e renaming h226 → _p2mH226
open _root_.P2M8f8f5b7e renaming h227 → _p2mH227
open _root_.P2M8f8f5b7e renaming h228 → _p2mH228
open _root_.P2M8f8f5b7e renaming h229 → _p2mH229
open _root_.P2M8f8f5b7e renaming h230 → _p2mH230
open _root_.P2M8f8f5b7e renaming h231 → _p2mH231
open _root_.P2M8f8f5b7e renaming h232 → _p2mH232
open _root_.P2M8f8f5b7e renaming h233 → _p2mH233
open _root_.P2M8f8f5b7e renaming h234 → _p2mH234
open _root_.P2M8f8f5b7e renaming h235 → _p2mH235
open _root_.P2M8f8f5b7e renaming h402 → _p2mH402
end
open _root_.P2M8f8f5b7e renaming h219 → _p2mH219
open _root_.P2M8f8f5b7e renaming h220 → _p2mH220
open _root_.P2M8f8f5b7e renaming h221 → _p2mH221
open _root_.P2M8f8f5b7e renaming h222 → _p2mH222
open _root_.P2M8f8f5b7e renaming h223 → _p2mH223
open _root_.P2M8f8f5b7e renaming h224 → _p2mH224
open _root_.P2M8f8f5b7e renaming h225 → _p2mH225
open _root_.P2M8f8f5b7e renaming h226 → _p2mH226
open _root_.P2M8f8f5b7e renaming h227 → _p2mH227
open _root_.P2M8f8f5b7e renaming h228 → _p2mH228
open _root_.P2M8f8f5b7e renaming h229 → _p2mH229
open _root_.P2M8f8f5b7e renaming h230 → _p2mH230
open _root_.P2M8f8f5b7e renaming h231 → _p2mH231
open _root_.P2M8f8f5b7e renaming h232 → _p2mH232
open _root_.P2M8f8f5b7e renaming h233 → _p2mH233
open _root_.P2M8f8f5b7e renaming h234 → _p2mH234
open _root_.P2M8f8f5b7e renaming h235 → _p2mH235
namespace CurrentAFT.ProposalPrimary.bodyLaw
end CurrentAFT.ProposalPrimary.bodyLaw
namespace CurrentAFT.ProposalPrimary.primaryLaw
end CurrentAFT.ProposalPrimary.primaryLaw
section
namespace CurrentAFT.FringeCertificate
open AFT DiffuseProfiles ProposalPrimary
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.bodySize Parameters.legCount Parameters.dimension Parameters.safeMargin
  DiffuseProfiles.activation centerLaw primaryProfile safeLaw bodyLaw
  FirstResponse.responseEquiv
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h126 (security : ℕ) :
    _root_.CurrentAFT.DiffuseProfiles.activation security • _root_.CurrentAFT.FirstResponse.response security
      (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * _root_.CurrentAFT.FringeCertificate.primaryCertificateDensity security color) =
        _root_.CurrentAFT.FringeCertificate.bodyDeviation security := by
  have hq := _root_.CurrentAFT.FirstResponse.modulus_pos security
  have hp (color : _root_.CurrentAFT.FringeCertificate.Palette security) : (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color ≠ 0 :=
    ne_of_gt ((by positivity : 0 < 1 / (2 * (Parameters.modulus security : ℝ))).trans_le
      (_root_.CurrentAFT.ProposalPrimary.primaryProfile_atom_lower security color))
  have hdensity : (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * _root_.CurrentAFT.FringeCertificate.primaryCertificateDensity security color) =
      _root_.CurrentAFT.FringeCertificate.primaryCertificateProfile security := by
    funext color
    simp only [_root_.CurrentAFT.FringeCertificate.primaryCertificateDensity, mul_div_cancel₀ _ (hp color)]
  rw [hdensity, _root_.CurrentAFT.FringeCertificate.primaryCertificateProfile, map_smul]
  have hinverse : _root_.CurrentAFT.FirstResponse.response security
      ((_root_.CurrentAFT.FirstResponse.responseEquiv security).symm (_root_.CurrentAFT.FringeCertificate.bodyDeviation security)) = _root_.CurrentAFT.FringeCertificate.bodyDeviation security :=
    by rw [← _root_.CurrentAFT.FirstResponse.responseEquiv_forward]; exact (_root_.CurrentAFT.FirstResponse.responseEquiv security).apply_symm_apply _
  rw [hinverse, smul_smul, mul_inv_cancel₀ (_root_.CurrentAFT.DiffuseProfiles.activation_pos security).ne', one_smul]
open _root_.P2M8f8f5b7e renaming h126 → _p2mH126
end
open _root_.P2M8f8f5b7e renaming h126 → _p2mH126
end CurrentAFT.FringeCertificate
open _root_.P2M8f8f5b7e renaming h126 → _p2mH126
end
open _root_.P2M8f8f5b7e renaming h126 → _p2mH126
namespace CurrentAFT.BodyResponse
end CurrentAFT.BodyResponse
namespace CurrentAFT.BodyResponse.jointBodyInputEnergy
end CurrentAFT.BodyResponse.jointBodyInputEnergy
namespace CurrentAFT.BodyResponse.jointBodyProfile
end CurrentAFT.BodyResponse.jointBodyProfile
namespace CurrentAFT.FringeCertificate
end CurrentAFT.FringeCertificate
namespace CurrentAFT.FringeCertificate.bodyDeviation
end CurrentAFT.FringeCertificate.bodyDeviation
namespace CurrentAFT.FringeCertificate.fringe
end CurrentAFT.FringeCertificate.fringe
namespace CurrentAFT.FringeCertificate.primaryCertificateDensity
end CurrentAFT.FringeCertificate.primaryCertificateDensity
namespace CurrentAFT.FringeCertificate.primaryCertificateProfile
end CurrentAFT.FringeCertificate.primaryCertificateProfile
namespace CurrentAFT.FringeCertificate.uniformProfile
end CurrentAFT.FringeCertificate.uniformProfile
namespace CurrentAFT.PairedResponse
end CurrentAFT.PairedResponse
namespace CurrentAFT.PairedResponse.anchorWeightedScore
end CurrentAFT.PairedResponse.anchorWeightedScore
namespace CurrentAFT.PairedResponse.compensatorScore
end CurrentAFT.PairedResponse.compensatorScore
namespace CurrentAFT.PairedResponse.pairedScore
end CurrentAFT.PairedResponse.pairedScore
namespace CurrentAFT.ProposalPrimary.anchorPrimaryMean
end CurrentAFT.ProposalPrimary.anchorPrimaryMean
namespace CurrentAFT.ProposalPrimary.centerLaw
end CurrentAFT.ProposalPrimary.centerLaw
section
namespace CurrentAFT.BackgroundCertificates
open AFT DiffuseProfiles ProposalPrimary FringeCertificate
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  Parameters.bodySize Parameters.legCount Parameters.safeMargin DiffuseProfiles.activation
  DiffuseProfiles.actualSeedLaw primaryProfile safeLaw bodyLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h40 (security : ℕ) :
    _root_.CurrentAFT.BackgroundCertificates.bodyLeadingResponse security (_root_.CurrentAFT.BackgroundCertificates.bodyCertificateDensity security) =
      (_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security).weight - (_root_.CurrentAFT.ProposalPrimary.bodyLaw security false).weight := by
  rw [_root_.CurrentAFT.BackgroundCertificates.bodyLeadingResponse, _root_.CurrentAFT.BackgroundCertificates.bodyCertificateDensity_profile]
  funext output
  rw [Pi.sub_apply, _root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw_weight, _root_.CurrentAFT.BackgroundCertificates.bodyLaw_false_weight]
  simp only [_root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile, _root_.CurrentAFT.BackgroundCertificates.bodyCertificateProfile, mul_sub, Finset.sum_sub_distrib]
open _root_.P2M8f8f5b7e renaming h40 → _p2mH40
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h41 (security : ℕ) :
    _root_.CurrentAFT.DiffuseProfiles.activation security • _root_.CurrentAFT.FirstResponse.response security
      (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * _root_.CurrentAFT.FringeCertificate.primaryCertificateDensity security color) +
      _root_.CurrentAFT.BackgroundCertificates.bodyLeadingResponse security (_root_.CurrentAFT.BackgroundCertificates.bodyCertificateDensity security) =
        (_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security).weight - _root_.CurrentAFT.FringeCertificate.uniformProfile security := by
  rw [_p2mH126, _p2mH40]
  funext output
  simp only [Pi.add_apply, Pi.sub_apply, _root_.CurrentAFT.FringeCertificate.bodyDeviation]
  ring
open _root_.P2M8f8f5b7e renaming h41 → _p2mH41
end
open _root_.P2M8f8f5b7e renaming h40 → _p2mH40
open _root_.P2M8f8f5b7e renaming h41 → _p2mH41
end CurrentAFT.BackgroundCertificates
open _root_.P2M8f8f5b7e renaming h40 → _p2mH40
open _root_.P2M8f8f5b7e renaming h41 → _p2mH41
end
open _root_.P2M8f8f5b7e renaming h40 → _p2mH40
open _root_.P2M8f8f5b7e renaming h41 → _p2mH41
namespace AFT.FiniteDist
end AFT.FiniteDist
namespace AFT.TrimmedSlice.averagedPair
end AFT.TrimmedSlice.averagedPair
namespace AFT.TrimmedSlice.mixedPair
end AFT.TrimmedSlice.mixedPair
namespace AFT.TrimmedSlice.orderedPairSlice
end AFT.TrimmedSlice.orderedPairSlice
namespace CurrentAFT.BackgroundCertificates
end CurrentAFT.BackgroundCertificates
namespace CurrentAFT.BackgroundCertificates.bodyCertificateDensity
end CurrentAFT.BackgroundCertificates.bodyCertificateDensity
namespace CurrentAFT.BackgroundCertificates.bodyCertificateProfile
end CurrentAFT.BackgroundCertificates.bodyCertificateProfile
namespace CurrentAFT.BackgroundCertificates.bodyLeadingResponse
end CurrentAFT.BackgroundCertificates.bodyLeadingResponse
namespace CurrentAFT.BackgroundCertificates.convolvedCenterLaw
end CurrentAFT.BackgroundCertificates.convolvedCenterLaw
namespace CurrentAFT.BackgroundCertificates.rootConvolutionProfile
end CurrentAFT.BackgroundCertificates.rootConvolutionProfile
namespace CurrentAFT.DiffuseProfiles
end CurrentAFT.DiffuseProfiles
namespace CurrentAFT.DiffuseProfiles.actualBlur
end CurrentAFT.DiffuseProfiles.actualBlur
namespace CurrentAFT.DiffuseProfiles.actualSeedLaw
end CurrentAFT.DiffuseProfiles.actualSeedLaw
namespace CurrentAFT.DiffuseProfiles.edgeLaw
end CurrentAFT.DiffuseProfiles.edgeLaw
namespace CurrentAFT.DiffuseProfiles.scalarLaw
end CurrentAFT.DiffuseProfiles.scalarLaw
namespace CurrentAFT.ProposalSymmetry
end CurrentAFT.ProposalSymmetry
namespace CurrentAFT.ProposalSymmetry.seedNegate
end CurrentAFT.ProposalSymmetry.seedNegate
namespace CurrentAFT.ProposalSymmetry.shiftColor
end CurrentAFT.ProposalSymmetry.shiftColor
section
namespace CurrentAFT.FirstHistogram
open AFT DiffuseProfiles ProposalPrimary PairedResponse
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  actualSeedLaw actualProfile activation primaryLaw centerLaw InwardAnchor.smoothedAnchorLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h121 (security : ℕ) (color : _root_.CurrentAFT.FirstHistogram.Palette security) :
    _root_.CurrentAFT.FirstResponse.anchorSign security color.rev = -_root_.CurrentAFT.FirstResponse.anchorSign security color := by
  have hsum : color.rev.val + color.val = _root_.CurrentAFT.Parameters.modulus security - 1 := by
    simp only [Fin.val_rev]
    omega
  by_cases hl : 2 * color.val < _root_.CurrentAFT.Parameters.modulus security - 1
  · have hrl : ¬2 * color.rev.val < _root_.CurrentAFT.Parameters.modulus security - 1 := by omega
    have hrh : _root_.CurrentAFT.Parameters.modulus security - 1 < 2 * color.rev.val := by omega
    simp only [_root_.CurrentAFT.FirstResponse.anchorSign, hl, hrl, hrh, if_true, if_false]
    ring
  · by_cases hh : _root_.CurrentAFT.Parameters.modulus security - 1 < 2 * color.val
    · have hrl : 2 * color.rev.val < _root_.CurrentAFT.Parameters.modulus security - 1 := by omega
      simp only [_root_.CurrentAFT.FirstResponse.anchorSign, hl, hh, hrl, if_false, if_true]
    · have hrl : ¬2 * color.rev.val < _root_.CurrentAFT.Parameters.modulus security - 1 := by omega
      have hrh : ¬_root_.CurrentAFT.Parameters.modulus security - 1 < 2 * color.rev.val := by omega
      simp only [_root_.CurrentAFT.FirstResponse.anchorSign, hl, hh, hrl, hrh, if_false, neg_zero]
open _root_.P2M8f8f5b7e renaming h121 → _p2mH121
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h125 (security : ℕ) :
    (∑ primary, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * _root_.CurrentAFT.FirstResponse.anchorSign security primary) = 0 := by
  have hreflection :
      (∑ primary, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * _root_.CurrentAFT.FirstResponse.anchorSign security primary) =
        -(∑ primary, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * _root_.CurrentAFT.FirstResponse.anchorSign security primary) := by
    calc
      _ = ∑ primary : _root_.CurrentAFT.FirstHistogram.Palette security, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary.rev * _root_.CurrentAFT.FirstResponse.anchorSign security primary.rev :=
        (Equiv.sum_comp (Fin.revPerm : _root_.CurrentAFT.FirstHistogram.Palette security ≃ _root_.CurrentAFT.FirstHistogram.Palette security) _).symm
      _ = _ := by simp only [_p2mH227, _p2mH121, mul_neg,
        Finset.sum_neg_distrib]
  linarith
open _root_.P2M8f8f5b7e renaming h125 → _p2mH125
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h124 (security : ℕ) (output : _root_.CurrentAFT.FirstHistogram.Palette security) :
    _root_.CurrentAFT.FirstHistogram.legFirstMean security output =
      _root_.CurrentAFT.DiffuseProfiles.activation security * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output +
        _root_.CurrentAFT.DiffuseProfiles.activation security * _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile security
          (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).weight output +
        (_root_.CurrentAFT.ProposalPrimary.bodyLaw security true).weight output + 2 * (1 - _root_.CurrentAFT.DiffuseProfiles.activation security) * _root_.CurrentAFT.ProposalPrimary.diffuseMean security output := by
  have hcompanion : (∑ primary, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * _root_.CurrentAFT.FirstHistogram.markedCompanion security primary output) =
      _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile security (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).weight output := by
    simp_rw [_root_.CurrentAFT.FirstHistogram.markedCompanion_convolution]
    rw [_root_.CurrentAFT.FirstHistogram.convolution_sum]
    rfl
  unfold _root_.CurrentAFT.FirstHistogram.legFirstMean
  simp_rw [_root_.CurrentAFT.FirstHistogram.reference_histogram]
  calc
    _ = (∑ primary,
        (_root_.CurrentAFT.DiffuseProfiles.activation security * ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * _root_.CurrentAFT.FirstHistogram.atom primary output) +
          _root_.CurrentAFT.DiffuseProfiles.activation security * ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * _root_.CurrentAFT.FirstHistogram.markedCompanion security primary output) +
          (2 * (1 - _root_.CurrentAFT.DiffuseProfiles.activation security) * _root_.CurrentAFT.ProposalPrimary.diffuseMean security output) * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary +
          _root_.CurrentAFT.DiffuseProfiles.signProfile security output *
            ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * _root_.CurrentAFT.FirstResponse.anchorSign security primary))) +
        (_root_.CurrentAFT.ProposalPrimary.bodyLaw security true).weight output := by
      congr 1
      apply Finset.sum_congr rfl
      intro primary _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, _root_.CurrentAFT.FirstHistogram.sum_atom, hcompanion,
        _root_.AFT.FiniteDist.sum_one, mul_one, _p2mH125, mul_zero, add_zero]
      ring
open _root_.P2M8f8f5b7e renaming h124 → _p2mH124
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h123 (security : ℕ) (output : _root_.CurrentAFT.FirstHistogram.Palette security) :
    (_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security).weight output =
      (1 + _root_.CurrentAFT.ProposalPrimary.compensation security) * (_root_.CurrentAFT.ProposalPrimary.bodyLaw security false).weight output -
        _root_.CurrentAFT.ProposalPrimary.compensation security * _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile security
          (_root_.CurrentAFT.ProposalPrimary.anchorPrimaryLaw security).weight output := by
  rw [_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw_weight]
  unfold _root_.CurrentAFT.ProposalPrimary.centerLaw
  change _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile security (_root_.CurrentAFT.ProposalPrimary.centerProfile security) output = _
  rw [_root_.CurrentAFT.BackgroundCertificates.bodyLaw_false_weight]
  simp only [_root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile, _root_.CurrentAFT.ProposalPrimary.centerProfile, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro seed _ <;> ring
open _root_.P2M8f8f5b7e renaming h123 → _p2mH123
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h122 (security : ℕ) (output : _root_.CurrentAFT.FirstHistogram.Palette security) :
    _root_.CurrentAFT.ProposalPrimary.freeMass security *
        ((_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security).weight output - _root_.CurrentAFT.FringeCertificate.uniformProfile security output) +
      (_root_.CurrentAFT.Parameters.modulus security : ℝ) *
        ((_root_.CurrentAFT.ProposalPrimary.bodyLaw security true).weight output - _root_.CurrentAFT.FringeCertificate.uniformProfile security output) +
      (_root_.CurrentAFT.Parameters.legCount security : ℝ) *
        (_root_.CurrentAFT.FirstHistogram.legFirstMean security output - 3 * _root_.CurrentAFT.FringeCertificate.uniformProfile security output) = 0 := by
  rw [_p2mH124, _p2mH123]
  have hmark := (_root_.CurrentAFT.ProposalPrimary.markMass_pos security).ne'
  have hfree := (_root_.CurrentAFT.ProposalPrimary.freeMass_pos security).ne'
  have hq := (_root_.CurrentAFT.FirstResponse.modulus_pos security).ne'
  simp only [_root_.CurrentAFT.ProposalPrimary.primaryLaw]
  unfold _root_.CurrentAFT.ProposalPrimary.primaryProfile _root_.CurrentAFT.ProposalPrimary.compensation _root_.CurrentAFT.FringeCertificate.uniformProfile
  field_simp [hmark, hfree, hq]
  simp only [_root_.CurrentAFT.ProposalPrimary.markMass, _root_.CurrentAFT.ProposalPrimary.freeMass, _root_.CurrentAFT.Parameters.dimension, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring
open _root_.P2M8f8f5b7e renaming h122 → _p2mH122
end
open _root_.P2M8f8f5b7e renaming h121 → _p2mH121
open _root_.P2M8f8f5b7e renaming h122 → _p2mH122
open _root_.P2M8f8f5b7e renaming h123 → _p2mH123
open _root_.P2M8f8f5b7e renaming h124 → _p2mH124
open _root_.P2M8f8f5b7e renaming h125 → _p2mH125
end CurrentAFT.FirstHistogram
open _root_.P2M8f8f5b7e renaming h121 → _p2mH121
open _root_.P2M8f8f5b7e renaming h122 → _p2mH122
open _root_.P2M8f8f5b7e renaming h123 → _p2mH123
open _root_.P2M8f8f5b7e renaming h124 → _p2mH124
open _root_.P2M8f8f5b7e renaming h125 → _p2mH125
end
open _root_.P2M8f8f5b7e renaming h121 → _p2mH121
open _root_.P2M8f8f5b7e renaming h122 → _p2mH122
open _root_.P2M8f8f5b7e renaming h123 → _p2mH123
open _root_.P2M8f8f5b7e renaming h124 → _p2mH124
open _root_.P2M8f8f5b7e renaming h125 → _p2mH125
namespace AFT.FiniteDist.expectation
end AFT.FiniteDist.expectation
namespace AFT.FiniteDist.independent
end AFT.FiniteDist.independent
namespace AFT.FiniteDist.l2Sq
end AFT.FiniteDist.l2Sq
namespace AFT.FiniteDist.mk
end AFT.FiniteDist.mk
namespace AFT.FiniteDist.normalize
end AFT.FiniteDist.normalize
namespace AFT.GaussianSource.windowGaussian
end AFT.GaussianSource.windowGaussian
namespace AFT.GaussianSource.windowNormalizer
end AFT.GaussianSource.windowNormalizer
namespace AFT.GaussianSource.windowZero
end AFT.GaussianSource.windowZero
namespace AFT.Hoeffding.centeredAtom
end AFT.Hoeffding.centeredAtom
namespace AFT.Hoeffding.densityComponent
end AFT.Hoeffding.densityComponent
namespace CurrentAFT.PublicCharge
end CurrentAFT.PublicCharge
namespace CurrentAFT.PublicCharge.assembledEndpoint
end CurrentAFT.PublicCharge.assembledEndpoint
namespace CurrentAFT.PublicCharge.assembledEndpoint.match_1
end CurrentAFT.PublicCharge.assembledEndpoint.match_1
namespace CurrentAFT.PublicCharge.cycleDifference
end CurrentAFT.PublicCharge.cycleDifference
namespace CurrentAFT.PublicCharge.legCompanion
end CurrentAFT.PublicCharge.legCompanion
namespace CurrentAFT.PublicCharge.queueIncrement
end CurrentAFT.PublicCharge.queueIncrement
namespace CurrentAFT.characterFourier
end CurrentAFT.characterFourier
namespace CurrentAFT.coordinateCharacter
end CurrentAFT.coordinateCharacter
namespace CurrentAFT.signedFourier
end CurrentAFT.signedFourier
namespace CurrentAFT.uniformDensity
end CurrentAFT.uniformDensity
namespace CurrentAFT.uniformDeviation
end CurrentAFT.uniformDeviation
section
namespace CurrentAFT.ProtectedCycle
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h238 {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (reference : Index → _root_.AFT.FiniteDist Scalar) (first second : Index) (hdistinct : second ≠ first) :
    (_root_.AFT.FiniteDist.independent reference).map (fun latent => (latent first, latent second)) =
      (reference first).prod (reference second) := by
  ext values
  have htest := _root_.CurrentAFT.ProtectedCycle.independent_pair_expectation reference first second hdistinct
    (fun firstValue secondValue => if (firstValue, secondValue) = values then 1 else 0)
  have hleft : (_root_.AFT.FiniteDist.independent reference).expectation
      (fun latent => if (latent first, latent second) = values then 1 else 0) =
      ((_root_.AFT.FiniteDist.independent reference).map
        (fun latent => (latent first, latent second))).weight values := by
    simp only [_root_.AFT.FiniteDist.expectation, _root_.AFT.FiniteDist.map_weight, mul_ite, mul_one, mul_zero]
    apply Finset.sum_congr rfl
    intro latent _
    by_cases hequal : (latent first, latent second) = values <;> simp [hequal]
  rw [hleft] at htest
  rw [htest]
  rcases values with ⟨firstValue, secondValue⟩
  simp [mul_ite, _root_.AFT.FiniteDist.prod_weight, ite_and]
open _root_.P2M8f8f5b7e renaming h238 → _p2mH238
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h236 {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : _root_.AFT.FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (vertex : Fin body)
    (hdistinct : (finRotate body).symm vertex ≠ vertex) :
    (_root_.CurrentAFT.ProtectedCycle.cycleLaw body modulus edgeLaw value).map (fun root => root vertex) =
      _root_.CurrentAFT.ProtectedCycle.differenceLaw edgeLaw value := by
  unfold _root_.CurrentAFT.ProtectedCycle.cycleLaw _root_.CurrentAFT.ProtectedCycle.differenceLaw
  rw [_root_.AFT.FiniteDist.map_map]
  have hpair := _p2mH238 (fun _ : Fin body => edgeLaw) vertex
    ((finRotate body).symm vertex) hdistinct
  rw [← hpair, _root_.AFT.FiniteDist.map_map]
  rfl
open _root_.P2M8f8f5b7e renaming h236 → _p2mH236
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h237 {Scalar : Type*} [Fintype Scalar]
    (body modulus : ℕ) [NeZero modulus] (edgeLaw : _root_.AFT.FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (hbody : 2 ≤ body) (vertex : Fin body) :
    (_root_.CurrentAFT.ProtectedCycle.cycleLaw body modulus edgeLaw value).map (fun root => root vertex) =
      _root_.CurrentAFT.ProtectedCycle.differenceLaw edgeLaw value :=
  _p2mH236 body modulus edgeLaw value vertex (_root_.CurrentAFT.ProtectedCycle.cycle_predecessor_ne body hbody vertex)
open _root_.P2M8f8f5b7e renaming h237 → _p2mH237
end
open _root_.P2M8f8f5b7e renaming h236 → _p2mH236
open _root_.P2M8f8f5b7e renaming h237 → _p2mH237
open _root_.P2M8f8f5b7e renaming h238 → _p2mH238
end CurrentAFT.ProtectedCycle
open _root_.P2M8f8f5b7e renaming h236 → _p2mH236
open _root_.P2M8f8f5b7e renaming h237 → _p2mH237
open _root_.P2M8f8f5b7e renaming h238 → _p2mH238
end
open _root_.P2M8f8f5b7e renaming h236 → _p2mH236
open _root_.P2M8f8f5b7e renaming h237 → _p2mH237
open _root_.P2M8f8f5b7e renaming h238 → _p2mH238
namespace CurrentAFT.PathLikelihood
end CurrentAFT.PathLikelihood
namespace CurrentAFT.PathLikelihood.amplitude
end CurrentAFT.PathLikelihood.amplitude
namespace CurrentAFT.PathLikelihood.amplitude.match_1
end CurrentAFT.PathLikelihood.amplitude.match_1
namespace CurrentAFT.PathLikelihood.latentLaw
end CurrentAFT.PathLikelihood.latentLaw
namespace CurrentAFT.PathLikelihood.marginal
end CurrentAFT.PathLikelihood.marginal
namespace CurrentAFT.PathLikelihood.pathKernel
end CurrentAFT.PathLikelihood.pathKernel
namespace CurrentAFT.PathLikelihood.pathKernel.match_1
end CurrentAFT.PathLikelihood.pathKernel.match_1
namespace CurrentAFT.PathLikelihood.pathLaw
end CurrentAFT.PathLikelihood.pathLaw
namespace CurrentAFT.PathLikelihood.pathOutput
end CurrentAFT.PathLikelihood.pathOutput
namespace CurrentAFT.PathLikelihood.squareSum
end CurrentAFT.PathLikelihood.squareSum
namespace CurrentAFT.PathLikelihood.transfer
end CurrentAFT.PathLikelihood.transfer
namespace CurrentAFT.ProtectedCycle
end CurrentAFT.ProtectedCycle
namespace CurrentAFT.ProtectedCycle.centeredRelabeledCycleLaw
end CurrentAFT.ProtectedCycle.centeredRelabeledCycleLaw
section
namespace CurrentAFT.CycleSelections
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h100 {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : _root_.AFT.FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : _root_.CurrentAFT.CycleSelections.Selection body order) (slot : Fin order) :
    (_root_.CurrentAFT.CycleSelections.selectedLaw body order modulus source value sites).map (fun root => root slot) =
      _root_.CurrentAFT.ProtectedCycle.differenceLaw source value := by
  rw [_root_.CurrentAFT.CycleSelections.selectedLaw, _root_.AFT.FiniteDist.map_map]
  exact _p2mH237 body modulus source value hbody (sites slot)
open _root_.P2M8f8f5b7e renaming h100 → _p2mH100
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h99 {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (horder : order ≤ body) (hbody : 2 ≤ body)
    (source : _root_.AFT.FiniteDist Scalar) (value : Scalar → ZMod modulus) (slot : Fin order) :
    (_root_.CurrentAFT.CycleSelections.averagedSelectedLaw body order modulus horder source value).map (fun root => root slot) =
      _root_.CurrentAFT.ProtectedCycle.differenceLaw source value := by
  rw [_root_.CurrentAFT.CycleSelections.averagedSelectedLaw, _root_.AFT.FiniteDist.map_mix]
  simp_rw [_p2mH100 body order modulus hbody source value]
  exact _root_.AFT.FiniteDist.mix_const _ _
open _root_.P2M8f8f5b7e renaming h99 → _p2mH99
end
open _root_.P2M8f8f5b7e renaming h99 → _p2mH99
open _root_.P2M8f8f5b7e renaming h100 → _p2mH100
end CurrentAFT.CycleSelections
open _root_.P2M8f8f5b7e renaming h99 → _p2mH99
open _root_.P2M8f8f5b7e renaming h100 → _p2mH100
end
open _root_.P2M8f8f5b7e renaming h99 → _p2mH99
open _root_.P2M8f8f5b7e renaming h100 → _p2mH100
section
namespace CurrentAFT.BackgroundTranslations
open AFT DiffuseProfiles ProposalPrimary FringeCertificate BackgroundCertificates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.bodySize
  Parameters.legCount Parameters.safeMargin DiffuseProfiles.activation DiffuseProfiles.actualSeedLaw
  primaryProfile safeLaw bodyLaw FirstResponse.responseEquiv
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h57 (security : ℕ) (shift : ℤ) :
    _root_.CurrentAFT.DiffuseProfiles.activation security • _root_.CurrentAFT.FirstResponse.response security
      (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * _root_.CurrentAFT.BackgroundTranslations.residualCertificateDensity security shift color) =
        _root_.CurrentAFT.BackgroundTranslations.translationResidual security shift := by
  rw [_root_.CurrentAFT.BackgroundTranslations.residualCertificateDensity_profile, _root_.CurrentAFT.BackgroundTranslations.residualCertificateProfile, map_smul]
  have hinverse : _root_.CurrentAFT.FirstResponse.response security
      ((_root_.CurrentAFT.FirstResponse.responseEquiv security).symm (_root_.CurrentAFT.BackgroundTranslations.translationResidual security shift)) = _root_.CurrentAFT.BackgroundTranslations.translationResidual security shift := by
    rw [← _root_.CurrentAFT.FirstResponse.responseEquiv_forward]
    exact (_root_.CurrentAFT.FirstResponse.responseEquiv security).apply_symm_apply _
  rw [hinverse, smul_smul, mul_inv_cancel₀ (_root_.CurrentAFT.DiffuseProfiles.activation_pos security).ne', one_smul]
open _root_.P2M8f8f5b7e renaming h57 → _p2mH57
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h58 (security : ℕ) (shift : ℤ) :
    _root_.CurrentAFT.DiffuseProfiles.activation security • _root_.CurrentAFT.FirstResponse.response security
      (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * _root_.CurrentAFT.FringeCertificate.primaryCertificateDensity security color) +
    _root_.CurrentAFT.BackgroundCertificates.bodyLeadingResponse security (_root_.CurrentAFT.BackgroundTranslations.safeSeedDensity security shift) +
    _root_.CurrentAFT.DiffuseProfiles.activation security • _root_.CurrentAFT.FirstResponse.response security
      (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * _root_.CurrentAFT.BackgroundTranslations.residualCertificateDensity security shift color) =
      _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile security (_root_.CurrentAFT.BackgroundTranslations.shiftedSafeLaw security shift).weight - _root_.CurrentAFT.FringeCertificate.uniformProfile security := by
  rw [_p2mH126, _p2mH57,
    _root_.CurrentAFT.BackgroundCertificates.bodyLeadingResponse, _root_.CurrentAFT.BackgroundTranslations.safeSeedDensity_profile]
  funext output
  rw [Pi.add_apply, Pi.add_apply, Pi.sub_apply]
  simp only [_root_.CurrentAFT.FringeCertificate.bodyDeviation, _root_.CurrentAFT.BackgroundTranslations.translationResidual, _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile, _root_.CurrentAFT.BackgroundTranslations.safeSeedProfile, _root_.CurrentAFT.BackgroundTranslations.projectedShiftProfile,
    mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    mul_left_comm, _root_.CurrentAFT.BackgroundCertificates.bodyLaw_false_weight]
  ring
open _root_.P2M8f8f5b7e renaming h58 → _p2mH58
end
open _root_.P2M8f8f5b7e renaming h57 → _p2mH57
open _root_.P2M8f8f5b7e renaming h58 → _p2mH58
end CurrentAFT.BackgroundTranslations
open _root_.P2M8f8f5b7e renaming h57 → _p2mH57
open _root_.P2M8f8f5b7e renaming h58 → _p2mH58
end
open _root_.P2M8f8f5b7e renaming h57 → _p2mH57
open _root_.P2M8f8f5b7e renaming h58 → _p2mH58
namespace CurrentAFT.ActualControls
end CurrentAFT.ActualControls
namespace CurrentAFT.ActualControls.bodyResidueReference
end CurrentAFT.ActualControls.bodyResidueReference
namespace CurrentAFT.ActualControls.primaryResidueReference
end CurrentAFT.ActualControls.primaryResidueReference
namespace CurrentAFT.ActualControls.safeResidueEquiv
end CurrentAFT.ActualControls.safeResidueEquiv
namespace CurrentAFT.LocalReferenceEnergy
end CurrentAFT.LocalReferenceEnergy
namespace CurrentAFT.LocalReferenceEnergy.diffusePairAt
end CurrentAFT.LocalReferenceEnergy.diffusePairAt
namespace CurrentAFT.LocalReferenceEnergy.markedCompanionAt
end CurrentAFT.LocalReferenceEnergy.markedCompanionAt
namespace CurrentAFT.ReferenceMarginals
end CurrentAFT.ReferenceMarginals
namespace CurrentAFT.ReferenceMarginals.averagedLaw_height
end CurrentAFT.ReferenceMarginals.averagedLaw_height
section
namespace CurrentAFT.ConditionalPairMean
open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse
  LocalReferenceEnergy BackgroundCertificates FringeCertificate
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h86 (security : ℕ) (primary : _root_.CurrentAFT.ConditionalPairMean.Palette security) (scalar : _root_.CurrentAFT.ConditionalPairMean.Scalar security)
    (output : _root_.CurrentAFT.ConditionalPairMean.Palette security) :
    (∑ other, (_root_.CurrentAFT.LocalReferenceEnergy.markedPairAt security primary scalar).weight (output, other)) =
      if primary = output then 1 else 0 := by
  simp only [_root_.CurrentAFT.LocalReferenceEnergy.markedPairAt, _root_.AFT.FiniteDist.map_weight, Prod.mk.injEq]
  rw [Finset.sum_comm]
  by_cases hprimary : primary = output
  · simp only [hprimary, true_and]
    simp [_root_.AFT.FiniteDist.sum_one]
  · simp [hprimary]
open _root_.P2M8f8f5b7e renaming h86 → _p2mH86
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h87 (security : ℕ) (primary : _root_.CurrentAFT.ConditionalPairMean.Palette security) (scalar : _root_.CurrentAFT.ConditionalPairMean.Scalar security)
    (output : _root_.CurrentAFT.ConditionalPairMean.Palette security) :
    (∑ other, (_root_.CurrentAFT.LocalReferenceEnergy.markedPairAt security primary scalar).weight (other, output)) =
      (_root_.CurrentAFT.LocalReferenceEnergy.markedCompanionAt security primary scalar).weight output := by
  simp only [_root_.CurrentAFT.LocalReferenceEnergy.markedPairAt, _root_.AFT.FiniteDist.map_weight, Prod.mk.injEq]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single output]
  · simp
  · intro other _ hother
    apply Finset.sum_eq_zero
    intro index _
    simp [hother]
  · simp
open _root_.P2M8f8f5b7e renaming h87 → _p2mH87
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h88 (security : ℕ) (scalar : _root_.CurrentAFT.ConditionalPairMean.Scalar security) (output : _root_.CurrentAFT.ConditionalPairMean.Palette security) :
    _root_.CurrentAFT.ConditionalPairMean.pairMean security scalar output =
      ∑ primary, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary *
        ((∑ other, (_root_.CurrentAFT.LocalReferenceEnergy.pairAt security primary scalar).weight (output, other)) +
          ∑ other, (_root_.CurrentAFT.LocalReferenceEnergy.pairAt security primary scalar).weight (other, output)) := by
  simp only [_root_.CurrentAFT.LocalReferenceEnergy.pairAt, Finset.sum_add_distrib, ← Finset.mul_sum,
    _p2mH86, _p2mH87]
  unfold _root_.CurrentAFT.ConditionalPairMean.pairMean _root_.CurrentAFT.ConditionalPairMean.diffuseFirst _root_.CurrentAFT.ConditionalPairMean.diffuseSecond _root_.CurrentAFT.ConditionalPairMean.markedSecond
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.CurrentAFT.ConditionalPairMean.firstMarginal, _root_.CurrentAFT.ConditionalPairMean.secondMarginal]
  simp only [mul_add, Finset.sum_add_distrib]
  ring_nf
  simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring_nf
open _root_.P2M8f8f5b7e renaming h88 → _p2mH88
end
open _root_.P2M8f8f5b7e renaming h86 → _p2mH86
open _root_.P2M8f8f5b7e renaming h87 → _p2mH87
open _root_.P2M8f8f5b7e renaming h88 → _p2mH88
end CurrentAFT.ConditionalPairMean
open _root_.P2M8f8f5b7e renaming h86 → _p2mH86
open _root_.P2M8f8f5b7e renaming h87 → _p2mH87
open _root_.P2M8f8f5b7e renaming h88 → _p2mH88
end
open _root_.P2M8f8f5b7e renaming h86 → _p2mH86
open _root_.P2M8f8f5b7e renaming h87 → _p2mH87
open _root_.P2M8f8f5b7e renaming h88 → _p2mH88
namespace CurrentAFT.ConditionalPairMean
end CurrentAFT.ConditionalPairMean
namespace CurrentAFT.ConditionalPairMean.centeredMean
end CurrentAFT.ConditionalPairMean.centeredMean
namespace CurrentAFT.ConditionalPairMean.diffuseFirst
end CurrentAFT.ConditionalPairMean.diffuseFirst
namespace CurrentAFT.ConditionalPairMean.diffuseSecond
end CurrentAFT.ConditionalPairMean.diffuseSecond
namespace CurrentAFT.ConditionalPairMean.firstMarginal
end CurrentAFT.ConditionalPairMean.firstMarginal
namespace CurrentAFT.ConditionalPairMean.markedSecond
end CurrentAFT.ConditionalPairMean.markedSecond
namespace CurrentAFT.ConditionalPairMean.pairMean
end CurrentAFT.ConditionalPairMean.pairMean
namespace CurrentAFT.ConditionalPairMean.secondMarginal
end CurrentAFT.ConditionalPairMean.secondMarginal
namespace CurrentAFT.LocalReferenceEnergy.markedPairAt
end CurrentAFT.LocalReferenceEnergy.markedPairAt
namespace CurrentAFT.UniformBodyProfiles
end CurrentAFT.UniformBodyProfiles
namespace CurrentAFT.UniformBodyProfiles.BodyRole
end CurrentAFT.UniformBodyProfiles.BodyRole
namespace CurrentAFT.UniformBodyProfiles.BodyRole.attachment
end CurrentAFT.UniformBodyProfiles.BodyRole.attachment
namespace CurrentAFT.UniformBodyProfiles.BodyRole.free
end CurrentAFT.UniformBodyProfiles.BodyRole.free
namespace CurrentAFT.UniformBodyProfiles.BodyRole.queue
end CurrentAFT.UniformBodyProfiles.BodyRole.queue
namespace CurrentAFT.UniformBodyProfiles.preRootLaw
end CurrentAFT.UniformBodyProfiles.preRootLaw
namespace CurrentAFT.UniformBodyProfiles.preRootLaw.match_1
end CurrentAFT.UniformBodyProfiles.preRootLaw.match_1
namespace CurrentAFT.UniformBodyProfiles.uniformVector
end CurrentAFT.UniformBodyProfiles.uniformVector
section
namespace CurrentAFT.BodyRootAverages
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy FirstHistogram
  UniformBodyProfiles BackgroundCertificates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ProposalPrimary.safeLaw
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h396 {Color Group : Type*} [AddCommGroup Group]
    (equiv : Color ≃ Group) (first second : Group) (color : Color) :
    (equiv.trans ((Equiv.addRight second).trans equiv.symm))
      ((equiv.trans ((Equiv.addRight first).trans equiv.symm)) color) =
      (equiv.trans ((Equiv.addRight (first + second)).trans equiv.symm)) color := by
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  change equiv.symm ((equiv color + first) + second) = equiv.symm (equiv color + (first + second))
  rw [add_assoc]
open _root_.P2M8f8f5b7e renaming h396 → _p2mH396
set_option maxRecDepth 8192
private noncomputable def _root_.P2M8f8f5b7e.h397 (modulus : ℕ) [NeZero modulus] (shift : ℤ) :
    Fin modulus ≃ Fin modulus :=
  (ZMod.finEquiv modulus).toEquiv.trans
    ((Equiv.addRight (shift : ZMod modulus)).trans (ZMod.finEquiv modulus).toEquiv.symm)
open _root_.P2M8f8f5b7e renaming h397 → CurrentAFT.BodyRootAverages.cyclicShift
open _root_.P2M8f8f5b7e renaming h397 → _p2mH397
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h398 (modulus : ℕ) [NeZero modulus] (first second : ℤ)
    (color : Fin modulus) :
    _p2mH397 modulus second (_p2mH397 modulus first color) =
      _p2mH397 modulus (first + second) color := by
  simpa only [_p2mH397, Int.cast_add] using
    _p2mH396 (ZMod.finEquiv modulus).toEquiv (first : ZMod modulus) (second : ZMod modulus) color
open _root_.P2M8f8f5b7e renaming h398 → _p2mH398
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h84 (security : ℕ) (first second : ℤ)
    (color : _root_.CurrentAFT.LocalReferenceEnergy.Palette security) :
    _root_.CurrentAFT.ProposalPrimary.shiftEquiv security second (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security first color) =
      _root_.CurrentAFT.ProposalPrimary.shiftEquiv security (first + second) color :=
  _p2mH398 (_root_.CurrentAFT.Parameters.modulus security) first second color
open _root_.P2M8f8f5b7e renaming h84 → _p2mH84
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h85 (security : ℕ) (law : _root_.AFT.FiniteDist (_root_.CurrentAFT.LocalReferenceEnergy.Palette security))
    (first second : ℤ) :
    (law.map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security first)).map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security second) =
      law.map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (first + second)) := by
  rw [_root_.AFT.FiniteDist.map_map]
  congr 1
  funext color
  exact _p2mH84 security first second color
open _root_.P2M8f8f5b7e renaming h85 → _p2mH85
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h83 (security : ℕ) (law : _root_.AFT.FiniteDist (_root_.CurrentAFT.LocalReferenceEnergy.Palette security)) :
    _root_.CurrentAFT.BodyRootAverages.rootAverage security law = (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).mix
      (fun seed => law.map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (_root_.CurrentAFT.DiffuseProfiles.actualBlur security seed))) := by
  ext output
  simp only [_root_.CurrentAFT.BodyRootAverages.rootAverage, _root_.CurrentAFT.LocalReferenceEnergy.publicBlurLaw, _root_.CurrentAFT.DiffuseProfiles.actualSeedLaw, _root_.AFT.FiniteDist.mix_weight,
    Fintype.sum_prod_type, _root_.AFT.FiniteDist.prod_weight, _root_.AFT.FiniteDist.map_equiv_weight,
    _root_.CurrentAFT.DiffuseProfiles.actualBlur]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, _root_.AFT.FiniteDist.sum_one, one_mul]
  ring
open _root_.P2M8f8f5b7e renaming h83 → _p2mH83
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h81 (security : ℕ) :
    _root_.CurrentAFT.BodyRootAverages.rootAverage security (_root_.CurrentAFT.ProposalPrimary.centerLaw security) = _root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security :=
  _p2mH83 security (_root_.CurrentAFT.ProposalPrimary.centerLaw security)
open _root_.P2M8f8f5b7e renaming h81 → _p2mH81
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h82 {Choice : Type*} [Fintype Choice] (security : ℕ)
    (choiceLaw : _root_.AFT.FiniteDist Choice) (laws : Choice → _root_.AFT.FiniteDist (_root_.CurrentAFT.LocalReferenceEnergy.Palette security)) :
    _root_.CurrentAFT.BodyRootAverages.rootAverage security (choiceLaw.mix laws) = choiceLaw.mix (fun choice => _root_.CurrentAFT.BodyRootAverages.rootAverage security (laws choice)) := by
  ext output
  simp only [_root_.CurrentAFT.BodyRootAverages.rootAverage, _root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.map_equiv_weight]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro choice _
  apply Finset.sum_congr rfl
  intro pair _
  ring
open _root_.P2M8f8f5b7e renaming h82 → _p2mH82
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h80 (security : ℕ) :
    _root_.CurrentAFT.BodyRootAverages.rootAverage security ((_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).mix (fun scalar =>
      (_root_.CurrentAFT.ProposalPrimary.safeLaw security).map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security scalar.val))) = _root_.CurrentAFT.ProposalPrimary.bodyLaw security true := by
  ext output
  simp only [_root_.CurrentAFT.BodyRootAverages.rootAverage, _root_.CurrentAFT.LocalReferenceEnergy.publicBlurLaw, _root_.CurrentAFT.ProposalPrimary.bodyLaw, _root_.CurrentAFT.DiffuseProfiles.actualSeedLaw, _root_.AFT.FiniteDist.mix_weight,
    Fintype.sum_prod_type, _root_.AFT.FiniteDist.prod_weight, _root_.AFT.FiniteDist.map_equiv_weight,
    if_true, _root_.CurrentAFT.DiffuseProfiles.actualBlur, _root_.CurrentAFT.DiffuseProfiles.actualSecond]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro scalar _
  have hshift := congrArg (fun distribution : _root_.AFT.FiniteDist (_root_.CurrentAFT.LocalReferenceEnergy.Palette security) =>
    distribution.weight output) (_p2mH85 security (_root_.CurrentAFT.ProposalPrimary.safeLaw security)
      scalar.val (first.val - second.val))
  simp only [_root_.AFT.FiniteDist.map_equiv_weight] at hshift
  rw [add_comm scalar.val] at hshift
  rw [hshift]
  ring
open _root_.P2M8f8f5b7e renaming h80 → _p2mH80
end
open _root_.P2M8f8f5b7e renaming h80 → _p2mH80
open _root_.P2M8f8f5b7e renaming h81 → _p2mH81
open _root_.P2M8f8f5b7e renaming h82 → _p2mH82
open _root_.P2M8f8f5b7e renaming h83 → _p2mH83
open _root_.P2M8f8f5b7e renaming h84 → _p2mH84
open _root_.P2M8f8f5b7e renaming h85 → _p2mH85
open _root_.P2M8f8f5b7e renaming h396 → _p2mH396
open _root_.P2M8f8f5b7e renaming h397 → CurrentAFT.BodyRootAverages.cyclicShift
open _root_.P2M8f8f5b7e renaming h397 → _p2mH397
open _root_.P2M8f8f5b7e renaming h398 → _p2mH398
end CurrentAFT.BodyRootAverages
open _root_.P2M8f8f5b7e renaming h80 → _p2mH80
open _root_.P2M8f8f5b7e renaming h81 → _p2mH81
open _root_.P2M8f8f5b7e renaming h82 → _p2mH82
open _root_.P2M8f8f5b7e renaming h83 → _p2mH83
open _root_.P2M8f8f5b7e renaming h84 → _p2mH84
open _root_.P2M8f8f5b7e renaming h85 → _p2mH85
open _root_.P2M8f8f5b7e renaming h396 → _p2mH396
open _root_.P2M8f8f5b7e renaming h397 → CurrentAFT.BodyRootAverages.cyclicShift
open _root_.P2M8f8f5b7e renaming h397 → _p2mH397
open _root_.P2M8f8f5b7e renaming h398 → _p2mH398
end
open _root_.P2M8f8f5b7e renaming h80 → _p2mH80
open _root_.P2M8f8f5b7e renaming h81 → _p2mH81
open _root_.P2M8f8f5b7e renaming h82 → _p2mH82
open _root_.P2M8f8f5b7e renaming h83 → _p2mH83
open _root_.P2M8f8f5b7e renaming h84 → _p2mH84
open _root_.P2M8f8f5b7e renaming h85 → _p2mH85
namespace AFT.MixedKernel.centered_sum_product_zero
end AFT.MixedKernel.centered_sum_product_zero
namespace CurrentAFT.PrimaryPairInverse
end CurrentAFT.PrimaryPairInverse
namespace CurrentAFT.PrimaryPairInverse.inverseFirst
end CurrentAFT.PrimaryPairInverse.inverseFirst
namespace CurrentAFT.PrimaryPairInverse.pairCertificateProfile
end CurrentAFT.PrimaryPairInverse.pairCertificateProfile
namespace CurrentAFT.PrimaryPairInverse.pairLeading
end CurrentAFT.PrimaryPairInverse.pairLeading
section
namespace CurrentAFT.PrimaryTensorInverse
open AFT DiffuseProfiles ProposalPrimary ActualControls FirstResponse PrimaryPairInverse
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw FirstResponse.responseEquiv
attribute [local instance] _root_.CurrentAFT.PrimaryTensorInverse.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h214 (security : ℕ) (kernel : _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    _root_.CurrentAFT.PrimaryTensorInverse.densityResponse security (_root_.CurrentAFT.PrimaryTensorInverse.densityInverse security kernel) = kernel := by
  have ha := (_root_.CurrentAFT.DiffuseProfiles.activation_pos security).ne'
  have hprofile : (fun input => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight input * _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security kernel input) =
      (_root_.CurrentAFT.DiffuseProfiles.activation security)⁻¹ • (_root_.CurrentAFT.FirstResponse.responseEquiv security).symm
        (fun input => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight input * kernel input) := by
    funext input
    rw [_root_.CurrentAFT.PrimaryTensorInverse.densityInverse_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [(_root_.CurrentAFT.ActualControls.primaryReference_positive security input).ne']
  funext output
  rw [_root_.CurrentAFT.PrimaryTensorInverse.densityResponse_apply, hprofile, map_smul]
  have hinverse : _root_.CurrentAFT.FirstResponse.response security ((_root_.CurrentAFT.FirstResponse.responseEquiv security).symm
      (fun input => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight input * kernel input)) =
        fun input => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight input * kernel input := by
    rw [← _root_.CurrentAFT.FirstResponse.responseEquiv_forward]
    exact (_root_.CurrentAFT.FirstResponse.responseEquiv security).apply_symm_apply _
  rw [hinverse]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [(_root_.CurrentAFT.ActualControls.primaryReference_positive security output).ne']
open _root_.P2M8f8f5b7e renaming h214 → _p2mH214
section Composition
variable {Input Middle Output : Type*} [Fintype Input] [Fintype Middle] [Fintype Output]
set_option maxRecDepth 8192
omit [Fintype Output] in
theorem _root_.P2M8f8f5b7e.h217 (degree : ℕ)
    (first : Fin degree → (Input → ℝ) →ₗ[ℝ] (Middle → ℝ))
    (second : Fin degree → (Middle → ℝ) →ₗ[ℝ] (Output → ℝ))
    (kernel : (Fin degree → Input) → ℝ) (output : Fin degree → Output) :
    _root_.AFT.TensorChannel.apply degree second (_root_.AFT.TensorChannel.apply degree first kernel) output =
      _root_.AFT.TensorChannel.apply degree (fun index => (second index).comp (first index)) kernel output := by
  simp only [_root_.AFT.TensorChannel.apply_formula_instance, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  simp only [LinearMap.comp_apply]
  have hmatrix (index : Fin degree) :
      second index (first index (Pi.single (input index) 1)) (output index) =
        ∑ middle : Middle, first index (Pi.single (input index) 1) middle *
          second index (Pi.single middle 1) (output index) :=
    _root_.AFT.TensorChannel.channel_sum_single (second index) (first index (Pi.single (input index) 1)) (output index)
  simp only [hmatrix]
  have hfactor :
      (∑ middle : Fin degree → Middle,
        (∏ index, first index (Pi.single (input index) 1) (middle index)) *
          (∏ index, second index (Pi.single (middle index) 1) (output index))) =
        ∏ index, ∑ middle : Middle,
          first index (Pi.single (input index) 1) middle * second index (Pi.single middle 1) (output index) := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro middle _
    rw [Finset.prod_mul_distrib]
  rw [← hfactor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro middle _
  ring
open _root_.P2M8f8f5b7e renaming h217 → _p2mH217
set_option maxRecDepth 8192
omit [Fintype Input] in
theorem _root_.P2M8f8f5b7e.h218 (degree : ℕ) (kernel : (Fin degree → Input) → ℝ) (output : Fin degree → Input) :
    _root_.AFT.TensorChannel.apply degree (fun _ => LinearMap.id : Fin degree → (Input → ℝ) →ₗ[ℝ] (Input → ℝ)) kernel output =
      kernel output := by
  induction degree with
  | zero =>
    have hword : output = Fin.elim0 := Subsingleton.elim _ _
    simp only [_root_.AFT.TensorChannel.apply, hword]
  | succ degree ih =>
    change _root_.AFT.TensorChannel.apply degree (fun _ => LinearMap.id)
      (fun tail => kernel (Fin.cons (output 0) tail)) (fun index => output index.succ) = _
    rw [ih]
    congr 1
    exact Fin.cons_self_tail output
open _root_.P2M8f8f5b7e renaming h218 → _p2mH218
end Composition
open _root_.P2M8f8f5b7e renaming h217 → _p2mH217
open _root_.P2M8f8f5b7e renaming h218 → _p2mH218
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h216 (security degree : ℕ) (kernel : (Fin degree → _root_.CurrentAFT.ActualControls.Palette security) → ℝ) :
    _root_.CurrentAFT.PrimaryTensorInverse.tensorResponse security degree (_root_.CurrentAFT.PrimaryTensorInverse.tensorInverse security degree kernel) = kernel := by
  have hcomp : (_root_.CurrentAFT.PrimaryTensorInverse.densityResponse security).comp (_root_.CurrentAFT.PrimaryTensorInverse.densityInverse security) = LinearMap.id := by
    apply LinearMap.ext
    intro kernel
    funext color
    exact congrFun (_p2mH214 security kernel) color
  funext output
  change _root_.AFT.TensorChannel.apply degree (fun _ => _root_.CurrentAFT.PrimaryTensorInverse.densityResponse security)
    (_root_.AFT.TensorChannel.apply degree (fun _ => _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security) kernel) output = _
  rw [_p2mH217]
  simp only [hcomp]
  exact _p2mH218 degree kernel output
open _root_.P2M8f8f5b7e renaming h216 → _p2mH216
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h215 (security degree : ℕ) (profile : (Fin degree → _root_.CurrentAFT.ActualControls.Palette security) → ℝ) :
    _root_.CurrentAFT.PrimaryTensorInverse.massLeading security degree (_root_.CurrentAFT.PrimaryTensorInverse.massLift security degree profile) = profile := by
  funext word
  rw [_root_.CurrentAFT.PrimaryTensorInverse.massLeading, _root_.CurrentAFT.PrimaryTensorInverse.massLift, _p2mH216, _root_.CurrentAFT.PrimaryTensorInverse.massDensity]
  exact mul_div_cancel₀ _ (_root_.CurrentAFT.PrimaryTensorInverse.referenceWeight_pos security degree word).ne'
open _root_.P2M8f8f5b7e renaming h215 → _p2mH215
section Permutations
variable {Input Output : Type*} [Fintype Input] [Fintype Output]
end Permutations
end
open _root_.P2M8f8f5b7e renaming h214 → _p2mH214
open _root_.P2M8f8f5b7e renaming h215 → _p2mH215
open _root_.P2M8f8f5b7e renaming h216 → _p2mH216
open _root_.P2M8f8f5b7e renaming h217 → _p2mH217
open _root_.P2M8f8f5b7e renaming h218 → _p2mH218
end CurrentAFT.PrimaryTensorInverse
open _root_.P2M8f8f5b7e renaming h214 → _p2mH214
open _root_.P2M8f8f5b7e renaming h215 → _p2mH215
open _root_.P2M8f8f5b7e renaming h216 → _p2mH216
open _root_.P2M8f8f5b7e renaming h217 → _p2mH217
open _root_.P2M8f8f5b7e renaming h218 → _p2mH218
end
open _root_.P2M8f8f5b7e renaming h214 → _p2mH214
open _root_.P2M8f8f5b7e renaming h215 → _p2mH215
open _root_.P2M8f8f5b7e renaming h216 → _p2mH216
open _root_.P2M8f8f5b7e renaming h217 → _p2mH217
open _root_.P2M8f8f5b7e renaming h218 → _p2mH218
namespace CurrentAFT.BackgroundFamilies
end CurrentAFT.BackgroundFamilies
namespace CurrentAFT.BackgroundFamilies.translationCertificate
end CurrentAFT.BackgroundFamilies.translationCertificate
namespace CurrentAFT.BackgroundLinear
end CurrentAFT.BackgroundLinear
namespace CurrentAFT.BackgroundLinear.certificateNorm
end CurrentAFT.BackgroundLinear.certificateNorm
namespace CurrentAFT.BackgroundLinear.fixedQueueLinear
end CurrentAFT.BackgroundLinear.fixedQueueLinear
namespace CurrentAFT.BackgroundLinear.legLinearCertificate
end CurrentAFT.BackgroundLinear.legLinearCertificate
namespace CurrentAFT.BackgroundLinear.meanTranslation
end CurrentAFT.BackgroundLinear.meanTranslation
namespace CurrentAFT.DiffusePair
end CurrentAFT.DiffusePair
section
namespace CurrentAFT.DiffusePairBounds
open AFT AFT.TrimmedSlice AFT.SafeConvolution DiffuseProfiles ProposalPrimary
  ActualControls FirstResponse PairSmoothing DiffusePair BackgroundRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  Parameters.safeMargin ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  DiffusePair.pairProfile DiffusePair.safePairProfile DiffusePair.liftedPairProfile
  DiffusePair.rootPairLaw DiffusePair.rootPairShift
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h106 (security : ℕ) (scalar : ℤ)
    (first second : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.DiffusePair.safePairProfile security scalar first second = _root_.CurrentAFT.DiffusePair.safePairProfile security scalar second first := by
  have htranspose : (fun first second =>
      _root_.AFT.SafePair.restrictPair (_root_.CurrentAFT.DiffusePair.safeCore security) (_root_.CurrentAFT.DiffusePair.pairProfile security scalar) second first) =
      _root_.AFT.SafePair.restrictPair (_root_.CurrentAFT.DiffusePair.safeCore security) (_root_.CurrentAFT.DiffusePair.pairProfile security scalar) := by
    funext first second
    by_cases hfirst : first ∈ _root_.CurrentAFT.DiffusePair.safeCore security <;> by_cases hsecond : second ∈ _root_.CurrentAFT.DiffusePair.safeCore security <;>
      simp only [_root_.AFT.SafePair.restrictPair, hfirst, hsecond, and_self, and_true, and_false,
        if_true, if_false, _root_.CurrentAFT.DiffusePair.pairProfile_symmetric security scalar]
  unfold _root_.CurrentAFT.DiffusePair.safePairProfile _root_.AFT.SafePair.coreSeed
  rw [_root_.AFT.SafePair.canonicalPair_transpose, htranspose]
open _root_.P2M8f8f5b7e renaming h106 → _p2mH106
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h105 (security : ℕ) (scalar : ℤ) (first second : _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.DiffusePairBounds.bodyPairDensity security scalar first second = _root_.CurrentAFT.DiffusePairBounds.bodyPairDensity security scalar second first := by
  rw [_root_.CurrentAFT.DiffusePairBounds.bodyPairDensity, _root_.CurrentAFT.DiffusePairBounds.bodyPairDensity, _p2mH106, mul_comm]
open _root_.P2M8f8f5b7e renaming h105 → _p2mH105
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h104 (security : ℕ) (scalar : ℤ) (first second : _root_.CurrentAFT.ActualControls.SafePalette security) :
    (_root_.CurrentAFT.ActualControls.bodyReference security).weight first * (_root_.CurrentAFT.ActualControls.bodyReference security).weight second *
      _root_.CurrentAFT.DiffusePairBounds.bodyPairDensity security scalar first second = _root_.CurrentAFT.DiffusePair.safePairProfile security scalar first.val second.val := by
  unfold _root_.CurrentAFT.DiffusePairBounds.bodyPairDensity
  exact mul_div_cancel₀ _ (mul_ne_zero (_root_.CurrentAFT.ActualControls.bodyReference_positive security first).ne'
    (_root_.CurrentAFT.ActualControls.bodyReference_positive security second).ne')
open _root_.P2M8f8f5b7e renaming h104 → _p2mH104
end
open _root_.P2M8f8f5b7e renaming h104 → _p2mH104
open _root_.P2M8f8f5b7e renaming h105 → _p2mH105
open _root_.P2M8f8f5b7e renaming h106 → _p2mH106
end CurrentAFT.DiffusePairBounds
open _root_.P2M8f8f5b7e renaming h104 → _p2mH104
open _root_.P2M8f8f5b7e renaming h105 → _p2mH105
open _root_.P2M8f8f5b7e renaming h106 → _p2mH106
end
open _root_.P2M8f8f5b7e renaming h104 → _p2mH104
open _root_.P2M8f8f5b7e renaming h105 → _p2mH105
open _root_.P2M8f8f5b7e renaming h106 → _p2mH106
namespace CurrentAFT.BackgroundFamilies.bodyArity
end CurrentAFT.BackgroundFamilies.bodyArity
namespace CurrentAFT.BackgroundFamilies.bodyCoefficient
end CurrentAFT.BackgroundFamilies.bodyCoefficient
namespace CurrentAFT.BackgroundFamilies.bodyFamily
end CurrentAFT.BackgroundFamilies.bodyFamily
namespace CurrentAFT.BackgroundFamilies.bodyKernel
end CurrentAFT.BackgroundFamilies.bodyKernel
namespace CurrentAFT.BackgroundFamilies.freeCertificate
end CurrentAFT.BackgroundFamilies.freeCertificate
namespace CurrentAFT.BackgroundFamilies.primaryArity
end CurrentAFT.BackgroundFamilies.primaryArity
namespace CurrentAFT.BackgroundFamilies.primaryCoefficient
end CurrentAFT.BackgroundFamilies.primaryCoefficient
namespace CurrentAFT.BackgroundFamilies.primaryFamily
end CurrentAFT.BackgroundFamilies.primaryFamily
namespace CurrentAFT.BackgroundFamilies.primaryKernel
end CurrentAFT.BackgroundFamilies.primaryKernel
namespace CurrentAFT.MarkedPairSeed
end CurrentAFT.MarkedPairSeed
namespace CurrentAFT.MarkedPairSeed.secondCentered
end CurrentAFT.MarkedPairSeed.secondCentered
namespace CurrentAFT.MarkedPairSeed.seedDensity
end CurrentAFT.MarkedPairSeed.seedDensity
section
namespace CurrentAFT.MarkedPairCertificates
open AFT ControlCoordinates ControlNorm GradedControlAlgebra GradedControlNorm
  DiffuseProfiles ProposalPrimary ActualControls FirstResponse PrimaryTensorInverse
  BackgroundRates BackgroundFamilies MarkedPairSeed
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth ProposalPrimary.primaryLaw ActualControls.bodyReference
  BackgroundRates.primaryFactor BackgroundRates.bodyFactor MarkedPairSeed.seedDensity
attribute [local instance] _root_.CurrentAFT.MarkedPairCertificates.classicalFinDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h157 (security : ℕ) (scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security) (center : _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.PrimaryTensorInverse.densityResponse security (fun primary => _root_.CurrentAFT.MarkedPairCertificates.inverseDensity security scalar primary center) =
      fun primary => _root_.CurrentAFT.MarkedPairSeed.seedDensity security scalar primary center := _p2mH214 security _
open _root_.P2M8f8f5b7e renaming h157 → _p2mH157
end
open _root_.P2M8f8f5b7e renaming h157 → _p2mH157
end CurrentAFT.MarkedPairCertificates
open _root_.P2M8f8f5b7e renaming h157 → _p2mH157
end
open _root_.P2M8f8f5b7e renaming h157 → _p2mH157
namespace AFT.BlockDensity
end AFT.BlockDensity
namespace AFT.BlockDensity.pairEnergy
end AFT.BlockDensity.pairEnergy
namespace AFT.BlockDensity.tripleEnergy
end AFT.BlockDensity.tripleEnergy
namespace CurrentAFT.LocalReferenceEnergy.attachmentAt
end CurrentAFT.LocalReferenceEnergy.attachmentAt
namespace CurrentAFT.LocalReferenceEnergy.averagedPair_height
end CurrentAFT.LocalReferenceEnergy.averagedPair_height
namespace CurrentAFT.LocalReferenceEnergy.pairAt
end CurrentAFT.LocalReferenceEnergy.pairAt
namespace CurrentAFT.LocalReferenceEnergy.uniformReference
end CurrentAFT.LocalReferenceEnergy.uniformReference
namespace CurrentAFT.MarkedPairCertificates
end CurrentAFT.MarkedPairCertificates
namespace CurrentAFT.MarkedPairCertificates.inverseDensity
end CurrentAFT.MarkedPairCertificates.inverseDensity
namespace CurrentAFT.MarkedPairCertificates.markedMixedCertificate
end CurrentAFT.MarkedPairCertificates.markedMixedCertificate
namespace CurrentAFT.MarkedPairCertificates.mixedArity
end CurrentAFT.MarkedPairCertificates.mixedArity
namespace CurrentAFT.MarkedPairCertificates.mixedKernel
end CurrentAFT.MarkedPairCertificates.mixedKernel
section
namespace CurrentAFT.MarkedPairLeading
open AFT AFT.SafePair DiffuseProfiles ProposalPrimary ActualControls FirstResponse FringeCertificate
  BackgroundCertificates BackgroundTranslations MarkedPairSeed MarkedPairCertificates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ActualControls.bodyReference InwardAnchor.shiftedAnchorLaw DiffuseProfiles.actualSeedLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h162 (security : ℕ) (scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security) (center : _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.MarkedPairSeed.secondMean security scalar center =
      (_root_.CurrentAFT.MarkedPairLeading.anchorMean security scalar).weight center.val / (_root_.CurrentAFT.ActualControls.bodyReference security).weight center - 1 := by
  unfold _root_.CurrentAFT.MarkedPairSeed.secondMean _root_.AFT.FiniteDist.expectation _root_.CurrentAFT.MarkedPairSeed.secondCentered _root_.CurrentAFT.MarkedPairSeed.rawDensity
  simp only [mul_sub, ← mul_div_assoc, Finset.sum_sub_distrib, ← Finset.sum_div, mul_one, _root_.AFT.FiniteDist.sum_one]
  rfl
open _root_.P2M8f8f5b7e renaming h162 → _p2mH162
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h163 (security : ℕ) (scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security)
    (primary : _root_.CurrentAFT.ActualControls.Palette security) (center : _root_.CurrentAFT.ActualControls.SafePalette security) :
    (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * (_root_.CurrentAFT.ActualControls.bodyReference security).weight center * _root_.CurrentAFT.MarkedPairSeed.seedDensity security scalar primary center =
      _root_.CurrentAFT.MarkedPairLeading.seedProfile security scalar primary center.val := by
  rw [_root_.CurrentAFT.MarkedPairSeed.seedDensity, _p2mH162]
  unfold _root_.CurrentAFT.MarkedPairSeed.secondCentered _root_.CurrentAFT.MarkedPairSeed.rawDensity _root_.CurrentAFT.MarkedPairSeed.uniformRelative _root_.CurrentAFT.MarkedPairLeading.seedProfile
  have hanchor : (_root_.CurrentAFT.MarkedPairSeed.fixedAnchor security scalar primary).weight center = (_root_.CurrentAFT.MarkedPairLeading.paletteAnchor security scalar primary).weight center.val := rfl
  have hbody : (_root_.CurrentAFT.ActualControls.bodyReference security).weight center = (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight center.val := by
    simp only [_root_.CurrentAFT.ActualControls.bodyReference, _root_.CurrentAFT.ActualControls.supportedLaw]
  rw [hanchor, ← hbody]
  field_simp [(_root_.CurrentAFT.ActualControls.primaryReference_positive security primary).ne', (_root_.CurrentAFT.ActualControls.bodyReference_positive security center).ne']
  ring
open _root_.P2M8f8f5b7e renaming h163 → _p2mH163
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h164 (security : ℕ) (scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security)
    (primary center : _root_.CurrentAFT.ActualControls.Palette security) (hunsafe : ¬_root_.CurrentAFT.InwardAnchor.SafeColor security center) :
    _root_.CurrentAFT.MarkedPairLeading.seedProfile security scalar primary center = 0 := by
  have hanchor (color : _root_.CurrentAFT.ActualControls.Palette security) :
      (_root_.CurrentAFT.MarkedPairLeading.paletteAnchor security scalar color).weight center = 0 :=
    _root_.CurrentAFT.InwardAnchor.shiftedAnchorLaw_zero_outside security color _ _ center hunsafe
  have hmean : (_root_.CurrentAFT.MarkedPairLeading.anchorMean security scalar).weight center = 0 := by
    simp only [_root_.CurrentAFT.MarkedPairLeading.anchorMean, _root_.AFT.FiniteDist.mix_weight, hanchor, mul_zero, Finset.sum_const_zero]
  have hbody : (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight center = 0 := by
    simp only [_root_.CurrentAFT.ProposalPrimary.centerLaw]
    exact _root_.CurrentAFT.ProposalPrimary.centerProfile_zero_outside security center hunsafe
  simp only [_root_.CurrentAFT.MarkedPairLeading.seedProfile, hanchor, hmean, hbody, mul_zero, sub_self, add_zero]
open _root_.P2M8f8f5b7e renaming h164 → _p2mH164
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h158 (security : ℕ) (profile : _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    (∑ output, _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security profile output) = ∑ color, profile color :=
  _root_.CurrentAFT.BackgroundTranslations.rootConvolutionProfile_mass security profile
open _root_.P2M8f8f5b7e renaming h158 → _p2mH158
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h159 (security : ℕ) (scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security)
    (primary output : _root_.CurrentAFT.ActualControls.Palette security) :
    (_root_.CurrentAFT.LocalReferenceEnergy.markedCompanionAt security primary scalar).weight output =
      _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.MarkedPairLeading.paletteAnchor security scalar primary).weight output := by
  unfold _root_.CurrentAFT.LocalReferenceEnergy.markedCompanionAt _root_.CurrentAFT.LocalReferenceEnergy.publicBlurLaw
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.map_equiv_weight]
  change ((_root_.CurrentAFT.DiffuseProfiles.edgeLaw security).prod (_root_.CurrentAFT.DiffuseProfiles.edgeLaw security)).expectation
    (fun edge => (_root_.CurrentAFT.MarkedPairLeading.paletteAnchor security scalar primary).weight
      ((_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (edge.1.val - edge.2.val)).symm output)) = _
  unfold _root_.CurrentAFT.MarkedPairLeading.bodyConvolution
  change _ = (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).expectation (fun seed =>
    (_root_.CurrentAFT.MarkedPairLeading.paletteAnchor security scalar primary).weight ((_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (_root_.CurrentAFT.DiffuseProfiles.actualBlur security seed)).symm output))
  simp only [_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw, _root_.AFT.FiniteDist.expectation_prod, _root_.CurrentAFT.DiffuseProfiles.actualBlur, _root_.AFT.FiniteDist.expectation_const]
open _root_.P2M8f8f5b7e renaming h159 → _p2mH159
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h161 {Color : Type*} [Fintype Color]
    (primary body uniform : _root_.AFT.FiniteDist Color) (anchor : Color → _root_.AFT.FiniteDist Color)
    (operator : Module.End ℝ (Color → ℝ))
    (hmass : ∀ profile, (∑ color, operator profile color) = ∑ color, profile color) :
    _root_.AFT.SafePair.canonicalPair uniform.weight (fun first second => primary.weight first * operator (anchor first).weight second) =
      fun first second => operator (_root_.CurrentAFT.MarkedPairLeading.mixedSeedProfile primary body uniform anchor first) second +
        (primary.weight first - uniform.weight first) * (operator body.weight second - uniform.weight second) := by
  have hrow (first : Color) : (∑ second, primary.weight first * operator (anchor first).weight second) = primary.weight first := by
    rw [← Finset.mul_sum, hmass, _root_.AFT.FiniteDist.sum_one, mul_one]
  have hmean : (primary.mix anchor).weight = ∑ first, primary.weight first • (anchor first).weight := by
    funext second
    simp only [_root_.AFT.FiniteDist.mix_weight, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hcolumn (second : Color) : (∑ first, primary.weight first * operator (anchor first).weight second) =
      operator (primary.mix anchor).weight second := by
    rw [hmean, map_sum]
    simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hseed (first : Color) : _root_.CurrentAFT.MarkedPairLeading.mixedSeedProfile primary body uniform anchor first =
      primary.weight first • (anchor first).weight - uniform.weight first • (primary.mix anchor).weight -
        primary.weight first • body.weight + uniform.weight first • body.weight := by
    funext second
    rfl
  funext first second
  simp only [_root_.AFT.SafePair.canonicalPair, hrow, hcolumn, _root_.AFT.FiniteDist.sum_one, one_mul]
  rw [hseed, map_add, map_sub, map_sub, map_smul, map_smul, map_smul, map_smul]
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring
open _root_.P2M8f8f5b7e renaming h161 → _p2mH161
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h160 (security : ℕ) (scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security) :
    _root_.AFT.SafePair.canonicalPair (_root_.CurrentAFT.FringeCertificate.uniformProfile security) (fun primary output =>
      (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * (_root_.CurrentAFT.LocalReferenceEnergy.markedCompanionAt security primary scalar).weight output) =
      fun primary output => _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.MarkedPairLeading.seedProfile security scalar primary) output +
        ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary - _root_.CurrentAFT.FringeCertificate.uniformProfile security primary) *
          ((_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security).weight output - _root_.CurrentAFT.FringeCertificate.uniformProfile security output) := by
  let uniform : _root_.AFT.FiniteDist (_root_.CurrentAFT.ActualControls.Palette security) := _root_.AFT.FiniteDist.uniform _
  have huniform : uniform.weight = _root_.CurrentAFT.FringeCertificate.uniformProfile security := by
    funext color
    simp only [uniform, _root_.AFT.FiniteDist.uniform_weight, Fintype.card_fin, _root_.CurrentAFT.FringeCertificate.uniformProfile]
  have hseed (primary : _root_.CurrentAFT.ActualControls.Palette security) :
      _root_.CurrentAFT.MarkedPairLeading.mixedSeedProfile (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ProposalPrimary.centerLaw security) uniform (_root_.CurrentAFT.MarkedPairLeading.paletteAnchor security scalar) primary =
        _root_.CurrentAFT.MarkedPairLeading.seedProfile security scalar primary := by
    funext center
    simp only [_root_.CurrentAFT.MarkedPairLeading.mixedSeedProfile, _root_.CurrentAFT.MarkedPairLeading.seedProfile, huniform, _root_.CurrentAFT.MarkedPairLeading.anchorMean]
  have hbody : _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight = (_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security).weight := by
    funext output
    exact (_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw_weight security output).symm
  have h := _p2mH161 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ProposalPrimary.centerLaw security) uniform (_root_.CurrentAFT.MarkedPairLeading.paletteAnchor security scalar)
    (_root_.CurrentAFT.MarkedPairLeading.bodyConvolution security) (_p2mH158 security)
  simp only [huniform, hseed, hbody] at h
  simpa only [_p2mH159] using h
open _root_.P2M8f8f5b7e renaming h160 → _p2mH160
end
open _root_.P2M8f8f5b7e renaming h158 → _p2mH158
open _root_.P2M8f8f5b7e renaming h159 → _p2mH159
open _root_.P2M8f8f5b7e renaming h160 → _p2mH160
open _root_.P2M8f8f5b7e renaming h161 → _p2mH161
open _root_.P2M8f8f5b7e renaming h162 → _p2mH162
open _root_.P2M8f8f5b7e renaming h163 → _p2mH163
open _root_.P2M8f8f5b7e renaming h164 → _p2mH164
end CurrentAFT.MarkedPairLeading
open _root_.P2M8f8f5b7e renaming h158 → _p2mH158
open _root_.P2M8f8f5b7e renaming h159 → _p2mH159
open _root_.P2M8f8f5b7e renaming h160 → _p2mH160
open _root_.P2M8f8f5b7e renaming h161 → _p2mH161
open _root_.P2M8f8f5b7e renaming h162 → _p2mH162
open _root_.P2M8f8f5b7e renaming h163 → _p2mH163
open _root_.P2M8f8f5b7e renaming h164 → _p2mH164
end
open _root_.P2M8f8f5b7e renaming h158 → _p2mH158
open _root_.P2M8f8f5b7e renaming h159 → _p2mH159
open _root_.P2M8f8f5b7e renaming h160 → _p2mH160
open _root_.P2M8f8f5b7e renaming h161 → _p2mH161
open _root_.P2M8f8f5b7e renaming h162 → _p2mH162
open _root_.P2M8f8f5b7e renaming h163 → _p2mH163
open _root_.P2M8f8f5b7e renaming h164 → _p2mH164
namespace CurrentAFT.DiffusePairBounds
end CurrentAFT.DiffusePairBounds
namespace CurrentAFT.DiffusePairBounds.bodyPairDensity
end CurrentAFT.DiffusePairBounds.bodyPairDensity
namespace CurrentAFT.PairReindex
end CurrentAFT.PairReindex
namespace CurrentAFT.PairReindex.liftPair
end CurrentAFT.PairReindex.liftPair
section
namespace CurrentAFT.DiffusePairResidual
open AFT AFT.TrimmedSlice AFT.SafePair AFT.SafeConvolution
  DiffuseProfiles ProposalPrimary FirstResponse ActualControls PairSmoothing
  DiffusePair DiffusePairBounds PairReindex
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  Parameters.safeMargin ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  DiffusePair.pairProfile DiffusePair.safePairProfile DiffusePair.liftedPairProfile
  DiffusePair.rootPairLaw DiffusePair.rootPairShift DiffusePair.pairSeedLaw DiffusePair.pairStart
  DiffuseProfiles.actualSeedLaw DiffuseProfiles.edgeLaw DiffuseProfiles.scalarLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h115 (security : ℕ) (scalar : ℤ) :
    _root_.AFT.SafeConvolution.convolution (_root_.CurrentAFT.DiffusePairResidual.rootResiduePairLaw security).weight (_root_.CurrentAFT.DiffusePairResidual.seedProfile security scalar) +
      _root_.CurrentAFT.DiffusePairResidual.residualProfile security scalar = _root_.AFT.SafeConvolution.uniformCanonical (_root_.CurrentAFT.DiffusePairResidual.originalProfile security scalar) := by
  unfold _root_.CurrentAFT.DiffusePairResidual.residualProfile
  abel
open _root_.P2M8f8f5b7e renaming h115 → _p2mH115
end
open _root_.P2M8f8f5b7e renaming h115 → _p2mH115
end CurrentAFT.DiffusePairResidual
open _root_.P2M8f8f5b7e renaming h115 → _p2mH115
end
open _root_.P2M8f8f5b7e renaming h115 → _p2mH115
namespace AFT.SafePair
end AFT.SafePair
namespace AFT.SafePair.pairCountingL2
end AFT.SafePair.pairCountingL2
namespace CurrentAFT.DiffusePair.pairProfile
end CurrentAFT.DiffusePair.pairProfile
namespace CurrentAFT.DiffusePair.safeCore
end CurrentAFT.DiffusePair.safeCore
namespace CurrentAFT.DiffusePair.safePairProfile
end CurrentAFT.DiffusePair.safePairProfile
namespace CurrentAFT.DiffusePairResidual
end CurrentAFT.DiffusePairResidual
namespace CurrentAFT.DiffusePairResidual.residueCore
end CurrentAFT.DiffusePairResidual.residueCore
section
namespace CurrentAFT.DiffusePairResidualRates
open AFT AFT.TrimmedSlice AFT.SafePair AFT.SafeConvolution
  DiffuseProfiles ProposalPrimary FirstResponse ActualControls PairSmoothing
  DiffusePair DiffusePairBounds DiffusePairResidual
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  Parameters.safeMargin ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ActualControls.bodyReference
  DiffusePair.pairProfile DiffusePair.safePairProfile DiffusePair.liftedPairProfile
  DiffusePair.rootPairLaw DiffusePair.rootPairShift
  DiffusePairResidual.originalProfile DiffusePairResidual.restrictedProfile DiffusePairResidual.seedProfile
  DiffusePairResidual.residualProfile DiffusePairResidual.rootResiduePairLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h116 (modulus : ℕ) [NeZero modulus]
    (first second : ZMod modulus × ZMod modulus → ℝ) (left right : Fin modulus) :
    _root_.CurrentAFT.DiffusePairResidualRates.pullbackPair modulus (first + second) left right =
      _root_.CurrentAFT.DiffusePairResidualRates.pullbackPair modulus first left right + _root_.CurrentAFT.DiffusePairResidualRates.pullbackPair modulus second left right := rfl
open _root_.P2M8f8f5b7e renaming h116 → _p2mH116
end
open _root_.P2M8f8f5b7e renaming h116 → _p2mH116
end CurrentAFT.DiffusePairResidualRates
open _root_.P2M8f8f5b7e renaming h116 → _p2mH116
end
open _root_.P2M8f8f5b7e renaming h116 → _p2mH116
section
namespace CurrentAFT.PairCertificateFamilies
open AFT ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm
  GradedControlStability DiffuseProfiles ProposalPrimary ActualControls
  BackgroundCertificates BackgroundRates BackgroundFamilies DiffusePair DiffusePairBounds
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ProposalPrimary.centerLaw
  ActualControls.bodyReference DiffusePairBounds.bodyPairDensity BackgroundRates.bodyFactor
attribute [local instance] _root_.CurrentAFT.PairCertificateFamilies.classicalFinDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
omit [Fintype Primary] [Fintype Body] in
theorem _root_.P2M8f8f5b7e.h187 (density : Body → Body → ℝ)
    (hsymmetric : ∀ first second, density first second = density second first) :
    _root_.CurrentAFT.ControlCoordinates.SeparatelySymmetric (_root_.CurrentAFT.PairCertificateFamilies.pairBodyRaw (Primary := Primary) density) := by
  intro primaryOrder bodyOrder colors centers
  have hne : (bodyOrder 0).val ≠ (bodyOrder 1).val := by
    intro hequal
    have h := bodyOrder.injective (Fin.ext hequal)
    have hv := congrArg Fin.val h
    norm_num at hv
  have hzero := (bodyOrder 0).isLt
  have hone := (bodyOrder 1).isLt
  have hcases : ((bodyOrder 0).val = 0 ∧ (bodyOrder 1).val = 1) ∨
      ((bodyOrder 0).val = 1 ∧ (bodyOrder 1).val = 0) := by omega
  rcases hcases with hcases | hcases
  · have h0 : bodyOrder 0 = 0 := Fin.ext hcases.1
    have h1 : bodyOrder 1 = 1 := Fin.ext hcases.2
    simp only [_root_.CurrentAFT.PairCertificateFamilies.pairBodyRaw, Function.comp_apply, h0, h1]
  · have h0 : bodyOrder 0 = 1 := Fin.ext hcases.1
    have h1 : bodyOrder 1 = 0 := Fin.ext hcases.2
    simpa only [_root_.CurrentAFT.PairCertificateFamilies.pairBodyRaw, Function.comp_apply, h0, h1] using hsymmetric (centers 1) (centers 0)
open _root_.P2M8f8f5b7e renaming h187 → _p2mH187
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h186 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (density : Body → Body → ℝ)
    (hfirst : ∀ second, ∑ first, body.weight first * density first second = 0)
    (hsecond : ∀ first, ∑ second, body.weight second * density first second = 0)
    (hsymmetric : ∀ first second, density first second = density second first) :
    (_root_.CurrentAFT.PairCertificateFamilies.bodyPairKernel primary body density hfirst hsecond).val = _root_.CurrentAFT.PairCertificateFamilies.pairBodyRaw density :=
  _root_.CurrentAFT.ControlProduct.symmetrize_of_symmetric _ (_p2mH187 density hsymmetric)
open _root_.P2M8f8f5b7e renaming h186 → _p2mH186
end
open _root_.P2M8f8f5b7e renaming h186 → _p2mH186
open _root_.P2M8f8f5b7e renaming h187 → _p2mH187
end CurrentAFT.PairCertificateFamilies
open _root_.P2M8f8f5b7e renaming h186 → _p2mH186
open _root_.P2M8f8f5b7e renaming h187 → _p2mH187
end
open _root_.P2M8f8f5b7e renaming h186 → _p2mH186
open _root_.P2M8f8f5b7e renaming h187 → _p2mH187
namespace CurrentAFT.DiffusePairCertificates
end CurrentAFT.DiffusePairCertificates
namespace CurrentAFT.DiffusePairCertificates.diffuseCertificate
end CurrentAFT.DiffusePairCertificates.diffuseCertificate
namespace CurrentAFT.PairQuadraticFamilies
end CurrentAFT.PairQuadraticFamilies
section
namespace CurrentAFT.ActualPairBridge
open AFT AFT.TrimmedSlice DiffuseProfiles ProposalPrimary ActualControls ProposalSymmetry
  FirstHistogram LocalReferenceEnergy DiffusePair
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.anchorWidth Parameters.sourceCutoff
  ProposalPrimary.primaryLaw DiffuseProfiles.edgeLaw LocalReferenceEnergy.diffusePairAt
  FirstHistogram.diffuseSeedPair ProposalSymmetry.directionLaw DiffusePair.pairProfile
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h26 {Primary Coin Direction Blur : Type*}
    [Fintype Primary] [Fintype Coin] [Fintype Direction] [Fintype Blur]
    (primary : _root_.AFT.FiniteDist Primary) (coin : _root_.AFT.FiniteDist Coin) (blur : _root_.AFT.FiniteDist Blur)
    (direction : Primary × Coin → Direction) (kernel : Direction → Blur → ℝ) :
    (((primary.prod coin).map direction).prod blur).expectation (fun seed => kernel seed.1 seed.2) =
      primary.expectation (fun color => coin.expectation (fun bit => blur.expectation (kernel (direction (color, bit))))) := by
  rw [_root_.AFT.FiniteDist.expectation_prod, _root_.AFT.FiniteDist.expectation_map, _root_.AFT.FiniteDist.expectation_prod]
  rfl
open _root_.P2M8f8f5b7e renaming h26 → _p2mH26
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h27 (security : ℕ) (scalar : _root_.CurrentAFT.LocalReferenceEnergy.Scalar security)
    (first second : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.LocalReferenceEnergy.signedDiffusePair security scalar (fun _ => 1) first second = _root_.CurrentAFT.DiffusePair.pairProfile security scalar.val first second := by
  have h := _p2mH26 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.AFT.FiniteDist.uniform Bool)
    ((_root_.CurrentAFT.DiffuseProfiles.edgeLaw security).prod (_root_.CurrentAFT.DiffuseProfiles.edgeLaw security))
    (fun point => _root_.CurrentAFT.InwardAnchor.positiveDirection security point.1 point.2)
    (fun sign edge => _root_.AFT.TrimmedSlice.averagedPair (_root_.CurrentAFT.Parameters.modulus security) 1
      (_root_.CurrentAFT.DiffuseProfiles.intervalStart sign (_root_.CurrentAFT.Parameters.anchorWidth security) (edge.1.val - edge.2.val)) scalar.val
        (_root_.CurrentAFT.Parameters.anchorWidth security) first second)
  have hleft : _root_.CurrentAFT.LocalReferenceEnergy.signedDiffusePair security scalar (fun _ => 1) first second =
      (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).expectation (fun color => (_root_.AFT.FiniteDist.uniform Bool).expectation (fun coin =>
        ((_root_.CurrentAFT.DiffuseProfiles.edgeLaw security).prod (_root_.CurrentAFT.DiffuseProfiles.edgeLaw security)).expectation (fun edge => _root_.AFT.TrimmedSlice.averagedPair (_root_.CurrentAFT.Parameters.modulus security) 1
          (_root_.CurrentAFT.DiffuseProfiles.intervalStart (_root_.CurrentAFT.InwardAnchor.positiveDirection security color coin) (_root_.CurrentAFT.Parameters.anchorWidth security)
            (edge.1.val - edge.2.val)) scalar.val (_root_.CurrentAFT.Parameters.anchorWidth security) first second))) := by
    simp only [_root_.CurrentAFT.LocalReferenceEnergy.signedDiffusePair, mul_one, _root_.CurrentAFT.LocalReferenceEnergy.diffusePairAt, _root_.AFT.FiniteDist.mix_weight,
      _root_.CurrentAFT.FirstHistogram.diffuseSeedPair_weight, _root_.CurrentAFT.DiffuseProfiles.actualBlur, _root_.CurrentAFT.DiffuseProfiles.actualSecond, _root_.CurrentAFT.LocalReferenceEnergy.publicBlurLaw, _root_.AFT.FiniteDist.expectation]
  have hright : _root_.CurrentAFT.DiffusePair.pairProfile security scalar.val first second =
      (((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).prod (_root_.AFT.FiniteDist.uniform Bool)).map
        (fun point => _root_.CurrentAFT.InwardAnchor.positiveDirection security point.1 point.2) |>.prod
          ((_root_.CurrentAFT.DiffuseProfiles.edgeLaw security).prod (_root_.CurrentAFT.DiffuseProfiles.edgeLaw security))).expectation (fun seed => _root_.AFT.TrimmedSlice.averagedPair (_root_.CurrentAFT.Parameters.modulus security) 1
            (_root_.CurrentAFT.DiffuseProfiles.intervalStart seed.1 (_root_.CurrentAFT.Parameters.anchorWidth security) (seed.2.1.val - seed.2.2.val)) scalar.val
              (_root_.CurrentAFT.Parameters.anchorWidth security) first second) := by
    simp only [_root_.CurrentAFT.DiffusePair.pairProfile, _root_.AFT.TrimmedSlice.mixedPair, _root_.CurrentAFT.DiffusePair.pairStart, _root_.CurrentAFT.DiffusePair.pairBlur, _root_.CurrentAFT.DiffusePair.pairSeedLaw, _root_.CurrentAFT.ProposalSymmetry.directionLaw, _root_.AFT.FiniteDist.expectation]
  exact hleft.trans (h.symm.trans hright.symm)
open _root_.P2M8f8f5b7e renaming h27 → _p2mH27
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h28 (security : ℕ) (scalar : _root_.CurrentAFT.LocalReferenceEnergy.Scalar security)
    (first second : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.LocalReferenceEnergy.signedPairAt security scalar (fun _ => 1) first second =
      (1 - _root_.CurrentAFT.DiffuseProfiles.activation security) * _root_.CurrentAFT.DiffusePair.pairProfile security scalar.val first second +
        _root_.CurrentAFT.DiffuseProfiles.activation security * (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight first * (_root_.CurrentAFT.LocalReferenceEnergy.markedCompanionAt security first scalar).weight second := by
  rw [_root_.CurrentAFT.LocalReferenceEnergy.signedPairAt_decomposition, _p2mH27]
  simp only [_root_.CurrentAFT.LocalReferenceEnergy.signedMarkedPair, mul_one]
open _root_.P2M8f8f5b7e renaming h28 → _p2mH28
end
open _root_.P2M8f8f5b7e renaming h26 → _p2mH26
open _root_.P2M8f8f5b7e renaming h27 → _p2mH27
open _root_.P2M8f8f5b7e renaming h28 → _p2mH28
end CurrentAFT.ActualPairBridge
open _root_.P2M8f8f5b7e renaming h26 → _p2mH26
open _root_.P2M8f8f5b7e renaming h27 → _p2mH27
open _root_.P2M8f8f5b7e renaming h28 → _p2mH28
end
open _root_.P2M8f8f5b7e renaming h26 → _p2mH26
open _root_.P2M8f8f5b7e renaming h27 → _p2mH27
open _root_.P2M8f8f5b7e renaming h28 → _p2mH28
namespace CurrentAFT.ControlProduct
end CurrentAFT.ControlProduct
namespace CurrentAFT.ControlProduct.homogeneousProduct
end CurrentAFT.ControlProduct.homogeneousProduct
namespace CurrentAFT.GradedControlAlgebra
end CurrentAFT.GradedControlAlgebra
namespace CurrentAFT.GradedControlAlgebra.coefficientsToFamily
end CurrentAFT.GradedControlAlgebra.coefficientsToFamily
namespace CurrentAFT.GradedControlAlgebra.familyProduct
end CurrentAFT.GradedControlAlgebra.familyProduct
namespace CurrentAFT.GradedControlAlgebra.positiveArity
end CurrentAFT.GradedControlAlgebra.positiveArity
namespace CurrentAFT.GradedControlAlgebra.scalarAt
end CurrentAFT.GradedControlAlgebra.scalarAt
namespace CurrentAFT.GradedControlAlgebra.scalarKernel
end CurrentAFT.GradedControlAlgebra.scalarKernel
namespace CurrentAFT.GradedControlAlgebra.transportKernel
end CurrentAFT.GradedControlAlgebra.transportKernel
namespace CurrentAFT.GradedControlAlgebra.zeroArity
end CurrentAFT.GradedControlAlgebra.zeroArity
section
namespace CurrentAFT.GradedInverse
open AFT ControlCoordinates ControlProduct GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h129 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order)
    (hfirst : _root_.CurrentAFT.GradedInverse.VanishesBelow primary body order 1 family) (power : ℕ) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow primary body order power (family ^ power) := by
  induction power with
  | zero => exact _root_.CurrentAFT.GradedInverse.vanishesBelow_zero primary body order _
  | succ power ih =>
    rw [pow_succ]
    exact _root_.CurrentAFT.GradedInverse.vanishesBelow_mul primary body order power 1 _ family ih hfirst
open _root_.P2M8f8f5b7e renaming h129 → _p2mH129
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h127 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order)
    (hzero : family (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0) : family ^ (order + 1) = 0 := by
  have h := _p2mH129 primary body order family
    (_root_.CurrentAFT.GradedInverse.vanishesBelow_one_of_zero primary body order family hzero) (order + 1)
  funext arity
  exact h arity (by have := arity.property; omega)
open _root_.P2M8f8f5b7e renaming h127 → _p2mH127
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h128 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (order : ℕ) (background : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order)
    (hscalar : background (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = (1 : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order)) :
    _root_.CurrentAFT.GradedInverse.backgroundInverse primary body order background * background = 1 := by
  have hzero : (1 - background : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0 := by
    change (1 : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) - background (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0
    rw [hscalar, sub_self]
  have hnil := _p2mH127 primary body order (1 - background) hzero
  have hgeom : (∑ power ∈ Finset.range (order + 1), (1 - background) ^ power) *
      (1 - (1 - background)) = 1 - (1 - background) ^ (order + 1) :=
    geom_sum_mul_neg (1 - background) (order + 1)
  simpa only [_root_.CurrentAFT.GradedInverse.backgroundInverse, sub_sub_cancel, hnil, sub_zero] using hgeom
open _root_.P2M8f8f5b7e renaming h128 → _p2mH128
end
open _root_.P2M8f8f5b7e renaming h127 → _p2mH127
open _root_.P2M8f8f5b7e renaming h128 → _p2mH128
open _root_.P2M8f8f5b7e renaming h129 → _p2mH129
end CurrentAFT.GradedInverse
open _root_.P2M8f8f5b7e renaming h127 → _p2mH127
open _root_.P2M8f8f5b7e renaming h128 → _p2mH128
open _root_.P2M8f8f5b7e renaming h129 → _p2mH129
end
open _root_.P2M8f8f5b7e renaming h127 → _p2mH127
open _root_.P2M8f8f5b7e renaming h128 → _p2mH128
open _root_.P2M8f8f5b7e renaming h129 → _p2mH129
namespace CurrentAFT.BackgroundPopulationBounds
end CurrentAFT.BackgroundPopulationBounds
namespace CurrentAFT.BodyRootAverages
end CurrentAFT.BodyRootAverages
namespace CurrentAFT.BodyRootAverages.cyclicShift
end CurrentAFT.BodyRootAverages.cyclicShift
namespace CurrentAFT.BodyRootAverages.role_rootAverage
end CurrentAFT.BodyRootAverages.role_rootAverage
namespace CurrentAFT.BodyRootAverages.rootAverage
end CurrentAFT.BodyRootAverages.rootAverage
namespace CurrentAFT.LocalReferenceEnergy.publicBlurLaw
end CurrentAFT.LocalReferenceEnergy.publicBlurLaw
namespace CurrentAFT.NormalizedMeanAlgebra
end CurrentAFT.NormalizedMeanAlgebra
namespace CurrentAFT.NormalizedMeanAlgebra.euclideanCenteredSum
end CurrentAFT.NormalizedMeanAlgebra.euclideanCenteredSum
namespace CurrentAFT.NormalizedMeanAlgebra.euclideanSum
end CurrentAFT.NormalizedMeanAlgebra.euclideanSum
section
namespace CurrentAFT.HistogramMean
open AFT DiffuseProfiles ProposalPrimary FirstHistogram LocalReferenceEnergy
  ConditionalPairMean BodyRootAverages UniformBodyProfiles BackgroundCertificates
  FringeCertificate BackgroundPopulationBounds FiniteConcentration
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.bodySize Parameters.legCount
  ProposalPrimary.primaryLaw ProposalPrimary.centerLaw ProposalPrimary.safeLaw
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h400 {Color : Type*} [Fintype Color] [DecidableEq Color]
    (law : _root_.AFT.FiniteDist (Color × Color)) (output : Color) :
    law.expectation (fun pair => _root_.CurrentAFT.FirstHistogram.atom pair.1 output + _root_.CurrentAFT.FirstHistogram.atom pair.2 output) =
      (∑ other, law.weight (output, other)) + ∑ other, law.weight (other, output) := by
  simp only [_root_.AFT.FiniteDist.expectation, Fintype.sum_prod_type, _root_.CurrentAFT.FirstHistogram.atom, mul_add, mul_ite,
    mul_one, mul_zero, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  congr 1
  rw [Finset.sum_comm]
  simp
open _root_.P2M8f8f5b7e renaming h400 → CurrentAFT.HistogramMean.pair_histogram
open _root_.P2M8f8f5b7e renaming h400 → _p2mH400
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h133 (security : ℕ) (output : _root_.CurrentAFT.HistogramMean.Palette security) :
    _root_.CurrentAFT.HistogramMean.offBodyMean security output =
      ∑ primary, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary *
        _root_.CurrentAFT.FirstHistogram.endpointHistogram security (_root_.CurrentAFT.FirstHistogram.referenceLaw security primary) output := by
  have hreference (primary : _root_.CurrentAFT.HistogramMean.Palette security) := _root_.CurrentAFT.LocalReferenceEnergy.reference_scalar_disintegration security primary
    (fun sample => _root_.CurrentAFT.FirstHistogram.atom sample.2.1 output + _root_.CurrentAFT.FirstHistogram.atom sample.2.2 output)
  simp only [_p2mH400] at hreference
  simp only [_root_.CurrentAFT.HistogramMean.offBodyMean, _root_.AFT.FiniteDist.expectation, _p2mH88, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro primary _
  conv_lhs =>
    arg 2
    ext scalar
    rw [mul_left_comm]
  rw [← Finset.mul_sum]
  change (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary *
    (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).expectation (fun scalar =>
      (∑ other, (_root_.CurrentAFT.LocalReferenceEnergy.pairAt security primary scalar).weight (output, other)) +
        ∑ other, (_root_.CurrentAFT.LocalReferenceEnergy.pairAt security primary scalar).weight (other, output)) = _
  rw [← hreference]
  rfl
open _root_.P2M8f8f5b7e renaming h133 → _p2mH133
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h134 (security : ℕ) (output : _root_.CurrentAFT.HistogramMean.Palette security) :
    _root_.CurrentAFT.HistogramMean.offBodyMean security output + (_root_.CurrentAFT.ProposalPrimary.bodyLaw security true).weight output =
      _root_.CurrentAFT.FirstHistogram.legFirstMean security output := by
  rw [_p2mH133]
  rfl
open _root_.P2M8f8f5b7e renaming h134 → _p2mH134
end
open _root_.P2M8f8f5b7e renaming h133 → _p2mH133
open _root_.P2M8f8f5b7e renaming h134 → _p2mH134
open _root_.P2M8f8f5b7e renaming h400 → CurrentAFT.HistogramMean.pair_histogram
open _root_.P2M8f8f5b7e renaming h400 → _p2mH400
end CurrentAFT.HistogramMean
open _root_.P2M8f8f5b7e renaming h133 → _p2mH133
open _root_.P2M8f8f5b7e renaming h134 → _p2mH134
open _root_.P2M8f8f5b7e renaming h400 → CurrentAFT.HistogramMean.pair_histogram
open _root_.P2M8f8f5b7e renaming h400 → _p2mH400
end
open _root_.P2M8f8f5b7e renaming h133 → _p2mH133
open _root_.P2M8f8f5b7e renaming h134 → _p2mH134
namespace CurrentAFT.ActualBlockFock
end CurrentAFT.ActualBlockFock
namespace CurrentAFT.ActualBlockFock.Slots
end CurrentAFT.ActualBlockFock.Slots
namespace CurrentAFT.ActualBlockFock.Slots.match_1
end CurrentAFT.ActualBlockFock.Slots.match_1
namespace CurrentAFT.ActualBlockFock.blockLawAt
end CurrentAFT.ActualBlockFock.blockLawAt
namespace CurrentAFT.ActualBlockFock.productFockEnergy
end CurrentAFT.ActualBlockFock.productFockEnergy
namespace CurrentAFT.ActualBlockFock.singletonLaw
end CurrentAFT.ActualBlockFock.singletonLaw
namespace CurrentAFT.ConditionalHistogramMGF
end CurrentAFT.ConditionalHistogramMGF
namespace CurrentAFT.PhysicalFockRates
end CurrentAFT.PhysicalFockRates
namespace CurrentAFT.PhysicalFockRates.normalizedScale
end CurrentAFT.PhysicalFockRates.normalizedScale
section
namespace CurrentAFT.ActualBlockMean
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PositiveFirstCoefficient
  ActualBlockFock ConditionalHistogramMean ActualCycleMeanMGF UniformBodyProfiles
  HistogramMean BodyRootAverages PhysicalBlockTensors
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] CycleMeanMGF.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
  primaryLaw centerLaw safeLaw scalarLaw
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h394 {Source Color : Type*} [Fintype Source] [Fintype Color]
    (source : _root_.AFT.FiniteDist Source) (pair : Source → _root_.AFT.FiniteDist (Color × Color))
    (body : _root_.AFT.FiniteDist Color) (color : Color) :
    ((_root_.AFT.PhysicalBlockTensors.sharedSourceTriple source pair (fun _ _ _ => body)).map (fun word => word 2)).weight color =
      body.weight color := by
  rw [_p2mH0]
  have hmass (first second : Color) : _root_.AFT.BlockDensity.attachedMass source pair (fun _ _ _ => body)
      first second color = (source.mix pair).weight (first, second) * body.weight color := by
    simp only [_root_.AFT.BlockDensity.attachedMass, _root_.AFT.FiniteDist.mix_weight, Finset.sum_mul, mul_assoc]
  simp_rw [hmass]
  have hsum : (∑ first, ∑ second, (source.mix pair).weight (first, second)) = 1 := by
    simpa only [Fintype.sum_prod_type] using (source.mix pair).sum_one
  calc
    _ = (∑ first, ∑ second, (source.mix pair).weight (first, second)) * body.weight color := by
      simp only [Finset.sum_mul]
    _ = _ := by rw [hsum, one_mul]
open _root_.P2M8f8f5b7e renaming h394 → _p2mH394
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h25 (security : ℕ) (root : ℤ) (scalar : _root_.CurrentAFT.FirstHistogram.Scalar security)
    (output : _root_.CurrentAFT.ActualBlockMean.Palette security) :
    (∑ index : Fin 3, ((_root_.CurrentAFT.PositiveFirstCoefficient.positiveTripleLaw security root scalar).map (fun word => word index)).weight output) =
      _root_.CurrentAFT.ConditionalPairMean.pairMean security scalar output + (_root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security root scalar).weight output := by
  rw [Fin.sum_univ_three]
  simp only [_root_.CurrentAFT.PositiveFirstCoefficient.positiveTripleLaw, _p2mH1, _p2mH2,
    _p2mH394]
  congr 1
  rw [_p2mH88]
  simp only [_root_.AFT.FiniteDist.mix_weight]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun first primary =>
    (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * (_root_.CurrentAFT.LocalReferenceEnergy.pairAt security primary scalar).weight (first, output))]
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
open _root_.P2M8f8f5b7e renaming h25 → _p2mH25
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h23 (security : ℕ) (root : ℤ) :
    (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).mix (_root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security root) =
      (_root_.CurrentAFT.UniformBodyProfiles.preRootLaw security .attachment 0).map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security root) := by
  rw [_root_.CurrentAFT.UniformBodyProfiles.preRootLaw, _root_.AFT.FiniteDist.map_mix]
  congr 1
  funext scalar
  rw [_root_.CurrentAFT.LocalReferenceEnergy.attachmentAt, _p2mH85, add_comm root scalar.val]
open _root_.P2M8f8f5b7e renaming h23 → _p2mH23
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h24 (security : ℕ) (root : ℤ) (output : _root_.CurrentAFT.ActualBlockMean.Palette security) :
    (∑ index : Fin 3, ((_root_.CurrentAFT.ActualBlockFock.primaryLawAt security root).map (fun word => word index)).weight output) =
      _root_.CurrentAFT.HistogramMean.offBodyMean security output + ((_root_.CurrentAFT.UniformBodyProfiles.preRootLaw security .attachment 0).map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security root)).weight output := by
  simp only [_root_.CurrentAFT.ActualBlockFock.primaryLawAt, _root_.AFT.FiniteDist.map_mix, _root_.AFT.FiniteDist.mix_weight]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, _p2mH25]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← _root_.AFT.FiniteDist.mix_weight, _p2mH23]
  rfl
open _root_.P2M8f8f5b7e renaming h24 → _p2mH24
end
open _root_.P2M8f8f5b7e renaming h23 → _p2mH23
open _root_.P2M8f8f5b7e renaming h24 → _p2mH24
open _root_.P2M8f8f5b7e renaming h25 → _p2mH25
open _root_.P2M8f8f5b7e renaming h394 → _p2mH394
end CurrentAFT.ActualBlockMean
open _root_.P2M8f8f5b7e renaming h23 → _p2mH23
open _root_.P2M8f8f5b7e renaming h24 → _p2mH24
open _root_.P2M8f8f5b7e renaming h25 → _p2mH25
open _root_.P2M8f8f5b7e renaming h394 → _p2mH394
end
open _root_.P2M8f8f5b7e renaming h23 → _p2mH23
open _root_.P2M8f8f5b7e renaming h24 → _p2mH24
open _root_.P2M8f8f5b7e renaming h25 → _p2mH25
namespace AFT.RepresentedPolynomial.referenceCoefficientForm
end AFT.RepresentedPolynomial.referenceCoefficientForm
namespace CurrentAFT.GradedInverse
end CurrentAFT.GradedInverse
namespace CurrentAFT.GradedInverse.backgroundInverse
end CurrentAFT.GradedInverse.backgroundInverse
namespace CurrentAFT.PairedReferenceEnergy
end CurrentAFT.PairedReferenceEnergy
namespace CurrentAFT.PairedReferenceEnergy.compensatorAt
end CurrentAFT.PairedReferenceEnergy.compensatorAt
namespace CurrentAFT.PairedReferenceEnergy.controlMass
end CurrentAFT.PairedReferenceEnergy.controlMass
namespace CurrentAFT.PairedReferenceEnergy.localDegreeLinear
end CurrentAFT.PairedReferenceEnergy.localDegreeLinear
namespace CurrentAFT.PairedReferenceEnergy.pairedMassLinear
end CurrentAFT.PairedReferenceEnergy.pairedMassLinear
namespace CurrentAFT.PairedReferenceEnergy.profileEnergy_sub_le
end CurrentAFT.PairedReferenceEnergy.profileEnergy_sub_le
namespace CurrentAFT.PairedReferenceEnergy.signedCompensatorAt
end CurrentAFT.PairedReferenceEnergy.signedCompensatorAt
namespace CurrentAFT.PrimaryTensorInverse
end CurrentAFT.PrimaryTensorInverse
namespace CurrentAFT.PrimaryTensorInverse.densityInverse
end CurrentAFT.PrimaryTensorInverse.densityInverse
namespace CurrentAFT.PrimaryTensorInverse.densityResponse
end CurrentAFT.PrimaryTensorInverse.densityResponse
namespace CurrentAFT.PrimaryTensorInverse.diagonal
end CurrentAFT.PrimaryTensorInverse.diagonal
namespace CurrentAFT.PrimaryTensorInverse.massDensity
end CurrentAFT.PrimaryTensorInverse.massDensity
namespace CurrentAFT.PrimaryTensorInverse.massLeading
end CurrentAFT.PrimaryTensorInverse.massLeading
namespace CurrentAFT.PrimaryTensorInverse.massLift
end CurrentAFT.PrimaryTensorInverse.massLift
section
namespace CurrentAFT.LocalCoefficientFamily
open AFT DiffuseProfiles ProposalPrimary ActualControls
open ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.LocalCoefficientFamily.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.LocalCoefficientFamily.classicalSubtypeDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h155 (security degree : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.LocalCoefficientFamily.Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    _root_.CurrentAFT.PrimaryTensorInverse.tensorResponse security degree
      (_root_.CurrentAFT.LocalCoefficientFamily.normalizedSelectedDensity security degree mass selected hdegree) =
        _root_.CurrentAFT.LocalCoefficientFamily.selectedDensity security degree mass selected hdegree :=
  _p2mH216 security degree _
open _root_.P2M8f8f5b7e renaming h155 → _p2mH155
set_option maxRecDepth 8192
private def _root_.P2M8f8f5b7e.h401 {Source Target Color : Type*} (equiv : Source ≃ Target) :
    (Target → Color) ≃ (Source → Color) where
  toFun word := word ∘ equiv
  invFun word := word ∘ equiv.symm
  left_inv word := by funext index; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv word := by funext index; simp only [Function.comp_apply, Equiv.symm_apply_apply]
open _root_.P2M8f8f5b7e renaming h401 → CurrentAFT.LocalCoefficientFamily.orderedWordEquiv
open _root_.P2M8f8f5b7e renaming h401 → _p2mH401
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h156 (security degree : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.LocalCoefficientFamily.Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree) :
    _root_.CurrentAFT.LocalCoefficientFamily.primaryLeadingPolynomial security degree (_root_.CurrentAFT.LocalCoefficientFamily.normalizedSelectedDensity security degree mass selected hdegree) =
      _root_.AFT.RepresentedPolynomial.referenceCoefficientForm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
        (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) mass selected := by
  unfold _root_.CurrentAFT.LocalCoefficientFamily.primaryLeadingPolynomial _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial _root_.CurrentAFT.PrimaryTensorInverse.massLeading
  rw [_p2mH155]
  let equiv := Fintype.equivFinOfCardEq hdegree
  have hreindex := (_p2mH401 (Color := _root_.CurrentAFT.LocalCoefficientFamily.Palette security) equiv).sum_comp
    (fun word : selected → _root_.CurrentAFT.LocalCoefficientFamily.Palette security =>
      MvPolynomial.C (_root_.AFT.LocalTensors.referenceRestrictedComponent (fun _ : Fin 4 => _root_.CurrentAFT.ProposalPrimary.primaryLaw security)
        (fun _ : Fin 4 => _root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) mass selected word *
          ∏ index, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight (word index)) *
        ∏ index, MvPolynomial.X (R := ℝ) (word index))
  change _ = ∑ word : selected → _root_.CurrentAFT.LocalCoefficientFamily.Palette security, _
  apply Eq.trans ?_ hreindex
  apply Finset.sum_congr rfl
  intro word _
  have hweight := equiv.prod_comp (fun index : Fin degree => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight (word index))
  have hmonomial := equiv.prod_comp (fun index : Fin degree => MvPolynomial.X (R := ℝ) (word index))
  simp only [_p2mH401, Equiv.coe_fn_mk, Function.comp_apply, hweight, hmonomial,
    _root_.CurrentAFT.LocalCoefficientFamily.selectedDensity, _root_.CurrentAFT.PrimaryTensorInverse.referenceWeight]
  congr 1
  congr 1
  ring
open _root_.P2M8f8f5b7e renaming h156 → _p2mH156
end
open _root_.P2M8f8f5b7e renaming h155 → _p2mH155
open _root_.P2M8f8f5b7e renaming h156 → _p2mH156
open _root_.P2M8f8f5b7e renaming h401 → CurrentAFT.LocalCoefficientFamily.orderedWordEquiv
open _root_.P2M8f8f5b7e renaming h401 → _p2mH401
end CurrentAFT.LocalCoefficientFamily
open _root_.P2M8f8f5b7e renaming h155 → _p2mH155
open _root_.P2M8f8f5b7e renaming h156 → _p2mH156
open _root_.P2M8f8f5b7e renaming h401 → CurrentAFT.LocalCoefficientFamily.orderedWordEquiv
open _root_.P2M8f8f5b7e renaming h401 → _p2mH401
end
open _root_.P2M8f8f5b7e renaming h155 → _p2mH155
open _root_.P2M8f8f5b7e renaming h156 → _p2mH156
namespace CurrentAFT.LeadingEvaluation
end CurrentAFT.LeadingEvaluation
namespace CurrentAFT.LeadingEvaluation.familyLinear
end CurrentAFT.LeadingEvaluation.familyLinear
namespace CurrentAFT.LeadingEvaluation.homogeneousLinear
end CurrentAFT.LeadingEvaluation.homogeneousLinear
namespace CurrentAFT.LocalCoefficientFamily
end CurrentAFT.LocalCoefficientFamily
namespace CurrentAFT.LocalCoefficientFamily.orderedWordEquiv
end CurrentAFT.LocalCoefficientFamily.orderedWordEquiv
namespace CurrentAFT.LocalCoefficientFamily.selectedDensity
end CurrentAFT.LocalCoefficientFamily.selectedDensity
namespace CurrentAFT.LocalCoefficientFamily.selectedKernel
end CurrentAFT.LocalCoefficientFamily.selectedKernel
namespace CurrentAFT.PrimaryTensorInverse.referenceWeight
end CurrentAFT.PrimaryTensorInverse.referenceWeight
section
namespace CurrentAFT.LocalCoefficientEvaluation
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open LocalCoefficientFamily LeadingEvaluation
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.LocalCoefficientEvaluation.classicalFinDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h150 {Color : Type*} [Fintype Color] (primary : _root_.AFT.FiniteDist Color)
    (hpositive : ∀ color, primary.weight color ≠ 0)
    (channel : (Color → ℝ) →ₗ[ℝ] (Color → ℝ)) (degree : ℕ) (density : (Fin degree → Color) → ℝ) :
    _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial primary (_root_.CurrentAFT.LocalCoefficientEvaluation.channelForm primary channel) degree density =
      _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial primary MvPolynomial.X degree (_root_.AFT.TensorChannel.apply degree (fun _ => channel) density) := by
  classical
  unfold _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial
  simp_rw [_root_.AFT.TensorChannel.apply_formula_instance]
  simp only [Finset.mul_sum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  unfold _root_.CurrentAFT.LocalCoefficientEvaluation.channelForm
  rw [Fintype.prod_sum (fun index : Fin degree => fun output : Color =>
    MvPolynomial.C (primary.weight output * channel (Pi.single (input index) 1) output / primary.weight (input index)) *
      MvPolynomial.X output)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro output _
  rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul]
  congr 1
  congr 1
  have hproduct : (∏ index, primary.weight (input index)) *
      (∏ index, primary.weight (output index) * channel (Pi.single (input index) 1) (output index) /
        primary.weight (input index)) =
      (∏ index, primary.weight (output index)) *
        ∏ index, channel (Pi.single (input index) 1) (output index) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro index _
    field_simp [hpositive (input index)]
  calc
    _ = density input * ((∏ index, primary.weight (input index)) *
        ∏ index, primary.weight (output index) * channel (Pi.single (input index) 1) (output index) /
          primary.weight (input index)) := by ring
    _ = _ := by rw [hproduct]; ring
open _root_.P2M8f8f5b7e renaming h150 → _p2mH150
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h151 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (forms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (degree : ℕ) (density : (Fin degree → Primary) → ℝ) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body forms bodyForms (fun colors (_ : Fin 0 → Body) => density colors) =
      _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial primary forms degree density := by
  simp only [_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial, _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial, Fin.prod_univ_zero, Fintype.sum_unique, mul_one]
open _root_.P2M8f8f5b7e renaming h151 → _p2mH151
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h152 (security degree : ℕ) (density : (Fin degree → _root_.CurrentAFT.LocalCoefficientEvaluation.Palette security) → ℝ)
    (bodyForms : _root_.CurrentAFT.ActualControls.SafePalette security → MvPolynomial (_root_.CurrentAFT.LocalCoefficientEvaluation.Palette security) ℝ) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms
      (fun colors (_ : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) => density colors) =
        _root_.CurrentAFT.LocalCoefficientFamily.primaryLeadingPolynomial security degree density := by
  rw [_p2mH151, _root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm,
    _p2mH150 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (fun color => (_root_.CurrentAFT.ActualControls.primaryReference_positive security color).ne')]
  rfl
open _root_.P2M8f8f5b7e renaming h152 → _p2mH152
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h154 (security degree : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.LocalCoefficientEvaluation.Palette security) → ℝ)
    (selected : Finset (Fin 4)) (hdegree : Fintype.card selected = degree)
    (bodyForms : _root_.CurrentAFT.ActualControls.SafePalette security → MvPolynomial (_root_.CurrentAFT.LocalCoefficientEvaluation.Palette security) ℝ) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms
      (_root_.CurrentAFT.LocalCoefficientFamily.selectedKernel security degree mass selected hdegree).val =
        _root_.AFT.RepresentedPolynomial.referenceCoefficientForm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
          (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) mass selected := by
  change _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms
    (_root_.CurrentAFT.ControlProduct.symmetrize (fun colors (_ : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) =>
      _root_.CurrentAFT.LocalCoefficientFamily.normalizedSelectedDensity security degree mass selected hdegree colors)) = _
  rw [_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial_symmetrize, _p2mH152, _p2mH156]
open _root_.P2M8f8f5b7e renaming h154 → _p2mH154
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h153 (security order : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.LocalCoefficientEvaluation.Palette security) → ℝ)
    (selected : Finset (Fin 4))
    (bodyForms : _root_.CurrentAFT.ActualControls.SafePalette security → MvPolynomial (_root_.CurrentAFT.LocalCoefficientEvaluation.Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :
    _root_.CurrentAFT.LocalCoefficientEvaluation.evaluation security order bodyForms hbody (_root_.CurrentAFT.LocalCoefficientFamily.selectedFamily security order mass selected) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.referenceCoefficientForm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
          (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) mass selected) := by
  unfold _root_.CurrentAFT.LocalCoefficientFamily.selectedFamily
  split_ifs with hdegree
  · change _root_.CurrentAFT.LeadingEvaluation.familyLinear _ _ _ _ _ (Pi.single _ _) = _
    rw [_root_.CurrentAFT.LeadingEvaluation.familyLinear_single]
    change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms (_root_.CurrentAFT.LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val) = _
    rw [_p2mH154]
  · rw [map_zero]
    have hzero := _root_.CurrentAFT.LeadingEvaluation.homogeneousLinear_above (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm_homogeneous security) hbody order selected.card 0 (by omega)
      (_root_.CurrentAFT.LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp))
    change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms (_root_.CurrentAFT.LocalCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val) = 0 at hzero
    rw [_p2mH154] at hzero
    exact hzero.symm
open _root_.P2M8f8f5b7e renaming h153 → _p2mH153
end
open _root_.P2M8f8f5b7e renaming h150 → _p2mH150
open _root_.P2M8f8f5b7e renaming h151 → _p2mH151
open _root_.P2M8f8f5b7e renaming h152 → _p2mH152
open _root_.P2M8f8f5b7e renaming h153 → _p2mH153
open _root_.P2M8f8f5b7e renaming h154 → _p2mH154
end CurrentAFT.LocalCoefficientEvaluation
open _root_.P2M8f8f5b7e renaming h150 → _p2mH150
open _root_.P2M8f8f5b7e renaming h151 → _p2mH151
open _root_.P2M8f8f5b7e renaming h152 → _p2mH152
open _root_.P2M8f8f5b7e renaming h153 → _p2mH153
open _root_.P2M8f8f5b7e renaming h154 → _p2mH154
end
open _root_.P2M8f8f5b7e renaming h150 → _p2mH150
open _root_.P2M8f8f5b7e renaming h151 → _p2mH151
open _root_.P2M8f8f5b7e renaming h152 → _p2mH152
open _root_.P2M8f8f5b7e renaming h153 → _p2mH153
open _root_.P2M8f8f5b7e renaming h154 → _p2mH154
namespace CurrentAFT.ActualBackground
end CurrentAFT.ActualBackground
namespace CurrentAFT.ActualBackground.background
end CurrentAFT.ActualBackground.background
namespace CurrentAFT.ActualBackground.stabilityConstant
end CurrentAFT.ActualBackground.stabilityConstant
namespace CurrentAFT.ActualBackgroundInverse
end CurrentAFT.ActualBackgroundInverse
namespace CurrentAFT.ActualBackgroundInverse.inverse
end CurrentAFT.ActualBackgroundInverse.inverse
namespace CurrentAFT.LocalCoefficientEvaluation
end CurrentAFT.LocalCoefficientEvaluation
namespace CurrentAFT.LocalCoefficientEvaluation.densityPolynomial
end CurrentAFT.LocalCoefficientEvaluation.densityPolynomial
namespace CurrentAFT.LocalCoefficientEvaluation.evaluation
end CurrentAFT.LocalCoefficientEvaluation.evaluation
namespace CurrentAFT.LocalCoefficientEvaluation.primaryForm
end CurrentAFT.LocalCoefficientEvaluation.primaryForm
section
namespace CurrentAFT.BackgroundEvaluation
open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies MarkedPairLeading LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
attribute [local instance] _root_.CurrentAFT.BackgroundEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h45 (security order degree : ℕ) (hdegree : degree ≤ order)
    (profile : (Fin degree → _root_.CurrentAFT.ActualControls.Palette security) → ℝ)
    (hcentered : _root_.CurrentAFT.PrimaryTensorInverse.MassCentered degree profile)
    (hsymmetric : ∀ (permutation : Equiv.Perm (Fin degree)) word, profile (word ∘ permutation) = profile word) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.PrimaryMassFamilies.massCertificateFamily security order degree hdegree profile hcentered hsymmetric) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security degree profile) := by
  unfold _root_.CurrentAFT.PrimaryMassFamilies.massCertificateFamily
  change _root_.CurrentAFT.LeadingEvaluation.familyLinear (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security) order (Pi.single _ _) = _
  rw [_root_.CurrentAFT.LeadingEvaluation.familyLinear_single]
  change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
    (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security) (fun colors (_ : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) => _root_.CurrentAFT.PrimaryTensorInverse.massLift security degree profile colors)) = _
  rw [_p2mH152]
  unfold _root_.CurrentAFT.LocalCoefficientFamily.primaryLeadingPolynomial
  rw [_p2mH215]
open _root_.P2M8f8f5b7e renaming h45 → _p2mH45
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h46 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.PrimaryDeviationCertificate.certificate security order horder) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile (_root_.CurrentAFT.PrimaryDeviationCertificate.deviation security))) :=
  _p2mH45 security order 1 horder _ _ _
open _root_.P2M8f8f5b7e renaming h46 → _p2mH46
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h43 (security order : ℕ) (horder : 1 ≤ order) (scalar : _root_.CurrentAFT.ConditionalPairMean.Scalar security) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.ConditionalPairLinear.certificate security order horder scalar) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security 1 (_root_.CurrentAFT.ConditionalPairLinear.wordMean security scalar)) :=
  _p2mH45 security order 1 horder _ _ _
open _root_.P2M8f8f5b7e renaming h43 → _p2mH43
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h44 (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.DiffusePairCertificates.diffusePrimaryCertificate security order horder scalar) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security 2 (_root_.CurrentAFT.DiffusePairCertificates.residualMass security scalar)) :=
  _p2mH45 security order 2 horder _ _ _
open _root_.P2M8f8f5b7e renaming h44 → _p2mH44
end
open _root_.P2M8f8f5b7e renaming h43 → _p2mH43
open _root_.P2M8f8f5b7e renaming h44 → _p2mH44
open _root_.P2M8f8f5b7e renaming h45 → _p2mH45
open _root_.P2M8f8f5b7e renaming h46 → _p2mH46
end CurrentAFT.BackgroundEvaluation
open _root_.P2M8f8f5b7e renaming h43 → _p2mH43
open _root_.P2M8f8f5b7e renaming h44 → _p2mH44
open _root_.P2M8f8f5b7e renaming h45 → _p2mH45
open _root_.P2M8f8f5b7e renaming h46 → _p2mH46
end
open _root_.P2M8f8f5b7e renaming h43 → _p2mH43
open _root_.P2M8f8f5b7e renaming h44 → _p2mH44
open _root_.P2M8f8f5b7e renaming h45 → _p2mH45
open _root_.P2M8f8f5b7e renaming h46 → _p2mH46
namespace CurrentAFT.BackgroundEvaluation
end CurrentAFT.BackgroundEvaluation
namespace CurrentAFT.BackgroundEvaluation.bodyForm
end CurrentAFT.BackgroundEvaluation.bodyForm
section
namespace CurrentAFT.BackgroundFirstEvaluation
open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation
  LocalCoefficientFamily LocalCoefficientEvaluation FringeCertificate BackgroundTranslations
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
attribute [local instance] _root_.CurrentAFT.BackgroundFirstEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h52 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Primary → ℝ) (hcenter : ∑ color, primary.weight color * density color = 0) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms (_root_.CurrentAFT.BackgroundFamilies.primaryKernel primary body density hcenter).val =
      _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial primary primaryForms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density) :=
  _p2mH151 primary body primaryForms bodyForms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density)
open _root_.P2M8f8f5b7e renaming h52 → _p2mH52
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h49 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForms color).IsHomogeneous 1) (hbody : ∀ center, (bodyForms center).IsHomogeneous 1)
    (order : ℕ) (horder : 1 ≤ order) (density : Primary → ℝ)
    (hcenter : ∑ color, primary.weight color * density color = 0) :
    _root_.CurrentAFT.LeadingEvaluation.familyHom primary body primaryForms bodyForms hprimary hbody order
      (_root_.CurrentAFT.BackgroundFamilies.primaryFamily primary body order horder density hcenter) =
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial primary primaryForms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density)) := by
  change _root_.CurrentAFT.LeadingEvaluation.familyLinear primary body primaryForms bodyForms order (Pi.single _ _) = _
  rw [_root_.CurrentAFT.LeadingEvaluation.familyLinear_single]
  change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms
    (_root_.CurrentAFT.BackgroundFamilies.primaryKernel primary body density hcenter).val) = _
  rw [_p2mH52]
open _root_.P2M8f8f5b7e renaming h49 → _p2mH49
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h48 (security : ℕ) (profile : _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile profile) = _root_.AFT.RepresentedPolynomial.profileForm profile := by
  rw [_root_.AFT.RepresentedPolynomial.profileForm_apply]
  unfold _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial
  simp only [_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile, Fin.prod_univ_one]
  exact ((Equiv.funUnique (Fin 1) (_root_.CurrentAFT.ActualControls.Palette security)).symm.sum_comp
    (fun word : Fin 1 → _root_.CurrentAFT.ActualControls.Palette security => MvPolynomial.C (profile (word 0)) * MvPolynomial.X (word 0))).symm
open _root_.P2M8f8f5b7e renaming h48 → _p2mH48
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h47 (security : ℕ) (density : _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    _root_.CurrentAFT.PrimaryTensorInverse.massLeading security 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density) =
      _root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile (_root_.CurrentAFT.DiffuseProfiles.activation security • _root_.CurrentAFT.FirstResponse.response security
        (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * density color)) := by
  funext word
  have hresponse : _root_.CurrentAFT.PrimaryTensorInverse.tensorResponse security 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density) word = _root_.CurrentAFT.PrimaryTensorInverse.densityResponse security density (word 0) := rfl
  rw [_root_.CurrentAFT.PrimaryTensorInverse.massLeading, hresponse, _root_.CurrentAFT.PrimaryTensorInverse.referenceWeight, Fin.prod_univ_one, _root_.CurrentAFT.PrimaryTensorInverse.densityResponse_apply]
  simp only [_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile, Pi.smul_apply, smul_eq_mul]
  field_simp [(_root_.CurrentAFT.ActualControls.primaryReference_positive security (word 0)).ne']
open _root_.P2M8f8f5b7e renaming h47 → _p2mH47
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h51 (security order : ℕ) (horder : 1 ≤ order)
    (bodyForms : _root_.CurrentAFT.ActualControls.SafePalette security → MvPolynomial (_root_.CurrentAFT.ActualControls.Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1)
    (density : _root_.CurrentAFT.ActualControls.Palette security → ℝ)
    (hcenter : ∑ color, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * density color = 0) :
    _root_.CurrentAFT.LocalCoefficientEvaluation.evaluation security order bodyForms hbody
      (_root_.CurrentAFT.BackgroundFamilies.primaryFamily (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder density hcenter) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm
        (_root_.CurrentAFT.DiffuseProfiles.activation security • _root_.CurrentAFT.FirstResponse.response security (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * density color))) := by
  have h := _p2mH49 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms
    (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm_homogeneous security) hbody order horder density hcenter
  have hpoly := _p2mH152 security 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density) bodyForms
  rw [_p2mH151] at hpoly
  rw [hpoly] at h
  unfold _root_.CurrentAFT.LocalCoefficientFamily.primaryLeadingPolynomial at h
  rw [_p2mH47, _p2mH48] at h
  exact h
open _root_.P2M8f8f5b7e renaming h51 → _p2mH51
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h50 (security order : ℕ) (horder : 1 ≤ order)
    (density : _root_.CurrentAFT.ActualControls.Palette security → ℝ)
    (hcenter : ∑ color, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * density color = 0) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.BackgroundFamilies.primaryFamily (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder density hcenter) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm
        (_root_.CurrentAFT.DiffuseProfiles.activation security • _root_.CurrentAFT.FirstResponse.response security (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * density color))) :=
  _p2mH51 security order horder (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm_homogeneous security) density hcenter
open _root_.P2M8f8f5b7e renaming h50 → _p2mH50
end
open _root_.P2M8f8f5b7e renaming h47 → _p2mH47
open _root_.P2M8f8f5b7e renaming h48 → _p2mH48
open _root_.P2M8f8f5b7e renaming h49 → _p2mH49
open _root_.P2M8f8f5b7e renaming h50 → _p2mH50
open _root_.P2M8f8f5b7e renaming h51 → _p2mH51
open _root_.P2M8f8f5b7e renaming h52 → _p2mH52
end CurrentAFT.BackgroundFirstEvaluation
open _root_.P2M8f8f5b7e renaming h47 → _p2mH47
open _root_.P2M8f8f5b7e renaming h48 → _p2mH48
open _root_.P2M8f8f5b7e renaming h49 → _p2mH49
open _root_.P2M8f8f5b7e renaming h50 → _p2mH50
open _root_.P2M8f8f5b7e renaming h51 → _p2mH51
open _root_.P2M8f8f5b7e renaming h52 → _p2mH52
end
open _root_.P2M8f8f5b7e renaming h47 → _p2mH47
open _root_.P2M8f8f5b7e renaming h48 → _p2mH48
open _root_.P2M8f8f5b7e renaming h49 → _p2mH49
open _root_.P2M8f8f5b7e renaming h50 → _p2mH50
open _root_.P2M8f8f5b7e renaming h51 → _p2mH51
open _root_.P2M8f8f5b7e renaming h52 → _p2mH52
namespace CurrentAFT.BackgroundFirstEvaluation
end CurrentAFT.BackgroundFirstEvaluation
section
namespace CurrentAFT.BodyChannelEvaluation
open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation BackgroundFirstEvaluation
  MarkedPairLeading LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference MarkedPairLeading.bodyConvolution
attribute [local instance] _root_.CurrentAFT.BodyChannelEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h67 {Input Output : Type*} [Fintype Input] [Fintype Output]
    (input : _root_.AFT.FiniteDist Input) (output : _root_.AFT.FiniteDist Output) (hpositive : ∀ point, input.weight point ≠ 0)
    (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) (degree : ℕ) (density : (Fin degree → Input) → ℝ) :
    _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial input (_root_.CurrentAFT.BodyChannelEvaluation.rectangularForm input.weight output.weight channel) degree density =
      _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial output MvPolynomial.X degree (_root_.AFT.TensorChannel.apply degree (fun _ => channel) density) := by
  unfold _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial
  simp_rw [_root_.AFT.TensorChannel.apply_formula_instance]
  simp only [Finset.mul_sum, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro point _
  unfold _root_.CurrentAFT.BodyChannelEvaluation.rectangularForm
  rw [Fintype.prod_sum (fun index : Fin degree => fun value : Output =>
    MvPolynomial.C (output.weight value * channel (Pi.single (point index) 1) value / input.weight (point index)) * MvPolynomial.X value)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro value _
  rw [Finset.prod_mul_distrib, ← map_prod, ← mul_assoc, ← map_mul]
  congr 1
  congr 1
  have hproduct : (∏ index, input.weight (point index)) *
      (∏ index, output.weight (value index) * channel (Pi.single (point index) 1) (value index) / input.weight (point index)) =
      (∏ index, output.weight (value index)) * ∏ index, channel (Pi.single (point index) 1) (value index) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro index _
    field_simp [hpositive (point index)]
  calc
    _ = density point * ((∏ index, input.weight (point index)) *
        ∏ index, output.weight (value index) * channel (Pi.single (point index) 1) (value index) / input.weight (point index)) := by ring
    _ = _ := by rw [hproduct]; ring
open _root_.P2M8f8f5b7e renaming h67 → _p2mH67
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h69 {Input Output : Type*} [Fintype Input]
    (input : _root_.AFT.FiniteDist Input) (embedding : Input → Output) (point : Input) :
    _root_.CurrentAFT.BodyChannelEvaluation.weightedEmbedding input embedding (Pi.single point (1 : ℝ) : Input → ℝ) = input.weight point • (Pi.single (embedding point) (1 : ℝ) : Output → ℝ) := by
  funext output
  change (∑ other, input.weight other * (Pi.single point (1 : ℝ) : Input → ℝ) other *
    (Pi.single (embedding other) (1 : ℝ) : Output → ℝ) output) =
      input.weight point * (Pi.single (embedding point) (1 : ℝ) : Output → ℝ) output
  rw [Finset.sum_eq_single point]
  · simp only [Pi.single_eq_same, mul_one]
  · intro other _ hne
    simp only [Pi.single_eq_of_ne hne, mul_zero, zero_mul]
  · simp
open _root_.P2M8f8f5b7e renaming h69 → _p2mH69
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h60 (security : ℕ) (density : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) (output : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.BodyChannelEvaluation.bodyDensityChannel security density output = _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security density) output /
      (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight output := by
  simp only [_root_.CurrentAFT.BodyChannelEvaluation.bodyDensityChannel, LinearMap.comp_apply, _root_.CurrentAFT.PrimaryTensorInverse.diagonal, LinearMap.coe_mk, AddHom.coe_mk]
  ring
open _root_.P2M8f8f5b7e renaming h60 → _p2mH60
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h63 (security : ℕ) (point : _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.BackgroundEvaluation.bodyForm security point = _root_.CurrentAFT.BodyChannelEvaluation.rectangularForm (_root_.CurrentAFT.ActualControls.bodyReference security).weight (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight
      (_root_.CurrentAFT.BodyChannelEvaluation.bodyDensityChannel security) point := by
  rw [_root_.CurrentAFT.BackgroundEvaluation.bodyForm, _root_.AFT.RepresentedPolynomial.profileForm_apply]
  unfold _root_.CurrentAFT.BodyChannelEvaluation.rectangularForm
  apply Finset.sum_congr rfl
  intro output _
  congr 1
  congr 1
  rw [_p2mH60, _root_.CurrentAFT.BodyChannelEvaluation.safeMass, _p2mH69, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp [(_root_.CurrentAFT.ActualControls.primaryReference_positive security output).ne', (_root_.CurrentAFT.ActualControls.bodyReference_positive security point).ne']
open _root_.P2M8f8f5b7e renaming h63 → _p2mH63
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h66 (security degree : ℕ) (density : (Fin degree → _root_.CurrentAFT.ActualControls.SafePalette security) → ℝ) :
    _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security) degree density =
      _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security degree (_root_.CurrentAFT.BodyChannelEvaluation.bodyTensorMass security degree density) := by
  have hforms : _root_.CurrentAFT.BackgroundEvaluation.bodyForm security = _root_.CurrentAFT.BodyChannelEvaluation.rectangularForm (_root_.CurrentAFT.ActualControls.bodyReference security).weight (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight (_root_.CurrentAFT.BodyChannelEvaluation.bodyDensityChannel security) :=
    funext (_p2mH63 security)
  rw [hforms, _p2mH67 (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
    (fun point => (_root_.CurrentAFT.ActualControls.bodyReference_positive security point).ne')]
  rfl
open _root_.P2M8f8f5b7e renaming h66 → _p2mH66
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h64 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Body → ℝ) (hcenter : ∑ color, body.weight color * density color = 0) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms (_root_.CurrentAFT.BackgroundFamilies.bodyKernel primary body density hcenter).val =
      _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial body bodyForms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density) := by
  simp only [_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial, _root_.CurrentAFT.BackgroundFamilies.bodyKernel, _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial, _root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile, Fin.prod_univ_zero,
    Fintype.sum_unique, one_mul]
open _root_.P2M8f8f5b7e renaming h64 → _p2mH64
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h61 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForms color).IsHomogeneous 1) (hbody : ∀ center, (bodyForms center).IsHomogeneous 1)
    (order : ℕ) (horder : 1 ≤ order) (density : Body → ℝ)
    (hcenter : ∑ color, body.weight color * density color = 0) :
    _root_.CurrentAFT.LeadingEvaluation.familyHom primary body primaryForms bodyForms hprimary hbody order
      (_root_.CurrentAFT.BackgroundFamilies.bodyFamily primary body order horder density hcenter) =
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial body bodyForms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density)) := by
  change _root_.CurrentAFT.LeadingEvaluation.familyLinear primary body primaryForms bodyForms order (Pi.single _ _) = _
  rw [_root_.CurrentAFT.LeadingEvaluation.familyLinear_single]
  change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms
    (_root_.CurrentAFT.BackgroundFamilies.bodyKernel primary body density hcenter).val) = _
  rw [_p2mH64]
open _root_.P2M8f8f5b7e renaming h61 → _p2mH61
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h65 (security : ℕ) (density : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.BodyChannelEvaluation.bodyTensorMass security 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density) =
      _root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile (_root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security density)) := by
  funext word
  have hresponse : _root_.AFT.TensorChannel.apply 1 (fun _ => _root_.CurrentAFT.BodyChannelEvaluation.bodyDensityChannel security) (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density) word =
      _root_.CurrentAFT.BodyChannelEvaluation.bodyDensityChannel security density (word 0) := rfl
  rw [_root_.CurrentAFT.BodyChannelEvaluation.bodyTensorMass, hresponse, _root_.CurrentAFT.PrimaryTensorInverse.referenceWeight, Fin.prod_univ_one, _p2mH60]
  unfold _root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile
  field_simp [(_root_.CurrentAFT.ActualControls.primaryReference_positive security (word 0)).ne']
open _root_.P2M8f8f5b7e renaming h65 → _p2mH65
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h62 (security order : ℕ) (horder : 1 ≤ order) (density : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ)
    (hcenter : ∑ color, (_root_.CurrentAFT.ActualControls.bodyReference security).weight color * density color = 0) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.BackgroundFamilies.bodyFamily (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder density hcenter) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security density))) := by
  have h := _p2mH61 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security)
    (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm_homogeneous security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm_homogeneous security) order horder density hcenter
  rw [_p2mH66, _p2mH65, _p2mH48] at h
  exact h
open _root_.P2M8f8f5b7e renaming h62 → _p2mH62
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h70 {State : Type*} [Fintype State] (law : _root_.AFT.FiniteDist State) (safe : State → Prop)
    (hzero : ∀ state, ¬safe state → law.weight state = 0) (density : State → ℝ) :
    _root_.CurrentAFT.BodyChannelEvaluation.weightedEmbedding (_root_.CurrentAFT.ActualControls.supportedLaw law safe hzero) Subtype.val (fun point => density point.val) =
      fun state => law.weight state * density state := by
  funext output
  calc
    _ = (_root_.CurrentAFT.ActualControls.supportedLaw law safe hzero).expectation (fun point => density point.val * (Pi.single point.val (1 : ℝ) : State → ℝ) output) := by
      unfold _root_.CurrentAFT.BodyChannelEvaluation.weightedEmbedding _root_.AFT.FiniteDist.expectation
      apply Finset.sum_congr rfl
      intro point _
      ring
    _ = law.expectation (fun point => density point * (Pi.single point (1 : ℝ) : State → ℝ) output) := _root_.CurrentAFT.ActualControls.supportedLaw_expectation law safe hzero
      (fun point : State => density point * (Pi.single point (1 : ℝ) : State → ℝ) output)
    _ = _ := by simp [_root_.AFT.FiniteDist.expectation, Pi.single_apply]
open _root_.P2M8f8f5b7e renaming h70 → _p2mH70
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h68 (security : ℕ) (density : _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    _root_.CurrentAFT.BodyChannelEvaluation.safeMass security (fun point => density point.val) = fun color => (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight color * density color := by
  unfold _root_.CurrentAFT.BodyChannelEvaluation.safeMass _root_.CurrentAFT.ActualControls.bodyReference
  exact _p2mH70 _ _ _ density
open _root_.P2M8f8f5b7e renaming h68 → _p2mH68
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h59 (security : ℕ) (density : _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (fun color => (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight color * density color) =
      _root_.CurrentAFT.BackgroundCertificates.bodyLeadingResponse security density := by
  unfold _root_.CurrentAFT.MarkedPairLeading.bodyConvolution _root_.CurrentAFT.BackgroundCertificates.bodyLeadingResponse
  rfl
open _root_.P2M8f8f5b7e renaming h59 → _p2mH59
end
open _root_.P2M8f8f5b7e renaming h59 → _p2mH59
open _root_.P2M8f8f5b7e renaming h60 → _p2mH60
open _root_.P2M8f8f5b7e renaming h61 → _p2mH61
open _root_.P2M8f8f5b7e renaming h62 → _p2mH62
open _root_.P2M8f8f5b7e renaming h63 → _p2mH63
open _root_.P2M8f8f5b7e renaming h64 → _p2mH64
open _root_.P2M8f8f5b7e renaming h65 → _p2mH65
open _root_.P2M8f8f5b7e renaming h66 → _p2mH66
open _root_.P2M8f8f5b7e renaming h67 → _p2mH67
open _root_.P2M8f8f5b7e renaming h68 → _p2mH68
open _root_.P2M8f8f5b7e renaming h69 → _p2mH69
open _root_.P2M8f8f5b7e renaming h70 → _p2mH70
end CurrentAFT.BodyChannelEvaluation
open _root_.P2M8f8f5b7e renaming h59 → _p2mH59
open _root_.P2M8f8f5b7e renaming h60 → _p2mH60
open _root_.P2M8f8f5b7e renaming h61 → _p2mH61
open _root_.P2M8f8f5b7e renaming h62 → _p2mH62
open _root_.P2M8f8f5b7e renaming h63 → _p2mH63
open _root_.P2M8f8f5b7e renaming h64 → _p2mH64
open _root_.P2M8f8f5b7e renaming h65 → _p2mH65
open _root_.P2M8f8f5b7e renaming h66 → _p2mH66
open _root_.P2M8f8f5b7e renaming h67 → _p2mH67
open _root_.P2M8f8f5b7e renaming h68 → _p2mH68
open _root_.P2M8f8f5b7e renaming h69 → _p2mH69
open _root_.P2M8f8f5b7e renaming h70 → _p2mH70
end
open _root_.P2M8f8f5b7e renaming h59 → _p2mH59
open _root_.P2M8f8f5b7e renaming h60 → _p2mH60
open _root_.P2M8f8f5b7e renaming h61 → _p2mH61
open _root_.P2M8f8f5b7e renaming h62 → _p2mH62
open _root_.P2M8f8f5b7e renaming h63 → _p2mH63
open _root_.P2M8f8f5b7e renaming h64 → _p2mH64
open _root_.P2M8f8f5b7e renaming h65 → _p2mH65
open _root_.P2M8f8f5b7e renaming h66 → _p2mH66
open _root_.P2M8f8f5b7e renaming h67 → _p2mH67
open _root_.P2M8f8f5b7e renaming h68 → _p2mH68
open _root_.P2M8f8f5b7e renaming h69 → _p2mH69
open _root_.P2M8f8f5b7e renaming h70 → _p2mH70
namespace CurrentAFT.BodyChannelEvaluation
end CurrentAFT.BodyChannelEvaluation
namespace CurrentAFT.BodyChannelEvaluation.bodyDensityChannel
end CurrentAFT.BodyChannelEvaluation.bodyDensityChannel
namespace CurrentAFT.BodyChannelEvaluation.bodyTensorMass
end CurrentAFT.BodyChannelEvaluation.bodyTensorMass
namespace CurrentAFT.BodyChannelEvaluation.safeMass
end CurrentAFT.BodyChannelEvaluation.safeMass
section
namespace CurrentAFT.BackgroundAtomEvaluation
open AFT ControlCoordinates DiffuseProfiles ProposalPrimary ActualControls
  BackgroundFamilies BackgroundEvaluation BackgroundFirstEvaluation BodyChannelEvaluation
  BackgroundCertificates BackgroundTranslations FringeCertificate
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
attribute [local instance] _root_.CurrentAFT.BackgroundAtomEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h38 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.BackgroundFamilies.freeCertificate security order horder) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm
        ((_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security).weight - _root_.CurrentAFT.FringeCertificate.uniformProfile security)) := by
  unfold _root_.CurrentAFT.BackgroundFamilies.freeCertificate
  rw [map_add, _p2mH50, _p2mH62, _p2mH68, _p2mH59]
  rw [← map_add, ← map_add, _p2mH41]
open _root_.P2M8f8f5b7e renaming h38 → _p2mH38
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h39 (security order : ℕ) (horder : 1 ≤ order) (shift : ℤ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.BackgroundFamilies.translationCertificate security order horder shift) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm
        (_root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile security (_root_.CurrentAFT.BackgroundTranslations.shiftedSafeLaw security shift).weight - _root_.CurrentAFT.FringeCertificate.uniformProfile security)) := by
  unfold _root_.CurrentAFT.BackgroundFamilies.translationCertificate
  rw [map_add, map_add, _p2mH50, _p2mH50, _p2mH62,
    _p2mH68, _p2mH59]
  rw [← map_add, ← map_add, ← map_add, ← map_add]
  apply congrArg (_root_.CurrentAFT.TruncatedOutput.quotientMap order)
  apply congrArg _root_.AFT.RepresentedPolynomial.profileForm
  rw [add_right_comm, _p2mH58]
open _root_.P2M8f8f5b7e renaming h39 → _p2mH39
end
open _root_.P2M8f8f5b7e renaming h38 → _p2mH38
open _root_.P2M8f8f5b7e renaming h39 → _p2mH39
end CurrentAFT.BackgroundAtomEvaluation
open _root_.P2M8f8f5b7e renaming h38 → _p2mH38
open _root_.P2M8f8f5b7e renaming h39 → _p2mH39
end
open _root_.P2M8f8f5b7e renaming h38 → _p2mH38
open _root_.P2M8f8f5b7e renaming h39 → _p2mH39
namespace CurrentAFT.BackgroundAtomEvaluation
end CurrentAFT.BackgroundAtomEvaluation
section
namespace CurrentAFT.BodyPairEvaluation
open AFT ControlCoordinates ControlProduct LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies BackgroundEvaluation BodyChannelEvaluation
  PairCertificateFamilies DiffusePair DiffusePairBounds LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution DiffusePair.safePairProfile
attribute [local instance] _root_.CurrentAFT.BodyPairEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h75 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Body → Body → ℝ) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms (_root_.CurrentAFT.PairCertificateFamilies.pairBodyRaw density) =
      _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial body bodyForms 2 (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile density) := by
  simp only [_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial, _root_.CurrentAFT.PairCertificateFamilies.pairBodyRaw, _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial, _root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile,
    Fin.prod_univ_zero, Fintype.sum_unique, one_mul]
open _root_.P2M8f8f5b7e renaming h75 → _p2mH75
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h72 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (hprimary : ∀ color, (primaryForms color).IsHomogeneous 1) (hbody : ∀ center, (bodyForms center).IsHomogeneous 1)
    (order : ℕ) (horder : 2 ≤ order) (density : Body → Body → ℝ)
    (hfirst : ∀ second, ∑ first, body.weight first * density first second = 0)
    (hsecond : ∀ first, ∑ second, body.weight second * density first second = 0)
    (hsymmetric : ∀ first second, density first second = density second first) :
    _root_.CurrentAFT.LeadingEvaluation.familyHom primary body primaryForms bodyForms hprimary hbody order
      (Pi.single (_root_.CurrentAFT.PairCertificateFamilies.bodyPairArity order horder) (_root_.CurrentAFT.PairCertificateFamilies.bodyPairKernel primary body density hfirst hsecond)) =
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial body bodyForms 2 (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile density)) := by
  change _root_.CurrentAFT.LeadingEvaluation.familyLinear primary body primaryForms bodyForms order (Pi.single _ _) = _
  rw [_root_.CurrentAFT.LeadingEvaluation.familyLinear_single]
  change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms
    (_root_.CurrentAFT.PairCertificateFamilies.bodyPairKernel primary body density hfirst hsecond).val) = _
  rw [_p2mH186 _ _ _ _ _ hsymmetric, _p2mH75]
open _root_.P2M8f8f5b7e renaming h72 → _p2mH72
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h74 (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.PairCertificateFamilies.diffuseBodyCertificate security order horder scalar) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security 2
        (_root_.CurrentAFT.BodyChannelEvaluation.bodyTensorMass security 2 (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile (_root_.CurrentAFT.DiffusePairBounds.bodyPairDensity security scalar)))) := by
  have h := _p2mH72 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
    (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm_homogeneous security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm_homogeneous security)
    order horder (_root_.CurrentAFT.DiffusePairBounds.bodyPairDensity security scalar) (_root_.CurrentAFT.DiffusePairBounds.bodyPairDensity_centered_first security scalar)
    (_root_.CurrentAFT.DiffusePairBounds.bodyPairDensity_centered_second security scalar) (_p2mH105 security scalar)
  rw [_p2mH66] at h
  exact h
open _root_.P2M8f8f5b7e renaming h74 → _p2mH74
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h73 (security : ℕ) (density : _root_.CurrentAFT.ActualControls.SafePalette security → _root_.CurrentAFT.ActualControls.SafePalette security → ℝ)
    (word : Fin 2 → _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.BodyChannelEvaluation.bodyTensorMass security 2 (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile density) word =
      _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security (fun first =>
        _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security (density first)) (word 1))) (word 0) := by
  have hresponse : _root_.AFT.TensorChannel.apply 2 (fun _ => _root_.CurrentAFT.BodyChannelEvaluation.bodyDensityChannel security)
      (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile density) word = _root_.CurrentAFT.BodyChannelEvaluation.bodyDensityChannel security
        (fun first => _root_.CurrentAFT.BodyChannelEvaluation.bodyDensityChannel security (density first) (word 1)) (word 0) := rfl
  have hinside : (fun first => _root_.CurrentAFT.BodyChannelEvaluation.bodyDensityChannel security (density first) (word 1)) =
      ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight (word 1))⁻¹ • (fun first =>
        _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security (density first)) (word 1)) := by
    funext first
    simp only [_p2mH60, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [_root_.CurrentAFT.BodyChannelEvaluation.bodyTensorMass, hresponse, _root_.CurrentAFT.PrimaryTensorInverse.referenceWeight, Fin.prod_univ_two, hinside,
    map_smul, Pi.smul_apply, smul_eq_mul, _p2mH60]
  field_simp [(_root_.CurrentAFT.ActualControls.primaryReference_positive security (word 0)).ne', (_root_.CurrentAFT.ActualControls.primaryReference_positive security (word 1)).ne']
open _root_.P2M8f8f5b7e renaming h73 → _p2mH73
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h79 {State : Type*} [Fintype State] (law : _root_.AFT.FiniteDist State)
    (safe : State → Prop) (hzero : ∀ state, ¬safe state → law.weight state = 0)
    (density : {state // safe state} → ℝ) (output : State) :
    _root_.CurrentAFT.BodyChannelEvaluation.weightedEmbedding (_root_.CurrentAFT.ActualControls.supportedLaw law safe hzero) Subtype.val density output =
      if h : safe output then law.weight output * density ⟨output, h⟩ else 0 := by
  let extension : State → ℝ := fun state => if h : safe state then density ⟨state, h⟩ else 0
  have hext : (fun point : {state // safe state} => extension point.val) = density := by
    funext point
    exact dif_pos point.property
  have h := congrFun (_p2mH70 law safe hzero extension) output
  rw [hext] at h
  rw [h]
  by_cases hs : safe output
  · simp only [extension, dif_pos hs]
  · simp only [extension, dif_neg hs, mul_zero]
open _root_.P2M8f8f5b7e renaming h79 → _p2mH79
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h76 (security : ℕ) (density : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) (output : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.BodyChannelEvaluation.safeMass security density output = if h : _root_.CurrentAFT.InwardAnchor.SafeColor security output then
      (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight output * density ⟨output, h⟩ else 0 := by
  unfold _root_.CurrentAFT.BodyChannelEvaluation.safeMass _root_.CurrentAFT.ActualControls.bodyReference
  exact _p2mH79 _ _ _ density output
open _root_.P2M8f8f5b7e renaming h76 → _p2mH76
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h78 (security : ℕ) (scalar : ℤ) (first : _root_.CurrentAFT.ActualControls.SafePalette security) :
    _root_.CurrentAFT.BodyChannelEvaluation.safeMass security (_root_.CurrentAFT.DiffusePairBounds.bodyPairDensity security scalar first) =
      ((_root_.CurrentAFT.ActualControls.bodyReference security).weight first)⁻¹ • _root_.CurrentAFT.DiffusePair.safePairProfile security scalar first.val := by
  funext second
  rw [_p2mH76]
  by_cases hs : _root_.CurrentAFT.InwardAnchor.SafeColor security second
  · rw [dif_pos hs]
    have h := _p2mH104 security scalar first ⟨second, hs⟩
    have hw : (_root_.CurrentAFT.ActualControls.bodyReference security).weight ⟨second, hs⟩ = (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight second := by
      unfold _root_.CurrentAFT.ActualControls.bodyReference
      rfl
    rw [hw] at h
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp [(_root_.CurrentAFT.ActualControls.bodyReference_positive security first).ne']
    nlinarith [h]
  · rw [dif_neg hs]
    simp only [Pi.smul_apply, smul_eq_mul,
      _root_.CurrentAFT.DiffusePair.safePairProfile_zero_outside security scalar first.val second (Or.inr hs), mul_zero]
open _root_.P2M8f8f5b7e renaming h78 → _p2mH78
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h77 (security : ℕ) (scalar : ℤ) (second : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.BodyChannelEvaluation.safeMass security (fun first => _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security
      (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security (_root_.CurrentAFT.DiffusePairBounds.bodyPairDensity security scalar first)) second) =
      fun first => _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.DiffusePair.safePairProfile security scalar first) second := by
  funext first
  rw [_p2mH76]
  by_cases hs : _root_.CurrentAFT.InwardAnchor.SafeColor security first
  · rw [dif_pos hs, _p2mH78, map_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    have hw : (_root_.CurrentAFT.ActualControls.bodyReference security).weight ⟨first, hs⟩ = (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight first := by
      unfold _root_.CurrentAFT.ActualControls.bodyReference
      rfl
    rw [← hw]
    field_simp [(_root_.CurrentAFT.ActualControls.bodyReference_positive security ⟨first, hs⟩).ne']
  · rw [dif_neg hs]
    have hrow : _root_.CurrentAFT.DiffusePair.safePairProfile security scalar first = 0 := by
      funext color
      exact _root_.CurrentAFT.DiffusePair.safePairProfile_zero_outside security scalar first color (Or.inl hs)
    rw [hrow, map_zero, Pi.zero_apply]
open _root_.P2M8f8f5b7e renaming h77 → _p2mH77
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h71 (security : ℕ) (scalar : ℤ) (word : Fin 2 → _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.BodyChannelEvaluation.bodyTensorMass security 2 (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile (_root_.CurrentAFT.DiffusePairBounds.bodyPairDensity security scalar)) word =
      _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (fun first =>
        _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.DiffusePair.safePairProfile security scalar first) (word 1)) (word 0) := by
  rw [_p2mH73, _p2mH77]
open _root_.P2M8f8f5b7e renaming h71 → _p2mH71
end
open _root_.P2M8f8f5b7e renaming h71 → _p2mH71
open _root_.P2M8f8f5b7e renaming h72 → _p2mH72
open _root_.P2M8f8f5b7e renaming h73 → _p2mH73
open _root_.P2M8f8f5b7e renaming h74 → _p2mH74
open _root_.P2M8f8f5b7e renaming h75 → _p2mH75
open _root_.P2M8f8f5b7e renaming h76 → _p2mH76
open _root_.P2M8f8f5b7e renaming h77 → _p2mH77
open _root_.P2M8f8f5b7e renaming h78 → _p2mH78
open _root_.P2M8f8f5b7e renaming h79 → _p2mH79
end CurrentAFT.BodyPairEvaluation
open _root_.P2M8f8f5b7e renaming h71 → _p2mH71
open _root_.P2M8f8f5b7e renaming h72 → _p2mH72
open _root_.P2M8f8f5b7e renaming h73 → _p2mH73
open _root_.P2M8f8f5b7e renaming h74 → _p2mH74
open _root_.P2M8f8f5b7e renaming h75 → _p2mH75
open _root_.P2M8f8f5b7e renaming h76 → _p2mH76
open _root_.P2M8f8f5b7e renaming h77 → _p2mH77
open _root_.P2M8f8f5b7e renaming h78 → _p2mH78
open _root_.P2M8f8f5b7e renaming h79 → _p2mH79
end
open _root_.P2M8f8f5b7e renaming h71 → _p2mH71
open _root_.P2M8f8f5b7e renaming h72 → _p2mH72
open _root_.P2M8f8f5b7e renaming h73 → _p2mH73
open _root_.P2M8f8f5b7e renaming h74 → _p2mH74
open _root_.P2M8f8f5b7e renaming h75 → _p2mH75
open _root_.P2M8f8f5b7e renaming h76 → _p2mH76
open _root_.P2M8f8f5b7e renaming h77 → _p2mH77
open _root_.P2M8f8f5b7e renaming h78 → _p2mH78
open _root_.P2M8f8f5b7e renaming h79 → _p2mH79
namespace CurrentAFT.BodyPairEvaluation
end CurrentAFT.BodyPairEvaluation
section
namespace CurrentAFT.DiffusePairEvaluation
open AFT AFT.SafeConvolution AFT.SafePair ControlCoordinates LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls PrimaryMassFamilies PairReindex PairSmoothing
  BackgroundEvaluation BodyChannelEvaluation BodyPairEvaluation DiffusePair DiffusePairBounds FringeCertificate
  DiffusePairResidual DiffusePairResidualRates DiffusePairCertificates LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution DiffusePair.safePairProfile DiffusePairResidual.seedProfile
  DiffusePairResidual.rootResiduePairLaw BodyChannelEvaluation.bodyTensorMass DiffusePairBounds.bodyPairDensity
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h110 (modulus : ℕ) [NeZero modulus] (shift : ZMod modulus) (color : Fin modulus) :
    (_root_.CurrentAFT.DiffusePairEvaluation.cyclicEquiv modulus shift).symm color =
        (ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) color - shift) := by
  cases modulus with
  | zero => exact Fin.elim0 color
  | succ modulus =>
      simp [_root_.CurrentAFT.DiffusePairEvaluation.cyclicEquiv, ZMod.finEquiv, Equiv.symm_trans_apply, Equiv.addRight_symm,
        Equiv.coe_addRight, sub_eq_add_neg]
open _root_.P2M8f8f5b7e renaming h110 → _p2mH110
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h112 (modulus : ℕ) [NeZero modulus]
    {Seed : Type*} [Fintype Seed] (law : _root_.AFT.FiniteDist Seed) (shift : Seed → ZMod modulus)
    (profile : Fin modulus → Fin modulus → ℝ) (first second : Fin modulus) :
    (∑ left, law.weight left * ∑ right, law.weight right *
      profile ((ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) first - shift left))
        ((ZMod.finEquiv modulus).symm ((ZMod.finEquiv modulus) second - shift right))) =
      _root_.AFT.SafeConvolution.convolution ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).weight
        (fun color => _root_.CurrentAFT.PairReindex.liftPair (ZMod.finEquiv modulus).toEquiv profile color.1 color.2)
        ((ZMod.finEquiv modulus) first, (ZMod.finEquiv modulus) second) := by
  change _ = ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).expectation
    (fun displacement => _root_.CurrentAFT.PairReindex.liftPair (ZMod.finEquiv modulus).toEquiv profile
      ((ZMod.finEquiv modulus) first - displacement.1) ((ZMod.finEquiv modulus) second - displacement.2))
  rw [_root_.AFT.FiniteDist.expectation_map, _root_.AFT.FiniteDist.expectation_prod]
  rfl
open _root_.P2M8f8f5b7e renaming h112 → _p2mH112
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h109 (modulus : ℕ) [NeZero modulus]
    {Seed : Type*} [Fintype Seed] (law : _root_.AFT.FiniteDist Seed) (shift : Seed → ZMod modulus)
    (profile : Fin modulus → Fin modulus → ℝ) (first second : Fin modulus) :
    (∑ left, law.weight left * ∑ right, law.weight right *
      profile ((_root_.CurrentAFT.DiffusePairEvaluation.cyclicEquiv modulus (shift left)).symm first)
        ((_root_.CurrentAFT.DiffusePairEvaluation.cyclicEquiv modulus (shift right)).symm second)) =
      _root_.AFT.SafeConvolution.convolution ((law.prod law).map (fun seed => (shift seed.1, shift seed.2))).weight
        (fun color => _root_.CurrentAFT.PairReindex.liftPair (ZMod.finEquiv modulus).toEquiv profile color.1 color.2)
        ((ZMod.finEquiv modulus) first, (ZMod.finEquiv modulus) second) := by
  simp only [_p2mH110]
  exact _p2mH112 modulus law shift profile first second
open _root_.P2M8f8f5b7e renaming h109 → _p2mH109
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h108 (security : ℕ) (scalar : ℤ) (first second : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (fun left =>
      _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.DiffusePair.safePairProfile security scalar left) second) first =
      _root_.CurrentAFT.DiffusePairResidualRates.pullbackPair (_root_.CurrentAFT.Parameters.modulus security)
        (_root_.AFT.SafeConvolution.convolution (_root_.CurrentAFT.DiffusePairResidual.rootResiduePairLaw security).weight (_root_.CurrentAFT.DiffusePairResidual.seedProfile security scalar)) first second := by
  unfold _root_.CurrentAFT.MarkedPairLeading.bodyConvolution _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile
  unfold _root_.CurrentAFT.DiffusePairResidualRates.pullbackPair _root_.CurrentAFT.DiffusePairResidual.rootResiduePairLaw _root_.CurrentAFT.DiffusePair.rootPairLaw _root_.CurrentAFT.DiffusePair.rootPairShift _root_.CurrentAFT.DiffusePairResidual.seedProfile
  simp only [LinearMap.coe_mk, AddHom.coe_mk, _root_.CurrentAFT.ProposalPrimary.shiftEquiv]
  change (∑ left, (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).weight left * ∑ right, (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).weight right *
    _root_.CurrentAFT.DiffusePair.safePairProfile security scalar
      ((_root_.CurrentAFT.DiffusePairEvaluation.cyclicEquiv (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.DiffuseProfiles.actualBlur security left)).symm first)
      ((_root_.CurrentAFT.DiffusePairEvaluation.cyclicEquiv (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.DiffuseProfiles.actualBlur security right)).symm second)) = _
  exact _p2mH109 (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security)
    (fun seed => (_root_.CurrentAFT.DiffuseProfiles.actualBlur security seed : ZMod (_root_.CurrentAFT.Parameters.modulus security)))
    (_root_.CurrentAFT.DiffusePair.safePairProfile security scalar) first second
open _root_.P2M8f8f5b7e renaming h108 → _p2mH108
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h107 (security : ℕ) (scalar : ℤ) :
    _root_.CurrentAFT.BodyChannelEvaluation.bodyTensorMass security 2 (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile (_root_.CurrentAFT.DiffusePairBounds.bodyPairDensity security scalar)) =
      _root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile (_root_.CurrentAFT.DiffusePairResidualRates.pullbackPair (_root_.CurrentAFT.Parameters.modulus security)
        (_root_.AFT.SafeConvolution.convolution (_root_.CurrentAFT.DiffusePairResidual.rootResiduePairLaw security).weight (_root_.CurrentAFT.DiffusePairResidual.seedProfile security scalar))) := by
  funext word
  exact (_p2mH71 security scalar word).trans
    (_p2mH108 security scalar (word 0) (word 1))
open _root_.P2M8f8f5b7e renaming h107 → _p2mH107
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h113 (security degree : ℕ)
    (first second : (Fin degree → _root_.CurrentAFT.ActualControls.Palette security) → ℝ) :
    _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security degree (first + second) =
      _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security degree first + _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security degree second := by
  unfold _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial
  simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
open _root_.P2M8f8f5b7e renaming h113 → _p2mH113
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h114 (modulus : ℕ) [NeZero modulus]
    (profile : Fin modulus → Fin modulus → ℝ) :
    _root_.CurrentAFT.DiffusePairResidualRates.pullbackPair modulus (_root_.AFT.SafeConvolution.uniformCanonical (fun color =>
      _root_.CurrentAFT.PairReindex.liftPair (ZMod.finEquiv modulus).toEquiv profile color.1 color.2)) =
        _root_.AFT.SafePair.canonicalPair (fun _ => 1 / (modulus : ℝ)) profile := by
  have h := _root_.CurrentAFT.PairReindex.canonicalPair_uniform_lift (ZMod.finEquiv modulus).toEquiv profile
  simp only [ZMod.card, Fintype.card_fin] at h
  funext first second
  change _root_.AFT.SafePair.canonicalPair (fun _ => 1 / (Fintype.card (ZMod modulus) : ℝ))
      (_root_.CurrentAFT.PairReindex.liftPair (ZMod.finEquiv modulus).toEquiv profile)
      ((ZMod.finEquiv modulus) first) ((ZMod.finEquiv modulus) second) = _
  simp only [ZMod.card]
  rw [h]
  simp only [_root_.CurrentAFT.PairReindex.liftPair]
  cases modulus with
  | zero => exact Fin.elim0 first
  | succ modulus => rfl
open _root_.P2M8f8f5b7e renaming h114 → _p2mH114
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h111 (security order : ℕ) (horder : 2 ≤ order) (scalar : ℤ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.DiffusePairCertificates.diffuseCertificate security order horder scalar) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security 2
        (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile (_root_.AFT.SafePair.canonicalPair (_root_.CurrentAFT.FringeCertificate.uniformProfile security) (_root_.CurrentAFT.DiffusePair.pairProfile security scalar)))) := by
  unfold _root_.CurrentAFT.DiffusePairCertificates.diffuseCertificate
  rw [map_add, _p2mH74, _p2mH44,
    _p2mH107, ← map_add, ← _p2mH113]
  congr 2
  funext word
  change _root_.CurrentAFT.DiffusePairResidualRates.pullbackPair (_root_.CurrentAFT.Parameters.modulus security)
      (_root_.AFT.SafeConvolution.convolution (_root_.CurrentAFT.DiffusePairResidual.rootResiduePairLaw security).weight (_root_.CurrentAFT.DiffusePairResidual.seedProfile security scalar)) (word 0) (word 1) +
      _root_.CurrentAFT.DiffusePairResidualRates.pullbackPair (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.DiffusePairResidual.residualProfile security scalar) (word 0) (word 1) = _
  rw [← _p2mH116, _p2mH115]
  unfold _root_.CurrentAFT.DiffusePairResidual.originalProfile _root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile _root_.CurrentAFT.FringeCertificate.uniformProfile
  simpa only [one_div] using
    congrFun (congrFun (_p2mH114 (_root_.CurrentAFT.Parameters.modulus security) (_root_.CurrentAFT.DiffusePair.pairProfile security scalar)) (word 0)) (word 1)
open _root_.P2M8f8f5b7e renaming h111 → _p2mH111
end
open _root_.P2M8f8f5b7e renaming h107 → _p2mH107
open _root_.P2M8f8f5b7e renaming h108 → _p2mH108
open _root_.P2M8f8f5b7e renaming h109 → _p2mH109
open _root_.P2M8f8f5b7e renaming h110 → _p2mH110
open _root_.P2M8f8f5b7e renaming h111 → _p2mH111
open _root_.P2M8f8f5b7e renaming h112 → _p2mH112
open _root_.P2M8f8f5b7e renaming h113 → _p2mH113
open _root_.P2M8f8f5b7e renaming h114 → _p2mH114
end CurrentAFT.DiffusePairEvaluation
open _root_.P2M8f8f5b7e renaming h107 → _p2mH107
open _root_.P2M8f8f5b7e renaming h108 → _p2mH108
open _root_.P2M8f8f5b7e renaming h109 → _p2mH109
open _root_.P2M8f8f5b7e renaming h110 → _p2mH110
open _root_.P2M8f8f5b7e renaming h111 → _p2mH111
open _root_.P2M8f8f5b7e renaming h112 → _p2mH112
open _root_.P2M8f8f5b7e renaming h113 → _p2mH113
open _root_.P2M8f8f5b7e renaming h114 → _p2mH114
end
open _root_.P2M8f8f5b7e renaming h107 → _p2mH107
open _root_.P2M8f8f5b7e renaming h108 → _p2mH108
open _root_.P2M8f8f5b7e renaming h109 → _p2mH109
open _root_.P2M8f8f5b7e renaming h110 → _p2mH110
open _root_.P2M8f8f5b7e renaming h111 → _p2mH111
open _root_.P2M8f8f5b7e renaming h112 → _p2mH112
open _root_.P2M8f8f5b7e renaming h113 → _p2mH113
open _root_.P2M8f8f5b7e renaming h114 → _p2mH114
section
namespace CurrentAFT.MixedPairEvaluation
open AFT ControlCoordinates LeadingEvaluation DiffuseProfiles ProposalPrimary ActualControls
  PrimaryTensorInverse PrimaryMassFamilies BackgroundEvaluation BodyChannelEvaluation BodyPairEvaluation
  MarkedPairCertificates MarkedPairLeading MarkedPairSeed LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution MarkedPairSeed.seedDensity
attribute [local instance] _root_.CurrentAFT.MixedPairEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h166 {Color Variable : Type*} [Fintype Color] (law : _root_.AFT.FiniteDist Color)
    (forms : Color → MvPolynomial Variable ℝ) (density : Color → ℝ) :
    _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial law forms 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density) =
      ∑ point, MvPolynomial.C (law.weight point * density point) * forms point := by
  unfold _root_.CurrentAFT.LocalCoefficientEvaluation.densityPolynomial _root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile
  simp only [Fin.prod_univ_one]
  exact ((Equiv.funUnique (Fin 1) Color).symm.sum_comp
    (fun word : Fin 1 → Color => MvPolynomial.C (law.weight (word 0) * density (word 0)) * forms (word 0))).symm
open _root_.P2M8f8f5b7e renaming h166 → _p2mH166
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h174 {Input Output : Type*} [Fintype Input] [Fintype Output]
    (input : _root_.AFT.FiniteDist Input) (output : _root_.AFT.FiniteDist Output) (hpositive : ∀ point, input.weight point ≠ 0)
    (channel : (Input → ℝ) →ₗ[ℝ] (Output → ℝ)) (density : Input → ℝ) :
    (∑ point, MvPolynomial.C (input.weight point * density point) *
      _root_.CurrentAFT.BodyChannelEvaluation.rectangularForm input.weight output.weight channel point) =
        _root_.AFT.RepresentedPolynomial.profileForm (fun point => output.weight point * channel density point) := by
  have h := _p2mH67 input output hpositive channel 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density)
  have hchannel : _root_.AFT.TensorChannel.apply 1 (fun _ => channel) (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile density) = _root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile (channel density) := rfl
  rw [hchannel, _p2mH166, _p2mH166] at h
  exact h
open _root_.P2M8f8f5b7e renaming h174 → _p2mH174
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h171 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (density : Primary → Body → ℝ)
    (hprimary : ∀ center, primary.expectation (fun color => density color center) = 0)
    (hbody : ∀ color, body.expectation (density color) = 0) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms (_root_.CurrentAFT.MarkedPairCertificates.mixedKernel primary body density hprimary hbody).val =
      _root_.CurrentAFT.MixedPairEvaluation.mixedPolynomial primary body primaryForms bodyForms density := by
  unfold _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial _root_.CurrentAFT.MarkedPairCertificates.mixedKernel _root_.CurrentAFT.MixedPairEvaluation.mixedPolynomial
  simp only [Fin.prod_univ_one]
  rw [← (Equiv.funUnique (Fin 1) Primary).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const]
  apply Finset.sum_congr rfl
  intro color _
  calc
    _ = ∑ center, MvPolynomial.C (primary.weight color * body.weight center * density color center) *
        (primaryForms color * bodyForms center) := by
      simpa only [Equiv.funUnique_symm_apply, uniqueElim_const] using
        ((Equiv.funUnique (Fin 1) Body).symm.sum_comp (fun centers : Fin 1 → Body =>
          MvPolynomial.C (primary.weight color * body.weight (centers 0) * density color (centers 0)) *
            (primaryForms color * bodyForms (centers 0)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro center _
      ring
open _root_.P2M8f8f5b7e renaming h171 → _p2mH171
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h173 {Primary Body Output : Type*}
    [Fintype Primary] [Fintype Body] [Fintype Output]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (output : _root_.AFT.FiniteDist Output)
    (hpositive : ∀ point, primary.weight point ≠ 0)
    (channel : (Primary → ℝ) →ₗ[ℝ] (Output → ℝ)) (bodyForms : Body → MvPolynomial Output ℝ)
    (density : Primary → Body → ℝ) :
    _root_.CurrentAFT.MixedPairEvaluation.mixedPolynomial primary body (_root_.CurrentAFT.BodyChannelEvaluation.rectangularForm primary.weight output.weight channel) bodyForms density =
      ∑ value, MvPolynomial.C (output.weight value) * MvPolynomial.X value *
        (∑ center, MvPolynomial.C (body.weight center * channel (fun color => density color center) value) * bodyForms center) := by
  have hgroup : _root_.CurrentAFT.MixedPairEvaluation.mixedPolynomial primary body (_root_.CurrentAFT.BodyChannelEvaluation.rectangularForm primary.weight output.weight channel) bodyForms density =
      ∑ center, MvPolynomial.C (body.weight center) * bodyForms center *
        (∑ color, MvPolynomial.C (primary.weight color * density color center) *
          _root_.CurrentAFT.BodyChannelEvaluation.rectangularForm primary.weight output.weight channel color) := by
    unfold _root_.CurrentAFT.MixedPairEvaluation.mixedPolynomial
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum, map_mul]
    apply Finset.sum_congr rfl
    intro center _
    apply Finset.sum_congr rfl
    intro color _
    ring
  rw [hgroup]
  simp_rw [_p2mH174 primary output hpositive channel]
  simp only [_root_.AFT.RepresentedPolynomial.profileForm_apply, Finset.mul_sum, map_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro value _
  apply Finset.sum_congr rfl
  intro center _
  ring
open _root_.P2M8f8f5b7e renaming h173 → _p2mH173
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h165 (security : ℕ) (density : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    (∑ point, MvPolynomial.C ((_root_.CurrentAFT.ActualControls.bodyReference security).weight point * density point) * _root_.CurrentAFT.BackgroundEvaluation.bodyForm security point) =
      _root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security density)) := by
  simp_rw [_p2mH63]
  rw [_p2mH174 _ _ (fun point => (_root_.CurrentAFT.ActualControls.bodyReference_positive security point).ne')]
  congr 1
  funext output
  rw [_p2mH60]
  field_simp [(_root_.CurrentAFT.ActualControls.primaryReference_positive security output).ne']
open _root_.P2M8f8f5b7e renaming h165 → _p2mH165
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h172 (security : ℕ) (scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security) :
    _root_.CurrentAFT.MixedPairEvaluation.mixedPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security)
      (_root_.CurrentAFT.MarkedPairCertificates.inverseDensity security scalar) =
      ∑ primary, MvPolynomial.C ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary) * MvPolynomial.X primary *
        _root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security (_root_.CurrentAFT.MarkedPairSeed.seedDensity security scalar primary))) := by
  have hforms : _root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security = _root_.CurrentAFT.BodyChannelEvaluation.rectangularForm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight
      (_root_.CurrentAFT.PrimaryTensorInverse.densityResponse security) := rfl
  rw [hforms, _p2mH173 _ _ _ (fun point => (_root_.CurrentAFT.ActualControls.primaryReference_positive security point).ne')]
  simp_rw [_p2mH157, _p2mH165]
open _root_.P2M8f8f5b7e renaming h172 → _p2mH172
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h175 (security : ℕ) (scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security)
    (primary : _root_.CurrentAFT.ActualControls.Palette security) :
    (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary • _root_.CurrentAFT.BodyChannelEvaluation.safeMass security (_root_.CurrentAFT.MarkedPairSeed.seedDensity security scalar primary) =
      _root_.CurrentAFT.MarkedPairLeading.seedProfile security scalar primary := by
  funext center
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [_p2mH76]
  by_cases hs : _root_.CurrentAFT.InwardAnchor.SafeColor security center
  · rw [dif_pos hs]
    have hw : (_root_.CurrentAFT.ActualControls.bodyReference security).weight ⟨center, hs⟩ = (_root_.CurrentAFT.ProposalPrimary.centerLaw security).weight center := by
      unfold _root_.CurrentAFT.ActualControls.bodyReference
      rfl
    rw [← hw, ← mul_assoc]
    exact _p2mH163 security scalar primary ⟨center, hs⟩
  · rw [dif_neg hs, mul_zero, _p2mH164 security scalar primary center hs]
open _root_.P2M8f8f5b7e renaming h175 → _p2mH175
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h169 (security : ℕ) (profile : _root_.CurrentAFT.ActualControls.Palette security → _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security 2 (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile profile) =
      ∑ first, ∑ second, MvPolynomial.C (profile first second) * MvPolynomial.X first * MvPolynomial.X second := by
  unfold _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial _root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile
  simp only [Fin.prod_univ_two]
  calc
    _ = ∑ first, ∑ second, MvPolynomial.C (profile first second) * (MvPolynomial.X first * MvPolynomial.X second) := by
      simpa only [Fintype.sum_prod_type, finTwoArrowEquiv, Equiv.coe_fn_symm_mk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one] using
        ((finTwoArrowEquiv (_root_.CurrentAFT.ActualControls.Palette security)).symm.sum_comp
          (fun word : Fin 2 → _root_.CurrentAFT.ActualControls.Palette security =>
            MvPolynomial.C (profile (word 0) (word 1)) * (MvPolynomial.X (word 0) * MvPolynomial.X (word 1)))).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      ring
open _root_.P2M8f8f5b7e renaming h169 → _p2mH169
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h168 (security : ℕ) (scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security) :
    _root_.CurrentAFT.MixedPairEvaluation.mixedPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security)
      (_root_.CurrentAFT.MarkedPairCertificates.inverseDensity security scalar) = _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security 2
        (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile (fun primary output => _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.MarkedPairLeading.seedProfile security scalar primary) output)) := by
  rw [_p2mH172, _p2mH169]
  apply Finset.sum_congr rfl
  intro primary _
  have hprofile : _root_.AFT.RepresentedPolynomial.profileForm
      (_root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.MarkedPairLeading.seedProfile security scalar primary)) =
      MvPolynomial.C ((_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary) * _root_.AFT.RepresentedPolynomial.profileForm
        (_root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security (_root_.CurrentAFT.MarkedPairSeed.seedDensity security scalar primary))) := by
    rw [← _p2mH175 security scalar primary, map_smul, map_smul, MvPolynomial.smul_eq_C_mul]
  have hsum : (∑ output, MvPolynomial.C (_root_.CurrentAFT.MarkedPairLeading.bodyConvolution security
      (_root_.CurrentAFT.MarkedPairLeading.seedProfile security scalar primary) output) * MvPolynomial.X primary * MvPolynomial.X output) =
      MvPolynomial.X primary * _root_.AFT.RepresentedPolynomial.profileForm
        (_root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.MarkedPairLeading.seedProfile security scalar primary)) := by
    rw [_root_.AFT.RepresentedPolynomial.profileForm_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro output _
    ring
  rw [hsum, hprofile]
  ring
open _root_.P2M8f8f5b7e renaming h168 → _p2mH168
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h170 {Primary Body Variable : Type*} [Fintype Primary] [Fintype Body]
    (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body)
    (primaryForms : Primary → MvPolynomial Variable ℝ) (bodyForms : Body → MvPolynomial Variable ℝ)
    (hprimaryForms : ∀ color, (primaryForms color).IsHomogeneous 1)
    (hbodyForms : ∀ center, (bodyForms center).IsHomogeneous 1)
    (order : ℕ) (horder : 2 ≤ order) (density : Primary → Body → ℝ)
    (hprimary : ∀ center, primary.expectation (fun color => density color center) = 0)
    (hbody : ∀ color, body.expectation (density color) = 0) :
    _root_.CurrentAFT.LeadingEvaluation.familyHom primary body primaryForms bodyForms hprimaryForms hbodyForms order
      (Pi.single (_root_.CurrentAFT.MarkedPairCertificates.mixedArity order horder) (_root_.CurrentAFT.MarkedPairCertificates.mixedKernel primary body density hprimary hbody)) =
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.MixedPairEvaluation.mixedPolynomial primary body primaryForms bodyForms density) := by
  change _root_.CurrentAFT.LeadingEvaluation.familyLinear primary body primaryForms bodyForms order (Pi.single _ _) = _
  rw [_root_.CurrentAFT.LeadingEvaluation.familyLinear_single]
  change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial primary body primaryForms bodyForms
    (_root_.CurrentAFT.MarkedPairCertificates.mixedKernel primary body density hprimary hbody).val) = _
  rw [_p2mH171]
open _root_.P2M8f8f5b7e renaming h170 → _p2mH170
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h167 (security order : ℕ) (horder : 2 ≤ order) (scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.MarkedPairCertificates.markedMixedCertificate security order horder scalar) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security 2 (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile
        (fun primary output => _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.MarkedPairLeading.seedProfile security scalar primary) output))) := by
  have h := _p2mH170 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
    (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm_homogeneous security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm_homogeneous security)
    order horder (_root_.CurrentAFT.MarkedPairCertificates.inverseDensity security scalar) (_root_.CurrentAFT.MarkedPairCertificates.inverseDensity_centered_primary security scalar)
    (_root_.CurrentAFT.MarkedPairCertificates.inverseDensity_centered_body security scalar)
  rw [_p2mH168] at h
  exact h
open _root_.P2M8f8f5b7e renaming h167 → _p2mH167
end
open _root_.P2M8f8f5b7e renaming h165 → _p2mH165
open _root_.P2M8f8f5b7e renaming h166 → _p2mH166
open _root_.P2M8f8f5b7e renaming h167 → _p2mH167
open _root_.P2M8f8f5b7e renaming h168 → _p2mH168
open _root_.P2M8f8f5b7e renaming h169 → _p2mH169
open _root_.P2M8f8f5b7e renaming h170 → _p2mH170
open _root_.P2M8f8f5b7e renaming h171 → _p2mH171
open _root_.P2M8f8f5b7e renaming h172 → _p2mH172
open _root_.P2M8f8f5b7e renaming h173 → _p2mH173
open _root_.P2M8f8f5b7e renaming h174 → _p2mH174
open _root_.P2M8f8f5b7e renaming h175 → _p2mH175
end CurrentAFT.MixedPairEvaluation
open _root_.P2M8f8f5b7e renaming h165 → _p2mH165
open _root_.P2M8f8f5b7e renaming h166 → _p2mH166
open _root_.P2M8f8f5b7e renaming h167 → _p2mH167
open _root_.P2M8f8f5b7e renaming h168 → _p2mH168
open _root_.P2M8f8f5b7e renaming h169 → _p2mH169
open _root_.P2M8f8f5b7e renaming h170 → _p2mH170
open _root_.P2M8f8f5b7e renaming h171 → _p2mH171
open _root_.P2M8f8f5b7e renaming h172 → _p2mH172
open _root_.P2M8f8f5b7e renaming h173 → _p2mH173
open _root_.P2M8f8f5b7e renaming h174 → _p2mH174
open _root_.P2M8f8f5b7e renaming h175 → _p2mH175
end
open _root_.P2M8f8f5b7e renaming h165 → _p2mH165
open _root_.P2M8f8f5b7e renaming h166 → _p2mH166
open _root_.P2M8f8f5b7e renaming h167 → _p2mH167
open _root_.P2M8f8f5b7e renaming h168 → _p2mH168
open _root_.P2M8f8f5b7e renaming h169 → _p2mH169
open _root_.P2M8f8f5b7e renaming h170 → _p2mH170
open _root_.P2M8f8f5b7e renaming h171 → _p2mH171
open _root_.P2M8f8f5b7e renaming h172 → _p2mH172
open _root_.P2M8f8f5b7e renaming h173 → _p2mH173
open _root_.P2M8f8f5b7e renaming h174 → _p2mH174
open _root_.P2M8f8f5b7e renaming h175 → _p2mH175
namespace CurrentAFT.ActualPairBridge
end CurrentAFT.ActualPairBridge
namespace CurrentAFT.DiffusePair.pairBlur
end CurrentAFT.DiffusePair.pairBlur
namespace CurrentAFT.DiffusePair.pairSeedLaw
end CurrentAFT.DiffusePair.pairSeedLaw
namespace CurrentAFT.DiffusePair.pairStart
end CurrentAFT.DiffusePair.pairStart
namespace CurrentAFT.DiffusePairEvaluation
end CurrentAFT.DiffusePairEvaluation
namespace CurrentAFT.DiffusePairEvaluation.cyclicEquiv
end CurrentAFT.DiffusePairEvaluation.cyclicEquiv
namespace CurrentAFT.DiffusePairResidualRates
end CurrentAFT.DiffusePairResidualRates
namespace CurrentAFT.DiffusePairResidualRates.pullbackPair
end CurrentAFT.DiffusePairResidualRates.pullbackPair
namespace CurrentAFT.LocalReferenceEnergy.signedDiffusePair
end CurrentAFT.LocalReferenceEnergy.signedDiffusePair
namespace CurrentAFT.LocalReferenceEnergy.signedMarkedPair
end CurrentAFT.LocalReferenceEnergy.signedMarkedPair
namespace CurrentAFT.MixedPairEvaluation
end CurrentAFT.MixedPairEvaluation
namespace CurrentAFT.ProposalPrimary.shiftEquiv
end CurrentAFT.ProposalPrimary.shiftEquiv
namespace CurrentAFT.ProposalSymmetry.directionLaw
end CurrentAFT.ProposalSymmetry.directionLaw
section
namespace CurrentAFT.PairQuadraticEvaluation
open AFT AFT.SafePair AFT.RepresentedPolynomial ControlCoordinates LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls PrimaryMassFamilies BackgroundFamilies
  BackgroundEvaluation BackgroundFirstEvaluation BackgroundAtomEvaluation MixedPairEvaluation
  DiffusePairEvaluation PairQuadraticFamilies LocalCoefficientFamily MarkedPairLeading
  LocalReferenceEnergy ActualPairBridge FringeCertificate
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw ActualControls.bodyReference
  MarkedPairLeading.bodyConvolution
attribute [local instance] _root_.CurrentAFT.PairQuadraticEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h191 (security : ℕ)
    (profile : _root_.CurrentAFT.ActualControls.Palette security → _root_.CurrentAFT.ActualControls.Palette security → ℝ) :
    _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security 2 (_root_.CurrentAFT.PrimaryMassFamilies.pairWordProfile profile) = _root_.AFT.RepresentedPolynomial.pairForm profile := _p2mH169 security profile
open _root_.P2M8f8f5b7e renaming h191 → _p2mH191
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h190 (security order : ℕ) (horder : 2 ≤ order) (scalar : _root_.CurrentAFT.MarkedPairSeed.Scalar security) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.PairQuadraticFamilies.markedPairCertificate security order horder scalar) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.pairForm (_root_.AFT.SafePair.canonicalPair (_root_.CurrentAFT.FringeCertificate.uniformProfile security)
        (fun primary output => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight primary * (_root_.CurrentAFT.LocalReferenceEnergy.markedCompanionAt security primary scalar).weight output))) := by
  unfold _root_.CurrentAFT.PairQuadraticFamilies.markedPairCertificate
  change _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.MarkedPairCertificates.markedMixedCertificate security order horder scalar +
    _root_.CurrentAFT.PrimaryDeviationCertificate.certificate security order (by omega) * _root_.CurrentAFT.BackgroundFamilies.freeCertificate security order (by omega)) = _
  rw [map_add, map_mul, _p2mH167, _p2mH46, _p2mH38,
    _p2mH191, _p2mH48, ← map_mul, ← map_add]
  rw [← _p2mH8, ← _p2mH4]
  apply congrArg (_root_.CurrentAFT.TruncatedOutput.quotientMap order)
  apply congrArg _root_.AFT.RepresentedPolynomial.pairForm
  exact (_p2mH160 security scalar).symm
open _root_.P2M8f8f5b7e renaming h190 → _p2mH190
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h188 {Color : Type*} [Fintype Color] (reference : Color → ℝ)
    (first second : Color → Color → ℝ) (left right : ℝ) :
    _root_.AFT.SafePair.canonicalPair reference (left • first + right • second) =
      left • _root_.AFT.SafePair.canonicalPair reference first + right • _root_.AFT.SafePair.canonicalPair reference second := by
  funext a b
  simp only [_root_.AFT.SafePair.canonicalPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  ring
open _root_.P2M8f8f5b7e renaming h188 → _p2mH188
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h189 (security : ℕ) (scalar : _root_.CurrentAFT.LocalReferenceEnergy.Scalar security)
    (first second : _root_.CurrentAFT.ActualControls.Palette security) :
    (_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).weight (first, second) =
      _root_.CurrentAFT.LocalReferenceEnergy.signedPairAt security scalar (fun _ => 1) first second := by
  simp only [_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw, _root_.AFT.FiniteDist.mix_weight, _root_.CurrentAFT.LocalReferenceEnergy.signedPairAt, mul_one]
open _root_.P2M8f8f5b7e renaming h189 → _p2mH189
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h192 (security order : ℕ) (horder : 2 ≤ order) (scalar : _root_.CurrentAFT.LocalReferenceEnergy.Scalar security) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.PairQuadraticFamilies.pairQuadraticCertificate security order horder scalar) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.pairForm (_root_.AFT.SafePair.canonicalPair (_root_.CurrentAFT.FringeCertificate.uniformProfile security)
        (fun first second => (_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).weight (first, second)))) := by
  unfold _root_.CurrentAFT.PairQuadraticFamilies.pairQuadraticCertificate
  rw [map_add, map_smul, map_smul, _p2mH111, _p2mH190,
    _p2mH191, ← map_smul, ← map_smul, ← map_add]
  simp_rw [MvPolynomial.smul_eq_C_mul]
  rw [← _p2mH6, ← _p2mH6, ← _p2mH4, ← _p2mH188]
  apply congrArg (_root_.CurrentAFT.TruncatedOutput.quotientMap order)
  apply congrArg _root_.AFT.RepresentedPolynomial.pairForm
  apply congrArg (_root_.AFT.SafePair.canonicalPair (_root_.CurrentAFT.FringeCertificate.uniformProfile security))
  funext first second
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_assoc] using
    ((_p2mH189 security scalar first second).trans
      (_p2mH28 security scalar first second)).symm
open _root_.P2M8f8f5b7e renaming h192 → _p2mH192
end
open _root_.P2M8f8f5b7e renaming h188 → _p2mH188
open _root_.P2M8f8f5b7e renaming h189 → _p2mH189
open _root_.P2M8f8f5b7e renaming h190 → _p2mH190
open _root_.P2M8f8f5b7e renaming h191 → _p2mH191
open _root_.P2M8f8f5b7e renaming h192 → _p2mH192
end CurrentAFT.PairQuadraticEvaluation
open _root_.P2M8f8f5b7e renaming h188 → _p2mH188
open _root_.P2M8f8f5b7e renaming h189 → _p2mH189
open _root_.P2M8f8f5b7e renaming h190 → _p2mH190
open _root_.P2M8f8f5b7e renaming h191 → _p2mH191
open _root_.P2M8f8f5b7e renaming h192 → _p2mH192
end
open _root_.P2M8f8f5b7e renaming h188 → _p2mH188
open _root_.P2M8f8f5b7e renaming h189 → _p2mH189
open _root_.P2M8f8f5b7e renaming h190 → _p2mH190
open _root_.P2M8f8f5b7e renaming h191 → _p2mH191
open _root_.P2M8f8f5b7e renaming h192 → _p2mH192
namespace CurrentAFT.HistogramMean
end CurrentAFT.HistogramMean
namespace CurrentAFT.HistogramMean.drift
end CurrentAFT.HistogramMean.drift
namespace CurrentAFT.HistogramMean.offBodyMean
end CurrentAFT.HistogramMean.offBodyMean
namespace CurrentAFT.HistogramMean.pair_histogram
end CurrentAFT.HistogramMean.pair_histogram
namespace CurrentAFT.HistogramMean.queueLaw
end CurrentAFT.HistogramMean.queueLaw
namespace CurrentAFT.LocalReferenceEnergy.signedPairAt
end CurrentAFT.LocalReferenceEnergy.signedPairAt
namespace CurrentAFT.NormalizedMeanAlgebra.normalizationScale
end CurrentAFT.NormalizedMeanAlgebra.normalizationScale
namespace CurrentAFT.PairQuadraticEvaluation
end CurrentAFT.PairQuadraticEvaluation
namespace CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw
end CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw
section
namespace CurrentAFT.LegPolynomialEvaluation
open AFT AFT.RepresentedPolynomial ControlCoordinates GradedControlAlgebra LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls PrimaryMassFamilies BackgroundFamilies
  BackgroundEvaluation BackgroundFirstEvaluation BackgroundAtomEvaluation PairQuadraticEvaluation
  BackgroundCertificates BackgroundTranslations BackgroundLinear LocalCoefficientFamily
  LocalReferenceEnergy FirstHistogram FringeCertificate BodyRootAverages
  ConditionalPairMean LegBackgroundFamilies HistogramMean
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference
attribute [local instance] _root_.CurrentAFT.LegPolynomialEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h137 (security : ℕ) (scalar : _root_.CurrentAFT.LegPolynomialEvaluation.Scalar security) (output : _root_.CurrentAFT.ActualControls.Palette security) :
    (_root_.CurrentAFT.LegPolynomialEvaluation.attachmentLaw security scalar).weight output =
      _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile security (_root_.CurrentAFT.BackgroundTranslations.shiftedSafeLaw security scalar.val).weight output := by
  rw [_root_.CurrentAFT.LegPolynomialEvaluation.attachmentLaw, _p2mH83]
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.map_equiv_weight, _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile]
open _root_.P2M8f8f5b7e renaming h137 → _p2mH137
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h136 (security : ℕ) :
    (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).mix (_root_.CurrentAFT.LegPolynomialEvaluation.attachmentLaw security) = _root_.CurrentAFT.ProposalPrimary.bodyLaw security true := by
  unfold _root_.CurrentAFT.LegPolynomialEvaluation.attachmentLaw
  rw [← _p2mH82]
  exact _p2mH80 security
open _root_.P2M8f8f5b7e renaming h136 → _p2mH136
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h135 (security : ℕ) :
    (∑ scalar, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar • _root_.CurrentAFT.LegPolynomialEvaluation.attachmentDeviation security scalar) =
      (_root_.CurrentAFT.ProposalPrimary.bodyLaw security true).weight - _root_.CurrentAFT.FringeCertificate.uniformProfile security := by
  funext output
  have h := congrArg (fun law : _root_.AFT.FiniteDist (_root_.CurrentAFT.ActualControls.Palette security) => law.weight output)
    (_p2mH136 security)
  simp only [_root_.AFT.FiniteDist.mix_weight] at h
  simp only [_root_.CurrentAFT.LegPolynomialEvaluation.attachmentDeviation, Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, _root_.AFT.FiniteDist.sum_one, one_mul]
  rw [h]
open _root_.P2M8f8f5b7e renaming h135 → _p2mH135
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h148 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.BackgroundLinear.meanTranslation security order horder) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm ((_root_.CurrentAFT.ProposalPrimary.bodyLaw security true).weight - _root_.CurrentAFT.FringeCertificate.uniformProfile security)) := by
  have hprofile (scalar : _root_.CurrentAFT.LegPolynomialEvaluation.Scalar security) :
      _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile security (_root_.CurrentAFT.BackgroundTranslations.shiftedSafeLaw security scalar.val).weight - _root_.CurrentAFT.FringeCertificate.uniformProfile security =
        _root_.CurrentAFT.LegPolynomialEvaluation.attachmentDeviation security scalar := by
    funext output
    simp only [_root_.CurrentAFT.LegPolynomialEvaluation.attachmentDeviation, Pi.sub_apply, _p2mH137]
  unfold _root_.CurrentAFT.BackgroundLinear.meanTranslation
  simp only [map_sum, map_smul, _p2mH39]
  change (∑ scalar : _root_.CurrentAFT.LegPolynomialEvaluation.Scalar security, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar •
    _root_.CurrentAFT.LegPolynomialEvaluation.profileEvaluation security order
      (_root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile security (_root_.CurrentAFT.BackgroundTranslations.shiftedSafeLaw security scalar.val).weight - _root_.CurrentAFT.FringeCertificate.uniformProfile security)) =
    _root_.CurrentAFT.LegPolynomialEvaluation.profileEvaluation security order _
  simp_rw [← map_smul]
  rw [← map_sum]
  simp_rw [hprofile]
  rw [_p2mH135]
open _root_.P2M8f8f5b7e renaming h148 → _p2mH148
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h145 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.BackgroundLinear.legLinearCertificate security order horder) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm
        (fun output => _root_.CurrentAFT.FirstHistogram.legFirstMean security output - 3 * _root_.CurrentAFT.FringeCertificate.uniformProfile security output)) := by
  unfold _root_.CurrentAFT.BackgroundLinear.legLinearCertificate
  rw [map_smul, map_add, map_smul, map_smul, _p2mH38, _p2mH148]
  change -(_root_.CurrentAFT.Parameters.legCount security : ℝ)⁻¹ •
      (_root_.CurrentAFT.ProposalPrimary.freeMass security • _root_.CurrentAFT.LegPolynomialEvaluation.profileEvaluation security order _ +
        (_root_.CurrentAFT.Parameters.modulus security : ℝ) • _root_.CurrentAFT.LegPolynomialEvaluation.profileEvaluation security order _) =
    _root_.CurrentAFT.LegPolynomialEvaluation.profileEvaluation security order _
  rw [← map_smul, ← map_smul, ← map_add, ← map_smul]
  congr 1
  funext output
  have hbaseline := _p2mH122 security output
  have hlegs := (_root_.CurrentAFT.BackgroundLinear.legCount_pos security).ne'
  simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  field_simp [hlegs]
  nlinarith [hbaseline]
open _root_.P2M8f8f5b7e renaming h145 → _p2mH145
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h142 (security : ℕ) (scalar : _root_.CurrentAFT.LegPolynomialEvaluation.Scalar security) (output : _root_.CurrentAFT.ActualControls.Palette security) :
    (∑ second, (_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).weight (output, second)) +
        (∑ first, (_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).weight (first, output)) = _root_.CurrentAFT.ConditionalPairMean.pairMean security scalar output := by
  rw [_p2mH88]
  simp only [_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw, _root_.AFT.FiniteDist.mix_weight, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> rw [Finset.sum_comm]
open _root_.P2M8f8f5b7e renaming h142 → _p2mH142
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h143 (security : ℕ) (scalar : _root_.CurrentAFT.LegPolynomialEvaluation.Scalar security) :
    (∑ first, ∑ second, (_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).weight (first, second)) = 1 := by
  simpa only [Fintype.sum_prod_type] using (_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).sum_one
open _root_.P2M8f8f5b7e renaming h143 → _p2mH143
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h144 (security order : ℕ) (horder : 1 ≤ order) (scalar : _root_.CurrentAFT.LegPolynomialEvaluation.Scalar security) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.ConditionalPairLinear.certificate security order horder scalar) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.ConditionalPairMean.centeredMean security scalar)) := by
  rw [_p2mH43]
  change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LocalCoefficientFamily.massPolynomial security 1 (_root_.CurrentAFT.PrimaryMassFamilies.oneWordProfile (_root_.CurrentAFT.ConditionalPairMean.centeredMean security scalar))) = _
  rw [_p2mH48]
open _root_.P2M8f8f5b7e renaming h144 → _p2mH144
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h141 (security order : ℕ) (horder : 2 ≤ order) (scalar : _root_.CurrentAFT.LegPolynomialEvaluation.Scalar security) :
    _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.pairGenerating (_root_.CurrentAFT.FringeCertificate.uniformProfile security)
      (fun first second => (_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).weight (first, second))) =
      1 + _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.ConditionalPairLinear.certificate security order (by omega) scalar) +
        _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.PairQuadraticFamilies.pairQuadraticCertificate security order horder scalar) := by
  rw [_p2mH9, _p2mH143, map_one]
  have hprofile : (fun output =>
      (∑ second, (_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).weight (output, second)) +
      (∑ first, (_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).weight (first, output)) -
      2 * 1 * _root_.CurrentAFT.FringeCertificate.uniformProfile security output) = _root_.CurrentAFT.ConditionalPairMean.centeredMean security scalar := by
    funext output
    rw [_p2mH142]
    simp only [_root_.CurrentAFT.ConditionalPairMean.centeredMean, mul_one]
  rw [hprofile, map_add, map_add, map_one, _p2mH144, _p2mH192]
  ring
open _root_.P2M8f8f5b7e renaming h141 → _p2mH141
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h139 (security : ℕ) (scalar : _root_.CurrentAFT.LegPolynomialEvaluation.Scalar security) :
    _root_.CurrentAFT.LegPolynomialEvaluation.conditionalLegGenerating security scalar =
      _root_.AFT.RepresentedPolynomial.pairGenerating (_root_.CurrentAFT.FringeCertificate.uniformProfile security) (fun first second => (_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).weight (first, second)) *
        (1 + _root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.LegPolynomialEvaluation.attachmentDeviation security scalar)) := by
  rw [_root_.CurrentAFT.LegPolynomialEvaluation.conditionalLegGenerating, _p2mH17,
    _p2mH15 _ _ (_root_.CurrentAFT.LegPolynomialEvaluation.attachmentLaw security scalar).sum_one]
  rfl
open _root_.P2M8f8f5b7e renaming h139 → _p2mH139
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h149 (security order : ℕ) (horder : 1 ≤ order) (scalar : _root_.CurrentAFT.LegPolynomialEvaluation.Scalar security) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.BackgroundFamilies.translationCertificate security order horder scalar.val) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.LegPolynomialEvaluation.attachmentDeviation security scalar)) := by
  rw [_p2mH39]
  apply congrArg (_root_.CurrentAFT.TruncatedOutput.quotientMap order)
  apply congrArg _root_.AFT.RepresentedPolynomial.profileForm
  funext output
  simp only [_root_.CurrentAFT.LegPolynomialEvaluation.attachmentDeviation, Pi.sub_apply, _p2mH137]
open _root_.P2M8f8f5b7e renaming h149 → _p2mH149
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h140 (security order : ℕ) (horder : 2 ≤ order) (scalar : _root_.CurrentAFT.LegPolynomialEvaluation.Scalar security) :
    _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LegPolynomialEvaluation.conditionalLegGenerating security scalar) =
      1 + _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
        (_root_.CurrentAFT.ConditionalPairLinear.certificate security order (by omega) scalar +
          _root_.CurrentAFT.BackgroundFamilies.translationCertificate security order (by omega) scalar.val) +
        _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.LegBackgroundFamilies.conditionalQuadratic security order horder scalar) +
        _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.LegBackgroundFamilies.conditionalCubic security order horder scalar) := by
  rw [_p2mH139, map_mul, map_add, map_one,
    _p2mH141 security order horder scalar,
    ← _p2mH149 security order (by omega) scalar]
  unfold _root_.CurrentAFT.LegBackgroundFamilies.conditionalQuadratic _root_.CurrentAFT.LegBackgroundFamilies.conditionalCubic
  simp only [map_add, map_mul]
  ring
open _root_.P2M8f8f5b7e renaming h140 → _p2mH140
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h146 (security : ℕ) :
    (∑ scalar, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar •
      (_root_.CurrentAFT.ConditionalPairMean.centeredMean security scalar + _root_.CurrentAFT.LegPolynomialEvaluation.attachmentDeviation security scalar)) =
      fun output => _root_.CurrentAFT.FirstHistogram.legFirstMean security output - 3 * _root_.CurrentAFT.FringeCertificate.uniformProfile security output := by
  funext output
  have hatt := congrFun (_p2mH135 security) output
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at hatt
  simp only [Finset.sum_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add,
    Finset.sum_add_distrib]
  rw [hatt]
  simp only [_root_.CurrentAFT.ConditionalPairMean.centeredMean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    _root_.AFT.FiniteDist.sum_one, one_mul]
  have hleg := _p2mH134 security output
  unfold _root_.CurrentAFT.HistogramMean.offBodyMean _root_.AFT.FiniteDist.expectation at hleg
  nlinarith [hleg]
open _root_.P2M8f8f5b7e renaming h146 → _p2mH146
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h147 (security order : ℕ) (horder : 1 ≤ order) :
    (∑ scalar, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar • _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.ConditionalPairLinear.certificate security order horder scalar +
        _root_.CurrentAFT.BackgroundFamilies.translationCertificate security order horder scalar.val)) =
      _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.BackgroundLinear.legLinearCertificate security order horder) := by
  simp only [map_add, _p2mH144, _p2mH149]
  rw [_p2mH145]
  change (∑ scalar : _root_.CurrentAFT.LegPolynomialEvaluation.Scalar security, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar •
    (_root_.CurrentAFT.LegPolynomialEvaluation.profileEvaluation security order (_root_.CurrentAFT.ConditionalPairMean.centeredMean security scalar) +
      _root_.CurrentAFT.LegPolynomialEvaluation.profileEvaluation security order (_root_.CurrentAFT.LegPolynomialEvaluation.attachmentDeviation security scalar))) = _root_.CurrentAFT.LegPolynomialEvaluation.profileEvaluation security order _
  simp_rw [← map_add]
  simp_rw [← map_smul]
  rw [← map_sum, _p2mH146]
open _root_.P2M8f8f5b7e renaming h147 → _p2mH147
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h138 (security order : ℕ) (horder : 2 ≤ order) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (1 + _root_.CurrentAFT.LegBackgroundFamilies.completeLegAtom security order horder) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LegPolynomialEvaluation.legGenerating security) := by
  unfold _root_.CurrentAFT.LegPolynomialEvaluation.legGenerating
  simp only [map_sum, map_smul, _p2mH140 security order horder, smul_add,
    Finset.sum_add_distrib]
  rw [← Finset.sum_smul, _root_.AFT.FiniteDist.sum_one, one_smul, _p2mH147]
  unfold _root_.CurrentAFT.LegBackgroundFamilies.completeLegAtom _root_.CurrentAFT.LegBackgroundFamilies.legQuadratic _root_.CurrentAFT.LegBackgroundFamilies.legCubic
  simp only [map_add, map_one, map_sum, map_smul]
  ring
open _root_.P2M8f8f5b7e renaming h138 → _p2mH138
end
open _root_.P2M8f8f5b7e renaming h135 → _p2mH135
open _root_.P2M8f8f5b7e renaming h136 → _p2mH136
open _root_.P2M8f8f5b7e renaming h137 → _p2mH137
open _root_.P2M8f8f5b7e renaming h138 → _p2mH138
open _root_.P2M8f8f5b7e renaming h139 → _p2mH139
open _root_.P2M8f8f5b7e renaming h140 → _p2mH140
open _root_.P2M8f8f5b7e renaming h141 → _p2mH141
open _root_.P2M8f8f5b7e renaming h142 → _p2mH142
open _root_.P2M8f8f5b7e renaming h143 → _p2mH143
open _root_.P2M8f8f5b7e renaming h144 → _p2mH144
open _root_.P2M8f8f5b7e renaming h145 → _p2mH145
open _root_.P2M8f8f5b7e renaming h146 → _p2mH146
open _root_.P2M8f8f5b7e renaming h147 → _p2mH147
open _root_.P2M8f8f5b7e renaming h148 → _p2mH148
open _root_.P2M8f8f5b7e renaming h149 → _p2mH149
end CurrentAFT.LegPolynomialEvaluation
open _root_.P2M8f8f5b7e renaming h135 → _p2mH135
open _root_.P2M8f8f5b7e renaming h136 → _p2mH136
open _root_.P2M8f8f5b7e renaming h137 → _p2mH137
open _root_.P2M8f8f5b7e renaming h138 → _p2mH138
open _root_.P2M8f8f5b7e renaming h139 → _p2mH139
open _root_.P2M8f8f5b7e renaming h140 → _p2mH140
open _root_.P2M8f8f5b7e renaming h141 → _p2mH141
open _root_.P2M8f8f5b7e renaming h142 → _p2mH142
open _root_.P2M8f8f5b7e renaming h143 → _p2mH143
open _root_.P2M8f8f5b7e renaming h144 → _p2mH144
open _root_.P2M8f8f5b7e renaming h145 → _p2mH145
open _root_.P2M8f8f5b7e renaming h146 → _p2mH146
open _root_.P2M8f8f5b7e renaming h147 → _p2mH147
open _root_.P2M8f8f5b7e renaming h148 → _p2mH148
open _root_.P2M8f8f5b7e renaming h149 → _p2mH149
end
open _root_.P2M8f8f5b7e renaming h135 → _p2mH135
open _root_.P2M8f8f5b7e renaming h136 → _p2mH136
open _root_.P2M8f8f5b7e renaming h137 → _p2mH137
open _root_.P2M8f8f5b7e renaming h138 → _p2mH138
open _root_.P2M8f8f5b7e renaming h139 → _p2mH139
open _root_.P2M8f8f5b7e renaming h140 → _p2mH140
open _root_.P2M8f8f5b7e renaming h141 → _p2mH141
open _root_.P2M8f8f5b7e renaming h142 → _p2mH142
open _root_.P2M8f8f5b7e renaming h143 → _p2mH143
open _root_.P2M8f8f5b7e renaming h144 → _p2mH144
open _root_.P2M8f8f5b7e renaming h145 → _p2mH145
open _root_.P2M8f8f5b7e renaming h146 → _p2mH146
open _root_.P2M8f8f5b7e renaming h147 → _p2mH147
open _root_.P2M8f8f5b7e renaming h148 → _p2mH148
open _root_.P2M8f8f5b7e renaming h149 → _p2mH149
namespace CurrentAFT.LegBackgroundFamilies
end CurrentAFT.LegBackgroundFamilies
namespace CurrentAFT.LegBackgroundFamilies.completeLegAtom
end CurrentAFT.LegBackgroundFamilies.completeLegAtom
namespace CurrentAFT.LegPolynomialEvaluation
end CurrentAFT.LegPolynomialEvaluation
namespace CurrentAFT.LegPolynomialEvaluation.attachmentDeviation
end CurrentAFT.LegPolynomialEvaluation.attachmentDeviation
namespace CurrentAFT.LegPolynomialEvaluation.attachmentLaw
end CurrentAFT.LegPolynomialEvaluation.attachmentLaw
namespace CurrentAFT.LegPolynomialEvaluation.conditionalLegGenerating
end CurrentAFT.LegPolynomialEvaluation.conditionalLegGenerating
namespace CurrentAFT.PairQuadraticFamilies.pairQuadraticCertificate
end CurrentAFT.PairQuadraticFamilies.pairQuadraticCertificate
section
namespace CurrentAFT.BackgroundPolynomialEvaluation
open AFT AFT.RepresentedPolynomial ControlCoordinates GradedControlAlgebra LeadingEvaluation
  DiffuseProfiles ProposalPrimary ActualControls BackgroundFamilies BackgroundEvaluation
  BackgroundAtomEvaluation BackgroundCertificates BackgroundTranslations BackgroundPopulationBounds
  LocalReferenceEnergy PairQuadraticEvaluation LegPolynomialEvaluation BodyRootAverages
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount ProposalPrimary.primaryLaw ActualControls.bodyReference
attribute [local instance] _root_.CurrentAFT.BackgroundPolynomialEvaluation.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h53 {Choice State Variable : Type*} [Fintype Choice] [Fintype State]
    (choice : _root_.AFT.FiniteDist Choice) (laws : Choice → _root_.AFT.FiniteDist State)
    (factor : State → MvPolynomial Variable ℝ) :
    _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating (choice.mix laws) factor = ∑ index, choice.weight index • _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating (laws index) factor := by
  unfold _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating
  simp only [_root_.AFT.FiniteDist.mix_weight, map_sum, map_mul, Finset.sum_mul,
    MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro state _
  ring
open _root_.P2M8f8f5b7e renaming h53 → _p2mH53
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h54 {First Second Variable : Type*} [Fintype First] [Fintype Second]
    (first : _root_.AFT.FiniteDist First) (second : _root_.AFT.FiniteDist Second)
    (firstFactor : First → MvPolynomial Variable ℝ) (secondFactor : Second → MvPolynomial Variable ℝ) :
    _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating (first.prod second) (fun state => firstFactor state.1 * secondFactor state.2) =
      _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating first firstFactor * _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating second secondFactor := by
  unfold _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating
  simp only [Fintype.sum_prod_type, _root_.AFT.FiniteDist.prod_weight, map_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  ring
open _root_.P2M8f8f5b7e renaming h54 → _p2mH54
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h56 (security : ℕ) (shift : ℤ) (output : _root_.CurrentAFT.ActualControls.Palette security) :
    (_root_.CurrentAFT.BackgroundPolynomialEvaluation.queueLaw security shift).weight output = _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile security (_root_.CurrentAFT.BackgroundTranslations.shiftedSafeLaw security shift).weight output := by
  rw [_root_.CurrentAFT.BackgroundPolynomialEvaluation.queueLaw, _p2mH83]
  simp only [_root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.map_equiv_weight, _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile]
open _root_.P2M8f8f5b7e renaming h56 → _p2mH56
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h55 (security order : ℕ) (horder : 2 ≤ order) (queue : ℤ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queue) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.BackgroundPolynomialEvaluation.fixedQueueGenerating security queue) := by
  unfold _root_.CurrentAFT.ActualBackground.fixedQueueBackground _root_.CurrentAFT.BackgroundPolynomialEvaluation.fixedQueueGenerating
  simp only [map_mul, map_pow, map_add, map_one, _p2mH38,
    _p2mH39, _p2mH138 security order horder]
  rw [_p2mH15 _ _ (_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security).sum_one,
    _p2mH15 _ _ (_root_.CurrentAFT.BackgroundPolynomialEvaluation.queueLaw security queue).sum_one]
  have hqueue : (_root_.CurrentAFT.BackgroundPolynomialEvaluation.queueLaw security queue).weight = _root_.CurrentAFT.BackgroundCertificates.rootConvolutionProfile security (_root_.CurrentAFT.BackgroundTranslations.shiftedSafeLaw security queue).weight :=
    funext (_p2mH56 security queue)
  rw [hqueue]
  simp only [map_add, map_one]
open _root_.P2M8f8f5b7e renaming h55 → _p2mH55
end
open _root_.P2M8f8f5b7e renaming h53 → _p2mH53
open _root_.P2M8f8f5b7e renaming h54 → _p2mH54
open _root_.P2M8f8f5b7e renaming h55 → _p2mH55
open _root_.P2M8f8f5b7e renaming h56 → _p2mH56
end CurrentAFT.BackgroundPolynomialEvaluation
open _root_.P2M8f8f5b7e renaming h53 → _p2mH53
open _root_.P2M8f8f5b7e renaming h54 → _p2mH54
open _root_.P2M8f8f5b7e renaming h55 → _p2mH55
open _root_.P2M8f8f5b7e renaming h56 → _p2mH56
end
open _root_.P2M8f8f5b7e renaming h53 → _p2mH53
open _root_.P2M8f8f5b7e renaming h54 → _p2mH54
open _root_.P2M8f8f5b7e renaming h55 → _p2mH55
open _root_.P2M8f8f5b7e renaming h56 → _p2mH56
namespace CurrentAFT.BackgroundPolynomialEvaluation
end CurrentAFT.BackgroundPolynomialEvaluation
namespace CurrentAFT.BackgroundPolynomialEvaluation.legLaw
end CurrentAFT.BackgroundPolynomialEvaluation.legLaw
namespace CurrentAFT.BackgroundPolynomialEvaluation.queueLaw
end CurrentAFT.BackgroundPolynomialEvaluation.queueLaw
section
namespace CurrentAFT.BackgroundEndpointLaw
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  BackgroundPopulationBounds BackgroundPolynomialEvaluation BackgroundEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.legCount Parameters.bodySize
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h42 {Input Output Variable : Type*} [Fintype Input] [Fintype Output]
    (law : _root_.AFT.FiniteDist Input) (map : Input → Output) (factor : Output → MvPolynomial Variable ℝ) :
    _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating (law.map map) factor = _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating law (factor ∘ map) := by
  unfold _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating
  simp only [_root_.AFT.FiniteDist.map_weight, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro input _
  simp only [apply_ite, map_zero, ite_mul, zero_mul, eq_comm, Finset.sum_ite_eq', Finset.mem_univ, if_true, Function.comp_apply]
open _root_.P2M8f8f5b7e renaming h42 → _p2mH42
attribute [local instance] _root_.CurrentAFT.BackgroundEndpointLaw.classicalFinDecidableEq
end
open _root_.P2M8f8f5b7e renaming h42 → _p2mH42
end CurrentAFT.BackgroundEndpointLaw
open _root_.P2M8f8f5b7e renaming h42 → _p2mH42
end
open _root_.P2M8f8f5b7e renaming h42 → _p2mH42
namespace CurrentAFT.CycleSelections
end CurrentAFT.CycleSelections
namespace CurrentAFT.CycleSelections.averagedSelectedLaw
end CurrentAFT.CycleSelections.averagedSelectedLaw
namespace CurrentAFT.CycleSelections.currentRootTag
end CurrentAFT.CycleSelections.currentRootTag
namespace CurrentAFT.CycleSelections.selectionPermutation
end CurrentAFT.CycleSelections.selectionPermutation
namespace CurrentAFT.SupportedHoeffding
end CurrentAFT.SupportedHoeffding
section
namespace CurrentAFT.CycleRootExpansion
open AFT CycleSelections
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {Index Color Value : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
  [AddCommGroup Value] [Module ℝ Value]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h94 (reference : Index → _root_.AFT.FiniteDist Color)
    (word : Index → Color) (hword : ∀ index, 0 < (reference index).weight (word index)) :
    (_root_.AFT.FiniteDist.independent reference).weight word ≠ 0 :=
  (Finset.prod_pos (fun index _ => hword index)).ne'
open _root_.P2M8f8f5b7e renaming h94 → _p2mH94
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h98 (joint : _root_.AFT.FiniteDist (Index → Color))
    (reference : Index → _root_.AFT.FiniteDist Color)
    (hsupport : ∀ word, joint.weight word ≠ 0 → ∀ index,
      0 < (reference index).weight (word index)) :
    (∑ selected : Finset Index, _root_.CurrentAFT.CycleRootExpansion.componentResponse (Value := Value) joint reference selected) =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear joint := by
  cases Subsingleton.elim (inferInstance : DecidableEq Index) (Classical.decEq Index)
  apply LinearMap.ext
  intro test
  simp only [LinearMap.sum_apply, _root_.CurrentAFT.CycleRootExpansion.componentResponse, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.CurrentAFT.CycleRootExpansion.expectationLinear]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro word _
  rw [← Finset.sum_smul, ← Finset.mul_sum, _root_.AFT.Hoeffding.densityComponent_sum]
  by_cases hzero : joint.weight word = 0
  · simp [hzero]
  · rw [mul_div_cancel₀ _ (_p2mH94 reference word (hsupport word hzero))]
open _root_.P2M8f8f5b7e renaming h98 → _p2mH98
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h90 (joint : _root_.AFT.FiniteDist (Index → Color))
    (reference : Index → _root_.AFT.FiniteDist Color) :
    _root_.CurrentAFT.CycleRootExpansion.componentResponse (Value := Value) joint reference ∅ =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent reference) := by
  cases Subsingleton.elim (inferInstance : DecidableEq Index) (Classical.decEq Index)
  apply LinearMap.ext
  intro test
  simp only [_root_.CurrentAFT.CycleRootExpansion.componentResponse, _root_.CurrentAFT.CycleRootExpansion.expectationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.AFT.Hoeffding.densityComponent, Finset.prod_empty, mul_one, joint.sum_one]
open _root_.P2M8f8f5b7e renaming h90 → _p2mH90
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h97 (joint : _root_.AFT.FiniteDist (Index → Color))
    (reference : Index → _root_.AFT.FiniteDist Color) (index : Index)
    (hmarginal : joint.map (fun word => word index) = reference index)
    (word : Index → Color) (hword : (reference index).weight (word index) ≠ 0) :
    _root_.AFT.Hoeffding.densityComponent reference joint.weight {index} word = 0 := by
  cases Subsingleton.elim (inferInstance : DecidableEq Index) (Classical.decEq Index)
  have hmean := _root_.AFT.FiniteDist.expectation_map joint (fun input => input index)
    (fun color => _root_.CurrentAFT.CycleSelections.centeredRootAtom (reference index) color (word index))
  rw [hmarginal, _root_.CurrentAFT.CycleSelections.centeredRootAtom_mean_zero _ _ hword] at hmean
  simpa only [_root_.AFT.Hoeffding.densityComponent, Finset.prod_singleton,
    _root_.AFT.FiniteDist.expectation, Function.comp_apply, _root_.CurrentAFT.SupportedHoeffding.centeredRootAtom_eq] using hmean.symm
open _root_.P2M8f8f5b7e renaming h97 → _p2mH97
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h91 (joint : _root_.AFT.FiniteDist (Index → Color))
    (reference : Index → _root_.AFT.FiniteDist Color) (index : Index)
    (hmarginal : joint.map (fun word => word index) = reference index) :
    _root_.CurrentAFT.CycleRootExpansion.componentResponse (Value := Value) joint reference {index} = 0 := by
  apply LinearMap.ext
  intro test
  change (∑ word, ((_root_.AFT.FiniteDist.independent reference).weight word *
    _root_.AFT.Hoeffding.densityComponent reference joint.weight {index} word) • test word) = 0
  apply Finset.sum_eq_zero
  intro word _
  by_cases hzero : (reference index).weight (word index) = 0
  · have hproduct : (_root_.AFT.FiniteDist.independent reference).weight word = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ index) hzero
    rw [hproduct, zero_mul, zero_smul]
  · rw [_p2mH97 joint reference index hmarginal word hzero,
      mul_zero, zero_smul]
open _root_.P2M8f8f5b7e renaming h91 → _p2mH91
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h95 (joint : _root_.AFT.FiniteDist (Index → Color))
    (reference : Index → _root_.AFT.FiniteDist Color)
    (hsupport : ∀ word, joint.weight word ≠ 0 → ∀ index,
      0 < (reference index).weight (word index))
    (hmarginal : ∀ index, joint.map (fun word => word index) = reference index) :
    _root_.CurrentAFT.CycleRootExpansion.expectationLinear (Value := Value) joint -
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent reference) =
      ∑ selected ∈ (Finset.univ : Finset (Finset Index)).filter (fun selected => 2 ≤ selected.card),
        _root_.CurrentAFT.CycleRootExpansion.componentResponse joint reference selected := by
  rw [← _p2mH98 joint reference hsupport,
    ← _p2mH90 joint reference]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Finset Index))
    (_root_.CurrentAFT.CycleRootExpansion.componentResponse (Value := Value) joint reference) (Finset.mem_univ ∅)
  rw [← hsplit, add_sub_cancel_right]
  symm
  apply Finset.sum_subset
  · intro selected hselected
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
    intro hequal
    have hcard := (Finset.mem_filter.mp hselected).2
    rw [hequal, Finset.card_empty] at hcard
    omega
  · intro selected hselected hnot
    have hnonempty := (Finset.mem_erase.mp hselected).1
    have hcard : selected.card = 1 := by
      have hpositive := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hnonempty)
      have hsmall : ¬ 2 ≤ selected.card := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
      omega
    obtain ⟨index, rfl⟩ := Finset.card_eq_one.mp hcard
    exact _p2mH91 joint reference index (hmarginal index)
open _root_.P2M8f8f5b7e renaming h95 → _p2mH95
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h93 (joint : _root_.AFT.FiniteDist (Index → Color))
    (reference : Index → _root_.AFT.FiniteDist Color)
    (hmarginal : ∀ index, joint.map (fun word => word index) = reference index)
    (word : Index → Color) (hword : joint.weight word ≠ 0) (index : Index) :
    0 < (reference index).weight (word index) := by
  have hpositive : 0 < joint.weight word := lt_of_le_of_ne (joint.nonneg word) (Ne.symm hword)
  rw [← hmarginal index, _root_.AFT.FiniteDist.map_weight]
  apply hpositive.trans_le
  apply (Finset.single_le_sum (s := Finset.univ)
    (f := fun input => if input index = word index then joint.weight input else 0)
    (fun input _ => by split_ifs; exact joint.nonneg input; exact le_rfl)
    (Finset.mem_univ word)).trans'
  simp only [if_true, le_refl]
open _root_.P2M8f8f5b7e renaming h93 → _p2mH93
section Actual
attribute [local instance] _root_.CurrentAFT.CycleRootExpansion.currentModulusNeZero
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h92 (security : ℕ) : 2 ≤ _root_.CurrentAFT.Parameters.bodySize security := by
  have hbase := _root_.CurrentAFT.Parameters.base_ge_two security
  have hmod := (_root_.CurrentAFT.Parameters.modulus_spec security).2.two_le
  have hpower : 1 ≤ _root_.CurrentAFT.Parameters.base security ^ 96 := one_le_pow₀ (by omega)
  rw [_root_.CurrentAFT.Parameters.bodySize_eq]
  exact hmod.trans (by simpa using Nat.mul_le_mul_left (_root_.CurrentAFT.Parameters.modulus security) hpower)
open _root_.P2M8f8f5b7e renaming h92 → _p2mH92
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h96 (security : ℕ) (index : _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    (_root_.CurrentAFT.CycleRootExpansion.rootLaw security).map (fun roots => roots index) = _root_.CurrentAFT.CycleRootExpansion.rootReference security := by
  let labels : _root_.CurrentAFT.CycleSelections.Selection (_root_.CurrentAFT.Parameters.bodySize security) 1 :=
    ⟨fun _ => index, fun first second _ => Subsingleton.elim first second⟩
  have h := congrArg (fun law : _root_.AFT.FiniteDist (Fin 1 → _root_.CurrentAFT.CycleRootExpansion.Root security) =>
    law.map (fun roots => roots 0))
    (_root_.CurrentAFT.CycleRootExpansion.rootLaw_selected security 1 (by have := _p2mH92 security; omega) labels)
  rw [_root_.AFT.FiniteDist.map_map] at h
  exact h.trans (_p2mH99 _ _ _ _
    (_p2mH92 security) _ _ 0)
open _root_.P2M8f8f5b7e renaming h96 → _p2mH96
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h89 (security : ℕ) :
    _root_.CurrentAFT.CycleRootExpansion.expectationLinear (Value := Value) (_root_.CurrentAFT.CycleRootExpansion.rootLaw security) -
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security)) =
      ∑ selected ∈ (Finset.univ : Finset (Finset (_root_.CurrentAFT.CycleRootExpansion.Vertex security))).filter
          (fun selected => 2 ≤ selected.card), _root_.CurrentAFT.CycleRootExpansion.actualComponent security selected :=
  _p2mH95 _ _ (_p2mH93 _ _ (_p2mH96 security))
    (_p2mH96 security)
open _root_.P2M8f8f5b7e renaming h89 → _p2mH89
variable {Control : Type*} [Fintype Control]
end Actual
open _root_.P2M8f8f5b7e renaming h89 → _p2mH89
open _root_.P2M8f8f5b7e renaming h92 → _p2mH92
open _root_.P2M8f8f5b7e renaming h96 → _p2mH96
end
open _root_.P2M8f8f5b7e renaming h89 → _p2mH89
open _root_.P2M8f8f5b7e renaming h90 → _p2mH90
open _root_.P2M8f8f5b7e renaming h91 → _p2mH91
open _root_.P2M8f8f5b7e renaming h92 → _p2mH92
open _root_.P2M8f8f5b7e renaming h93 → _p2mH93
open _root_.P2M8f8f5b7e renaming h94 → _p2mH94
open _root_.P2M8f8f5b7e renaming h95 → _p2mH95
open _root_.P2M8f8f5b7e renaming h96 → _p2mH96
open _root_.P2M8f8f5b7e renaming h97 → _p2mH97
open _root_.P2M8f8f5b7e renaming h98 → _p2mH98
end CurrentAFT.CycleRootExpansion
open _root_.P2M8f8f5b7e renaming h89 → _p2mH89
open _root_.P2M8f8f5b7e renaming h90 → _p2mH90
open _root_.P2M8f8f5b7e renaming h91 → _p2mH91
open _root_.P2M8f8f5b7e renaming h92 → _p2mH92
open _root_.P2M8f8f5b7e renaming h93 → _p2mH93
open _root_.P2M8f8f5b7e renaming h94 → _p2mH94
open _root_.P2M8f8f5b7e renaming h95 → _p2mH95
open _root_.P2M8f8f5b7e renaming h96 → _p2mH96
open _root_.P2M8f8f5b7e renaming h97 → _p2mH97
open _root_.P2M8f8f5b7e renaming h98 → _p2mH98
end
open _root_.P2M8f8f5b7e renaming h89 → _p2mH89
open _root_.P2M8f8f5b7e renaming h90 → _p2mH90
open _root_.P2M8f8f5b7e renaming h91 → _p2mH91
open _root_.P2M8f8f5b7e renaming h92 → _p2mH92
open _root_.P2M8f8f5b7e renaming h93 → _p2mH93
open _root_.P2M8f8f5b7e renaming h94 → _p2mH94
open _root_.P2M8f8f5b7e renaming h95 → _p2mH95
open _root_.P2M8f8f5b7e renaming h96 → _p2mH96
open _root_.P2M8f8f5b7e renaming h97 → _p2mH97
open _root_.P2M8f8f5b7e renaming h98 → _p2mH98
namespace CurrentAFT.ActualBlockFock.blockLawAt.match_1
end CurrentAFT.ActualBlockFock.blockLawAt.match_1
namespace CurrentAFT.ActualBlockFock.primaryLawAt
end CurrentAFT.ActualBlockFock.primaryLawAt
namespace CurrentAFT.ActualBlockMean
end CurrentAFT.ActualBlockMean
namespace CurrentAFT.ActualBlockMean.attachmentRoots
end CurrentAFT.ActualBlockMean.attachmentRoots
namespace CurrentAFT.ActualBlockMean.blockVector
end CurrentAFT.ActualBlockMean.blockVector
namespace CurrentAFT.ActualBlockMean.bodyVector
end CurrentAFT.ActualBlockMean.bodyVector
namespace CurrentAFT.ActualBlockMean.centerRoots
end CurrentAFT.ActualBlockMean.centerRoots
namespace CurrentAFT.ActualBlockMean.queueRoots
end CurrentAFT.ActualBlockMean.queueRoots
namespace CurrentAFT.ActualBlockMean.rootAt
end CurrentAFT.ActualBlockMean.rootAt
namespace CurrentAFT.ActualBlockMean.rootedLaw
end CurrentAFT.ActualBlockMean.rootedLaw
namespace CurrentAFT.ActualCycleMeanMGF
end CurrentAFT.ActualCycleMeanMGF
namespace CurrentAFT.ActualCycleMeanMGF.realizedResponse
end CurrentAFT.ActualCycleMeanMGF.realizedResponse
namespace CurrentAFT.BackgroundEndpointLaw
end CurrentAFT.BackgroundEndpointLaw
namespace CurrentAFT.BackgroundEndpointLaw.endpointColor
end CurrentAFT.BackgroundEndpointLaw.endpointColor
namespace CurrentAFT.BackgroundEndpointLaw.endpointColor.match_1
end CurrentAFT.BackgroundEndpointLaw.endpointColor.match_1
namespace CurrentAFT.BackgroundEndpointLaw.flatLaw
end CurrentAFT.BackgroundEndpointLaw.flatLaw
namespace CurrentAFT.BackgroundPolynomialEvaluation.endpointFactor
end CurrentAFT.BackgroundPolynomialEvaluation.endpointFactor
namespace CurrentAFT.BackgroundPolynomialEvaluation.legFactor
end CurrentAFT.BackgroundPolynomialEvaluation.legFactor
namespace CurrentAFT.CycleRootPolynomial
end CurrentAFT.CycleRootPolynomial
namespace CurrentAFT.CycleRootPolynomial.polynomialComponent
end CurrentAFT.CycleRootPolynomial.polynomialComponent
namespace CurrentAFT.CycleRootPolynomial.polynomialDefect
end CurrentAFT.CycleRootPolynomial.polynomialDefect
section
namespace CurrentAFT.RootBackgroundPolynomial
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  LocalReferenceEnergy ActualBlockFock ActualBlockMean BackgroundPolynomialEvaluation
  CycleRootExpansion CycleRootPolynomial ConditionalHistogramMean ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  CycleRootExpansion.rootLaw CycleRootExpansion.rootReference
attribute [local instance] _root_.CurrentAFT.RootBackgroundPolynomial.blockIndexDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h248 (security : ℕ) (first second : ℤ)
    (hequal : (first : _root_.CurrentAFT.CycleRootExpansion.Root security) = (second : _root_.CurrentAFT.CycleRootExpansion.Root security)) :
    _root_.CurrentAFT.ActualBlockFock.primaryLawAt security first = _root_.CurrentAFT.ActualBlockFock.primaryLawAt security second := by
  have hatt (scalar : _root_.CurrentAFT.LocalReferenceEnergy.Scalar security) :
      _root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security first scalar = _root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security second scalar := by
    unfold _root_.CurrentAFT.LocalReferenceEnergy.attachmentAt
    rw [_root_.CurrentAFT.RootBackgroundPolynomial.shiftEquiv_eq_of_cast security (first + scalar.val) (second + scalar.val)
      (by simp only [Int.cast_add, hequal])]
  unfold _root_.CurrentAFT.ActualBlockFock.primaryLawAt
  congr 1
  funext scalar
  simp only [_root_.CurrentAFT.PositiveFirstCoefficient.positiveTripleLaw, hatt]
open _root_.P2M8f8f5b7e renaming h248 → _p2mH248
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h249 (security : ℕ) :
    _root_.CurrentAFT.CycleRootExpansion.rootLaw security = (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security))).mix (fun permutation =>
      (_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security => _root_.CurrentAFT.DiffuseProfiles.edgeLaw security)).map (_root_.CurrentAFT.RootBackgroundPolynomial.rootedResidues security permutation)) := by
  unfold _root_.CurrentAFT.CycleRootExpansion.rootLaw _root_.CurrentAFT.ProtectedCycle.relabeledCycleLaw _root_.CurrentAFT.ProtectedCycle.cycleLaw
  simp only [_root_.AFT.FiniteDist.map_map]
  congr 1
  funext permutation
  congr 1
  funext latent vertex
  simp only [_root_.CurrentAFT.RootBackgroundPolynomial.rootedResidues, _root_.CurrentAFT.ActualBlockMean.rootAt, _root_.CurrentAFT.PublicCharge.cycleDifference, Int.cast_sub]
open _root_.P2M8f8f5b7e renaming h249 → _p2mH249
end
open _root_.P2M8f8f5b7e renaming h248 → _p2mH248
open _root_.P2M8f8f5b7e renaming h249 → _p2mH249
end CurrentAFT.RootBackgroundPolynomial
open _root_.P2M8f8f5b7e renaming h248 → _p2mH248
open _root_.P2M8f8f5b7e renaming h249 → _p2mH249
end
open _root_.P2M8f8f5b7e renaming h248 → _p2mH248
open _root_.P2M8f8f5b7e renaming h249 → _p2mH249
namespace CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating
end CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating
namespace CurrentAFT.RootBackgroundPolynomial
end CurrentAFT.RootBackgroundPolynomial
namespace CurrentAFT.RootBackgroundPolynomial.localPolynomialInt
end CurrentAFT.RootBackgroundPolynomial.localPolynomialInt
namespace CurrentAFT.RootBackgroundPolynomial.localPolynomialInt.match_1
end CurrentAFT.RootBackgroundPolynomial.localPolynomialInt.match_1
namespace CurrentAFT.RootBackgroundPolynomial.rootedResidues
end CurrentAFT.RootBackgroundPolynomial.rootedResidues
section
namespace CurrentAFT.RootIndependentBackground
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  LocalReferenceEnergy ActualBlockFock ActualBlockMean ActualCycleMeanMGF
  BackgroundPolynomialEvaluation BackgroundEndpointLaw RootBackgroundPolynomial
  CycleRootExpansion CycleRootPolynomial BodyRootAverages PairQuadraticEvaluation
  PositiveFirstCoefficient LegPolynomialEvaluation BackgroundTranslations
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
  CycleRootExpansion.rootLaw CycleRootExpansion.rootReference
attribute [local instance] _root_.CurrentAFT.RootIndependentBackground.finOneDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentBackground.finThreeDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentBackground.blockIndexDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h272 {Input Output State : Type*} [Fintype Input] [Fintype Output] [Fintype State]
    (law : _root_.AFT.FiniteDist Input) (map : Input → Output) (kernel : Output → _root_.AFT.FiniteDist State) :
    (law.map map).mix kernel = law.mix (kernel ∘ map) := by
  ext state
  change (law.map map).expectation (fun output => (kernel output).weight state) =
    law.expectation (fun input => (kernel (map input)).weight state)
  rw [_root_.AFT.FiniteDist.expectation_map]
  rfl
open _root_.P2M8f8f5b7e renaming h272 → _p2mH272
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h276 (security : ℕ) (law : _root_.AFT.FiniteDist (_root_.CurrentAFT.ActualControls.Palette security)) :
    (_root_.CurrentAFT.CycleRootExpansion.rootReference security).mix (fun root => law.map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root.val : ℤ))) =
      _root_.CurrentAFT.BodyRootAverages.rootAverage security law := by
  unfold _root_.CurrentAFT.CycleRootExpansion.rootReference _root_.CurrentAFT.ProtectedCycle.differenceLaw
  rw [_p2mH272]
  have hshift (edge : _root_.CurrentAFT.LocalReferenceEnergy.BlurSeed security) :
      _root_.CurrentAFT.ProposalPrimary.shiftEquiv security
        (((((edge.1 : ℤ) : _root_.CurrentAFT.CycleRootExpansion.Root security) - ((edge.2 : ℤ) : _root_.CurrentAFT.CycleRootExpansion.Root security)).val : ℕ) : ℤ) =
        _root_.CurrentAFT.ProposalPrimary.shiftEquiv security (edge.1.val - edge.2.val) := by
    apply _root_.CurrentAFT.RootBackgroundPolynomial.shiftEquiv_eq_of_cast
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val, Int.cast_sub]
  ext output
  simp only [_root_.AFT.FiniteDist.mix_weight, Function.comp_apply, hshift,
    _root_.CurrentAFT.BodyRootAverages.rootAverage, _root_.CurrentAFT.LocalReferenceEnergy.publicBlurLaw, Fintype.sum_prod_type, _root_.AFT.FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  ring
open _root_.P2M8f8f5b7e renaming h276 → _p2mH276
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h278 (security : ℕ) (law : _root_.AFT.FiniteDist (_root_.CurrentAFT.ActualControls.Palette security)) :
    _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.ActualBlockFock.singletonLaw law) = _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.FringeCertificate.uniformProfile security) law.weight := by
  unfold _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating _root_.CurrentAFT.ActualBlockFock.singletonLaw
  rw [_p2mH42]
  simp only [_root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating, _root_.AFT.RepresentedPolynomial.singleGenerating, Function.comp_apply, Fin.prod_univ_one]
open _root_.P2M8f8f5b7e renaming h278 → _p2mH278
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h271 {Choice Slot : Type*} [Fintype Choice] [Fintype Slot]
    (security : ℕ) (law : _root_.AFT.FiniteDist Choice) (kernel : Choice → _root_.AFT.FiniteDist (Slot → _root_.CurrentAFT.ActualControls.Palette security)) :
    _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (law.mix kernel) = ∑ choice, law.weight choice • _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (kernel choice) := by
  unfold _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating
  rw [_p2mH53]
open _root_.P2M8f8f5b7e renaming h271 → _p2mH271
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h279 {Color Value : Type*} [Fintype Color] [AddCommMonoid Value]
    (test : Color → Color → Color → Value) :
    (∑ word : Fin 3 → Color, test (word 0) (word 1) (word 2)) = ∑ first, ∑ second, ∑ third, test first second third := by
  simpa [_root_.CurrentAFT.RootIndependentBackground.tripleEquiv, Fintype.sum_prod_type] using
    ((_root_.CurrentAFT.RootIndependentBackground.tripleEquiv (Color := Color)).symm.sum_comp
      (fun word : Fin 3 → Color => test (word 0) (word 1) (word 2))).symm
open _root_.P2M8f8f5b7e renaming h279 → _p2mH279
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h273 (security : ℕ) (root : ℤ) (scalar : _root_.CurrentAFT.LocalReferenceEnergy.Scalar security) :
    _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.PositiveFirstCoefficient.positiveTripleLaw security root scalar) =
      _root_.AFT.RepresentedPolynomial.pairGenerating (_root_.CurrentAFT.FringeCertificate.uniformProfile security)
          (fun first second => (_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).weight (first, second)) *
        _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.FringeCertificate.uniformProfile security) (_root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security root scalar).weight := by
  rw [← _p2mH17]
  unfold _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating _root_.AFT.RepresentedPolynomial.tripleGenerating
  simp_rw [_root_.CurrentAFT.PositiveFirstCoefficient.positiveTriple_weight]
  simp only [_root_.AFT.PhysicalBlockTensors.tripleMass, _root_.CurrentAFT.LocalReferenceEnergy.tripleMassAt, Fin.prod_univ_three]
  simp_rw [← _p2mH189]
  rw [_p2mH279 (fun first second third =>
    MvPolynomial.C ((_root_.CurrentAFT.PairQuadraticEvaluation.conditionalPairLaw security scalar).weight (first, second) *
      (_root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security root scalar).weight third) *
      (_root_.AFT.RepresentedPolynomial.centeredFactor (_root_.CurrentAFT.FringeCertificate.uniformProfile security) first *
        _root_.AFT.RepresentedPolynomial.centeredFactor (_root_.CurrentAFT.FringeCertificate.uniformProfile security) second *
        _root_.AFT.RepresentedPolynomial.centeredFactor (_root_.CurrentAFT.FringeCertificate.uniformProfile security) third))]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  apply Finset.sum_congr rfl
  intro third _
  ring
open _root_.P2M8f8f5b7e renaming h273 → _p2mH273
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h277 {Choice Color : Type*} [Fintype Choice] [Fintype Color]
    (reference : Color → ℝ) (law : _root_.AFT.FiniteDist Choice) (kernel : Choice → _root_.AFT.FiniteDist Color) :
    _root_.AFT.RepresentedPolynomial.singleGenerating reference (law.mix kernel).weight =
      ∑ choice, law.weight choice • _root_.AFT.RepresentedPolynomial.singleGenerating reference (kernel choice).weight :=
  _p2mH53 law kernel (_root_.AFT.RepresentedPolynomial.centeredFactor reference)
open _root_.P2M8f8f5b7e renaming h277 → _p2mH277
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h275 (security : ℕ) (scalar : _root_.CurrentAFT.LocalReferenceEnergy.Scalar security) :
    (_root_.CurrentAFT.CycleRootExpansion.rootReference security).mix (fun root => _root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security root.val scalar) = _root_.CurrentAFT.LegPolynomialEvaluation.attachmentLaw security scalar := by
  have happ (root : _root_.CurrentAFT.CycleRootExpansion.Root security) : _root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security root.val scalar =
      (_root_.CurrentAFT.BackgroundTranslations.shiftedSafeLaw security scalar.val).map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security root.val) := by
    unfold _root_.CurrentAFT.LocalReferenceEnergy.attachmentAt _root_.CurrentAFT.BackgroundTranslations.shiftedSafeLaw
    rw [_p2mH85, add_comm scalar.val]
  simp_rw [happ]
  exact _p2mH276 security _
open _root_.P2M8f8f5b7e renaming h275 → _p2mH275
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h270 {Root Scalar Variable : Type*} [Fintype Root] [Fintype Scalar]
    (rootLaw : _root_.AFT.FiniteDist Root) (scalarLaw : _root_.AFT.FiniteDist Scalar)
    (pair : Scalar → MvPolynomial Variable ℝ) (body : Root → Scalar → MvPolynomial Variable ℝ) :
    (∑ root, rootLaw.weight root • (∑ scalar, scalarLaw.weight scalar • (pair scalar * body root scalar))) =
      ∑ scalar, scalarLaw.weight scalar • (pair scalar * ∑ root, rootLaw.weight root • body root scalar) := by
  simp only [Finset.smul_sum, MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro scalar _
  apply Finset.sum_congr rfl
  intro root _
  ring
open _root_.P2M8f8f5b7e renaming h270 → _p2mH270
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h274 (security : ℕ) :
    (∑ root : _root_.CurrentAFT.CycleRootExpansion.Root security, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root • _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.ActualBlockFock.primaryLawAt security root.val)) =
      _root_.CurrentAFT.LegPolynomialEvaluation.legGenerating security := by
  simp only [_root_.CurrentAFT.ActualBlockFock.primaryLawAt, _p2mH271, _p2mH273]
  rw [_p2mH270]
  simp_rw [← _p2mH277, _p2mH275]
  unfold _root_.CurrentAFT.LegPolynomialEvaluation.legGenerating
  apply Finset.sum_congr rfl
  intro scalar _
  congr 1
  rw [_p2mH15 _ _ (_root_.CurrentAFT.LegPolynomialEvaluation.attachmentLaw security scalar).sum_one]
  exact (_p2mH139 security scalar).symm
open _root_.P2M8f8f5b7e renaming h274 → _p2mH274
end
open _root_.P2M8f8f5b7e renaming h270 → _p2mH270
open _root_.P2M8f8f5b7e renaming h271 → _p2mH271
open _root_.P2M8f8f5b7e renaming h272 → _p2mH272
open _root_.P2M8f8f5b7e renaming h273 → _p2mH273
open _root_.P2M8f8f5b7e renaming h274 → _p2mH274
open _root_.P2M8f8f5b7e renaming h275 → _p2mH275
open _root_.P2M8f8f5b7e renaming h276 → _p2mH276
open _root_.P2M8f8f5b7e renaming h277 → _p2mH277
open _root_.P2M8f8f5b7e renaming h278 → _p2mH278
open _root_.P2M8f8f5b7e renaming h279 → _p2mH279
end CurrentAFT.RootIndependentBackground
open _root_.P2M8f8f5b7e renaming h270 → _p2mH270
open _root_.P2M8f8f5b7e renaming h271 → _p2mH271
open _root_.P2M8f8f5b7e renaming h272 → _p2mH272
open _root_.P2M8f8f5b7e renaming h273 → _p2mH273
open _root_.P2M8f8f5b7e renaming h274 → _p2mH274
open _root_.P2M8f8f5b7e renaming h275 → _p2mH275
open _root_.P2M8f8f5b7e renaming h276 → _p2mH276
open _root_.P2M8f8f5b7e renaming h277 → _p2mH277
open _root_.P2M8f8f5b7e renaming h278 → _p2mH278
open _root_.P2M8f8f5b7e renaming h279 → _p2mH279
end
open _root_.P2M8f8f5b7e renaming h270 → _p2mH270
open _root_.P2M8f8f5b7e renaming h271 → _p2mH271
open _root_.P2M8f8f5b7e renaming h272 → _p2mH272
open _root_.P2M8f8f5b7e renaming h273 → _p2mH273
open _root_.P2M8f8f5b7e renaming h274 → _p2mH274
open _root_.P2M8f8f5b7e renaming h275 → _p2mH275
open _root_.P2M8f8f5b7e renaming h276 → _p2mH276
open _root_.P2M8f8f5b7e renaming h277 → _p2mH277
open _root_.P2M8f8f5b7e renaming h278 → _p2mH278
open _root_.P2M8f8f5b7e renaming h279 → _p2mH279
namespace CurrentAFT.FirstHistogram
end CurrentAFT.FirstHistogram
namespace CurrentAFT.FirstHistogram.completeHistogramResponse
end CurrentAFT.FirstHistogram.completeHistogramResponse
namespace CurrentAFT.IndependentPairedReference
end CurrentAFT.IndependentPairedReference
namespace CurrentAFT.IndependentPairedReference.independentSignedMass
end CurrentAFT.IndependentPairedReference.independentSignedMass
namespace CurrentAFT.IndependentPairedReference.profileEnergy_add
end CurrentAFT.IndependentPairedReference.profileEnergy_add
section
namespace CurrentAFT.NormalizedLocalPolynomial
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse LocalCoefficientFamily LocalCoefficientEvaluation
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.NormalizedLocalPolynomial.classicalFinDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h176 (security order : ℕ) (mass : (Fin 4 → _root_.CurrentAFT.NormalizedLocalPolynomial.Palette security) → ℝ)
    (bodyForms : _root_.CurrentAFT.ActualControls.SafePalette security → MvPolynomial (_root_.CurrentAFT.NormalizedLocalPolynomial.Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :
    _root_.CurrentAFT.LocalCoefficientEvaluation.evaluation security order bodyForms hbody (_root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily security order mass) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight mass) := by
  unfold _root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily
  simp only [map_add, map_smul, map_one, map_sum, _p2mH153]
  have hexpand := _p2mH3 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
    (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) (_root_.CurrentAFT.ActualControls.primaryReference_positive security) mass
  rw [hexpand]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin 4)))
    (_root_.AFT.RepresentedPolynomial.referenceCoefficientForm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
      (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) mass) (Finset.mem_univ ∅)
  rw [_p2mH12] at hsplit
  rw [← hsplit, map_add, map_sum]
  have hconstant : _root_.CurrentAFT.TruncatedOutput.quotientMap order (MvPolynomial.C (∑ word, mass word)) =
      (∑ word, mass word) • (1 : _root_.CurrentAFT.TruncatedOutput.Polynomial (_root_.CurrentAFT.NormalizedLocalPolynomial.Palette security) order) := by
    rw [Algebra.smul_def, mul_one]
    exact (_root_.CurrentAFT.TruncatedOutput.quotientMap order).commutes _
  rw [hconstant, add_comm]
open _root_.P2M8f8f5b7e renaming h176 → _p2mH176
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h179 (security order : ℕ) (law : _root_.AFT.FiniteDist (Fin 4 → _root_.CurrentAFT.NormalizedLocalPolynomial.Palette security)) :
    _root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily security order law (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = (1 : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) := by
  rw [_root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily, _root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily_zeroArity, law.sum_one, one_smul]
open _root_.P2M8f8f5b7e renaming h179 → _p2mH179
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h177 (security order : ℕ) (positive : _root_.AFT.FiniteDist (Fin 4 → _root_.CurrentAFT.NormalizedLocalPolynomial.Palette security))
    (signed : (Fin 4 → _root_.CurrentAFT.NormalizedLocalPolynomial.Palette security) → ℝ) :
    _root_.CurrentAFT.NormalizedLocalPolynomial.normalizedFamily security order positive signed * _root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily security order positive =
      _root_.CurrentAFT.NormalizedLocalPolynomial.completeFamily security order signed := by
  unfold _root_.CurrentAFT.NormalizedLocalPolynomial.normalizedFamily
  rw [mul_assoc, _p2mH128 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
    (_root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily security order positive) (_p2mH179 security order positive), mul_one]
open _root_.P2M8f8f5b7e renaming h177 → _p2mH177
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h178 (security order : ℕ) (positive : _root_.AFT.FiniteDist (Fin 4 → _root_.CurrentAFT.NormalizedLocalPolynomial.Palette security))
    (signed : (Fin 4 → _root_.CurrentAFT.NormalizedLocalPolynomial.Palette security) → ℝ)
    (bodyForms : _root_.CurrentAFT.ActualControls.SafePalette security → MvPolynomial (_root_.CurrentAFT.NormalizedLocalPolynomial.Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :
    _root_.CurrentAFT.LocalCoefficientEvaluation.evaluation security order bodyForms hbody (_root_.CurrentAFT.NormalizedLocalPolynomial.normalizedFamily security order positive signed) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight positive.weight) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight signed) := by
  rw [← _p2mH176 security order positive.weight bodyForms hbody,
    ← _p2mH176 security order signed bodyForms hbody]
  change _root_.CurrentAFT.LocalCoefficientEvaluation.evaluation security order bodyForms hbody (_root_.CurrentAFT.NormalizedLocalPolynomial.normalizedFamily security order positive signed) *
      _root_.CurrentAFT.LocalCoefficientEvaluation.evaluation security order bodyForms hbody (_root_.CurrentAFT.NormalizedLocalPolynomial.positiveFamily security order positive) = _
  rw [← map_mul, _p2mH177]
open _root_.P2M8f8f5b7e renaming h178 → _p2mH178
end
open _root_.P2M8f8f5b7e renaming h176 → _p2mH176
open _root_.P2M8f8f5b7e renaming h177 → _p2mH177
open _root_.P2M8f8f5b7e renaming h178 → _p2mH178
open _root_.P2M8f8f5b7e renaming h179 → _p2mH179
end CurrentAFT.NormalizedLocalPolynomial
open _root_.P2M8f8f5b7e renaming h176 → _p2mH176
open _root_.P2M8f8f5b7e renaming h177 → _p2mH177
open _root_.P2M8f8f5b7e renaming h178 → _p2mH178
open _root_.P2M8f8f5b7e renaming h179 → _p2mH179
end
open _root_.P2M8f8f5b7e renaming h176 → _p2mH176
open _root_.P2M8f8f5b7e renaming h177 → _p2mH177
open _root_.P2M8f8f5b7e renaming h178 → _p2mH178
open _root_.P2M8f8f5b7e renaming h179 → _p2mH179
namespace CurrentAFT.GlobalRaising
end CurrentAFT.GlobalRaising
namespace CurrentAFT.GlobalRaising.bodyPoint
end CurrentAFT.GlobalRaising.bodyPoint
namespace CurrentAFT.GlobalRaising.homogeneousCorrectionLinear
end CurrentAFT.GlobalRaising.homogeneousCorrectionLinear
namespace CurrentAFT.GlobalRaising.primaryPoint
end CurrentAFT.GlobalRaising.primaryPoint
namespace CurrentAFT.GlobalRaising.raisedPoint
end CurrentAFT.GlobalRaising.raisedPoint
namespace CurrentAFT.GlobalRaising.raisingLinear
end CurrentAFT.GlobalRaising.raisingLinear
namespace CurrentAFT.GlobalRaising.responseInverse
end CurrentAFT.GlobalRaising.responseInverse
namespace CurrentAFT.GlobalRaising.responseLinear
end CurrentAFT.GlobalRaising.responseLinear
namespace CurrentAFT.GlobalRaising.selectedCorrection
end CurrentAFT.GlobalRaising.selectedCorrection
namespace CurrentAFT.GlobalRaising.selectedCorrectionLinear
end CurrentAFT.GlobalRaising.selectedCorrectionLinear
namespace CurrentAFT.GlobalRaising.selectedPointProduct
end CurrentAFT.GlobalRaising.selectedPointProduct
namespace CurrentAFT.PrimaryMassFamilies
end CurrentAFT.PrimaryMassFamilies
namespace CurrentAFT.PrimaryMassFamilies.massCertificateFamily
end CurrentAFT.PrimaryMassFamilies.massCertificateFamily
namespace CurrentAFT.PrimaryMassFamilies.massLiftKernel
end CurrentAFT.PrimaryMassFamilies.massLiftKernel
namespace CurrentAFT.PrimaryMassFamilies.oneWordProfile
end CurrentAFT.PrimaryMassFamilies.oneWordProfile
namespace CurrentAFT.PrimaryMassFamilies.pairWordProfile
end CurrentAFT.PrimaryMassFamilies.pairWordProfile
namespace CurrentAFT.PrimaryMassFamilies.primaryArity
end CurrentAFT.PrimaryMassFamilies.primaryArity
section
namespace CurrentAFT.OrdinaryRaising
open AFT DiffuseProfiles ProposalPrimary ActualControls FringeCertificate BackgroundCertificates
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse GradedInverseNorm LocalCoefficientFamily LocalRaisingFirst LocalRaisingBounds
  PrimaryTensorInverse PrimaryMassFamilies BackgroundFamilies LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.OrdinaryRaising.classicalFinDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h183 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.OrdinaryRaising.positiveAtom security order horder (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0 := by
  unfold _root_.CurrentAFT.OrdinaryRaising.positiveAtom _root_.CurrentAFT.PrimaryMassFamilies.massCertificateFamily
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => arity.val.1.val) hequal
  change 0 = 1 at h
  omega
open _root_.P2M8f8f5b7e renaming h183 → _p2mH183
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h185 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.OrdinaryRaising.positiveFamily security order horder (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = (1 : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) := by
  change (1 : _root_.CurrentAFT.LocalCoefficientFamily.Family security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) + _root_.CurrentAFT.OrdinaryRaising.positiveAtom security order horder (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = _
  rw [_p2mH183, add_zero]
open _root_.P2M8f8f5b7e renaming h185 → _p2mH185
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h181 (security order : ℕ) (horder : 1 ≤ order)
    (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) (hcentered : (_root_.CurrentAFT.ActualControls.bodyReference security).expectation score = 0) :
    _root_.CurrentAFT.OrdinaryRaising.normalizedFamily security order horder score hcentered =
      _root_.CurrentAFT.BackgroundFamilies.bodyFamily (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder score hcentered +
        _root_.CurrentAFT.OrdinaryRaising.raisingFamily security order horder score hcentered := by
  unfold _root_.CurrentAFT.OrdinaryRaising.normalizedFamily _root_.CurrentAFT.OrdinaryRaising.raisingFamily
  rw [mul_sub, mul_one]
  abel
open _root_.P2M8f8f5b7e renaming h181 → _p2mH181
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h184 (security order : ℕ) (horder : 1 ≤ order) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.OrdinaryRaising.positiveFamily security order horder) =
      1 + _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.OrdinaryRaising.deviation security)) := by
  unfold _root_.CurrentAFT.OrdinaryRaising.positiveFamily _root_.CurrentAFT.OrdinaryRaising.positiveAtom
  rw [map_add, map_one, _p2mH45,
    _p2mH48]
open _root_.P2M8f8f5b7e renaming h184 → _p2mH184
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h182 (security order : ℕ) (horder : 1 ≤ order)
    (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) (hcentered : (_root_.CurrentAFT.ActualControls.bodyReference security).expectation score = 0) :
    _root_.CurrentAFT.OrdinaryRaising.normalizedFamily security order horder score hcentered * _root_.CurrentAFT.OrdinaryRaising.positiveFamily security order horder =
      _root_.CurrentAFT.BackgroundFamilies.bodyFamily (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder score hcentered := by
  unfold _root_.CurrentAFT.OrdinaryRaising.normalizedFamily _root_.CurrentAFT.OrdinaryRaising.positiveInverse
  rw [mul_assoc, _p2mH128 _ _ order _ (_p2mH185 security order horder), mul_one]
open _root_.P2M8f8f5b7e renaming h182 → _p2mH182
end
open _root_.P2M8f8f5b7e renaming h181 → _p2mH181
open _root_.P2M8f8f5b7e renaming h182 → _p2mH182
open _root_.P2M8f8f5b7e renaming h183 → _p2mH183
open _root_.P2M8f8f5b7e renaming h184 → _p2mH184
open _root_.P2M8f8f5b7e renaming h185 → _p2mH185
end CurrentAFT.OrdinaryRaising
open _root_.P2M8f8f5b7e renaming h181 → _p2mH181
open _root_.P2M8f8f5b7e renaming h182 → _p2mH182
open _root_.P2M8f8f5b7e renaming h183 → _p2mH183
open _root_.P2M8f8f5b7e renaming h184 → _p2mH184
open _root_.P2M8f8f5b7e renaming h185 → _p2mH185
end
open _root_.P2M8f8f5b7e renaming h181 → _p2mH181
open _root_.P2M8f8f5b7e renaming h182 → _p2mH182
open _root_.P2M8f8f5b7e renaming h183 → _p2mH183
open _root_.P2M8f8f5b7e renaming h184 → _p2mH184
open _root_.P2M8f8f5b7e renaming h185 → _p2mH185
namespace CurrentAFT.FirstHistogram.scoreProfile
end CurrentAFT.FirstHistogram.scoreProfile
namespace CurrentAFT.FixedPairedFirst
end CurrentAFT.FixedPairedFirst
namespace CurrentAFT.FixedPairedFirst.compensatorAnchorAt
end CurrentAFT.FixedPairedFirst.compensatorAnchorAt
namespace CurrentAFT.FixedPairedFirst.fixedControlLaw
end CurrentAFT.FixedPairedFirst.fixedControlLaw
namespace CurrentAFT.FixedPairedFirst.pair_first_expectation
end CurrentAFT.FixedPairedFirst.pair_first_expectation
namespace CurrentAFT.FixedPairedFirst.pair_second_expectation
end CurrentAFT.FixedPairedFirst.pair_second_expectation
namespace CurrentAFT.FixedPairedFirst.pointLaw
end CurrentAFT.FixedPairedFirst.pointLaw
namespace CurrentAFT.LocalRaisingBounds
end CurrentAFT.LocalRaisingBounds
namespace CurrentAFT.LocalRaisingBounds.base_ge_one
end CurrentAFT.LocalRaisingBounds.base_ge_one
namespace CurrentAFT.LocalRaisingBounds.coefficientNorm
end CurrentAFT.LocalRaisingBounds.coefficientNorm
namespace CurrentAFT.LocalReferenceEnergy.tripleMassAt
end CurrentAFT.LocalReferenceEnergy.tripleMassAt
namespace CurrentAFT.PairedReferenceEnergy.jointPairedMass
end CurrentAFT.PairedReferenceEnergy.jointPairedMass
namespace CurrentAFT.RaisingBodySlots
end CurrentAFT.RaisingBodySlots
namespace CurrentAFT.RootIndependentBackground
end CurrentAFT.RootIndependentBackground
namespace CurrentAFT.RootIndependentBackground.roleMeanPolynomial
end CurrentAFT.RootIndependentBackground.roleMeanPolynomial
namespace CurrentAFT.RootIndependentBackground.roleMeanPolynomial.match_1
end CurrentAFT.RootIndependentBackground.roleMeanPolynomial.match_1
namespace CurrentAFT.RootIndependentBackground.tripleEquiv
end CurrentAFT.RootIndependentBackground.tripleEquiv
section
namespace CurrentAFT.RootTaggedSelected
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst PhysicalSynthesis
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  LocalCoefficientFamily LocalRaisingFirst LocalRaisingBounds NormalizedLocalPolynomial
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootTaggedSelected.classicalFinDecidableEq
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h358 (security order : ℕ) (score : _root_.CurrentAFT.RootTaggedSelected.RootPair security → _root_.CurrentAFT.RootTaggedSelected.Palette security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootTaggedSelected.normalizedResponse security order score) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.NormalizedLocalPolynomial.independentPositiveLaw security).weight) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.RootTaggedSelected.mass security score)) :=
  _p2mH178 security order _ _ (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security)
    (_root_.CurrentAFT.BackgroundEvaluation.bodyForm_homogeneous security)
open _root_.P2M8f8f5b7e renaming h358 → _p2mH358
end
open _root_.P2M8f8f5b7e renaming h358 → _p2mH358
end CurrentAFT.RootTaggedSelected
open _root_.P2M8f8f5b7e renaming h358 → _p2mH358
end
open _root_.P2M8f8f5b7e renaming h358 → _p2mH358
namespace AFT.TensorChannel.applyLinear
end AFT.TensorChannel.applyLinear
namespace AFT.TensorChannel.center
end AFT.TensorChannel.center
section
namespace CurrentAFT.RootCoordinateProjection
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {Index Root Control : Type*} [Fintype Index] [DecidableEq Index]
  [Fintype Root] [Fintype Control]
set_option maxRecDepth 8192
omit [Fintype Index] [Fintype Control] in
theorem _root_.P2M8f8f5b7e.h267 (root : _root_.AFT.FiniteDist Root) (index : Index)
    (score : _root_.CurrentAFT.RootCoordinateProjection.Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hinvariant : ∀ sample value, score (Function.update sample.1 index value, sample.2) = score sample) :
    _root_.CurrentAFT.RootCoordinateProjection.average root index score = score := by
  funext sample
  simp only [_root_.CurrentAFT.RootCoordinateProjection.average_apply, hinvariant, _root_.AFT.FiniteDist.expectation_const]
open _root_.P2M8f8f5b7e renaming h267 → _p2mH267
set_option maxRecDepth 8192
omit [Fintype Index] [Fintype Control] in
theorem _root_.P2M8f8f5b7e.h268 (root : _root_.AFT.FiniteDist Root) (index : Index)
    (score : _root_.CurrentAFT.RootCoordinateProjection.Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hcentered : ∀ sample : _root_.CurrentAFT.RootCoordinateProjection.Input (Index := Index) (Root := Root) (Control := Control), root.expectation (fun value => score (Function.update sample.1 index value, sample.2)) = 0) :
    _root_.CurrentAFT.RootCoordinateProjection.center root index score = score := by
  funext sample
  simp only [_root_.CurrentAFT.RootCoordinateProjection.center_apply, _root_.CurrentAFT.RootCoordinateProjection.average_apply, hcentered, sub_zero]
open _root_.P2M8f8f5b7e renaming h268 → _p2mH268
set_option maxRecDepth 8192
omit [Fintype Index] [Fintype Control] in
theorem _root_.P2M8f8f5b7e.h269 (root : _root_.AFT.FiniteDist Root) (coordinates : List (Index × Bool))
    (score : _root_.CurrentAFT.RootCoordinateProjection.Input (Index := Index) (Root := Root) (Control := Control) → ℝ)
    (hfixed : ∀ item ∈ coordinates, _root_.CurrentAFT.RootCoordinateProjection.coordinate root item.1 item.2 score = score) :
    _root_.CurrentAFT.RootCoordinateProjection.sequence root coordinates score = score := by
  induction coordinates with
  | nil => rfl
  | cons item rest ih =>
    change _root_.CurrentAFT.RootCoordinateProjection.coordinate root item.1 item.2 (_root_.CurrentAFT.RootCoordinateProjection.sequence root rest score) = score
    rw [ih (fun other hother => hfixed other (List.mem_cons_of_mem item hother))]
    exact hfixed item List.mem_cons_self
open _root_.P2M8f8f5b7e renaming h269 → _p2mH269
end
open _root_.P2M8f8f5b7e renaming h267 → _p2mH267
open _root_.P2M8f8f5b7e renaming h268 → _p2mH268
open _root_.P2M8f8f5b7e renaming h269 → _p2mH269
end CurrentAFT.RootCoordinateProjection
open _root_.P2M8f8f5b7e renaming h267 → _p2mH267
open _root_.P2M8f8f5b7e renaming h268 → _p2mH268
open _root_.P2M8f8f5b7e renaming h269 → _p2mH269
end
open _root_.P2M8f8f5b7e renaming h267 → _p2mH267
open _root_.P2M8f8f5b7e renaming h268 → _p2mH268
open _root_.P2M8f8f5b7e renaming h269 → _p2mH269
namespace CurrentAFT.CompleteFirstCoefficient
end CurrentAFT.CompleteFirstCoefficient
namespace CurrentAFT.CompleteFirstCoefficient.firstScore
end CurrentAFT.CompleteFirstCoefficient.firstScore
namespace CurrentAFT.LocalRaisingLinear
end CurrentAFT.LocalRaisingLinear
namespace CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear
end CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear
namespace CurrentAFT.RootCoordinateProjection
end CurrentAFT.RootCoordinateProjection
namespace CurrentAFT.RootCoordinateProjection.insert
end CurrentAFT.RootCoordinateProjection.insert
namespace CurrentAFT.RootCoordinateProjection.sequence
end CurrentAFT.RootCoordinateProjection.sequence
namespace CurrentAFT.RootSelectedZeroTag
end CurrentAFT.RootSelectedZeroTag
namespace CurrentAFT.RootTaggedSelected
end CurrentAFT.RootTaggedSelected
namespace CurrentAFT.RootTaggedSelected.rootsLaw
end CurrentAFT.RootTaggedSelected.rootsLaw
namespace CurrentAFT.RootTaggedSelected.sourceLaw
end CurrentAFT.RootTaggedSelected.sourceLaw
namespace CurrentAFT.RootTaggedSelectedCancellation
end CurrentAFT.RootTaggedSelectedCancellation
section
namespace CurrentAFT.RootPrimaryGroupedChannel
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm
  LocalCoefficientFamily LocalReferenceEnergy NormalizedLocalPolynomial
  LocalRaisingBounds RootTaggedSelected RootTaggedSelectedNorm
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootPrimaryGroupedChannel.classicalFinDecidableEq
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h336 (security order : ℕ) (tagged : Fin 2 → Bool)
    (score : _root_.CurrentAFT.RootPrimaryGroupedChannel.Input security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootPrimaryGroupedChannel.channel security order tagged score) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
          (_root_.CurrentAFT.NormalizedLocalPolynomial.independentPositiveLaw security).weight) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
          (_root_.CurrentAFT.RootTaggedSelected.mass security (_root_.CurrentAFT.RootPrimaryGroupedChannel.centeredScore security tagged score))) :=
  _p2mH358 security order _
open _root_.P2M8f8f5b7e renaming h336 → _p2mH336
end
open _root_.P2M8f8f5b7e renaming h336 → _p2mH336
end CurrentAFT.RootPrimaryGroupedChannel
open _root_.P2M8f8f5b7e renaming h336 → _p2mH336
end
open _root_.P2M8f8f5b7e renaming h336 → _p2mH336
namespace CurrentAFT.SelectedOrdinaryRoot
end CurrentAFT.SelectedOrdinaryRoot
namespace CurrentAFT.SelectedOrdinaryRoot.pushLinear
end CurrentAFT.SelectedOrdinaryRoot.pushLinear
namespace CurrentAFT.SelectedOrdinaryRoot.rawMass
end CurrentAFT.SelectedOrdinaryRoot.rawMass
namespace CurrentAFT.SelectedOrdinaryRoot.rawMassLinear
end CurrentAFT.SelectedOrdinaryRoot.rawMassLinear
namespace CurrentAFT.SelectedOrdinaryRoot.sliceLinear
end CurrentAFT.SelectedOrdinaryRoot.sliceLinear
section
namespace CurrentAFT.SelectedOrdinaryRootProperties
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds PrimaryTensorInverse
  SelectedOrdinaryRoot
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.SelectedOrdinaryRootProperties.classicalFinDecidableEq
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h377 (security : ℕ) (score : _root_.CurrentAFT.SelectedOrdinaryRoot.Input security → ℝ) :
    _root_.CurrentAFT.DiffuseProfiles.activation security • _root_.CurrentAFT.FirstResponse.response security
        (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * _root_.CurrentAFT.SelectedOrdinaryRoot.densityLinear security score color) =
      _root_.CurrentAFT.SelectedOrdinaryRoot.rawMass security (_root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security score) := by
  have h := _p2mH214 security
    (fun color => _root_.CurrentAFT.SelectedOrdinaryRoot.rawMass security (_root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security score) color / (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color)
  rw [← _root_.CurrentAFT.SelectedOrdinaryRoot.densityLinear_apply] at h
  funext color
  have hp := congrFun h color
  rw [_root_.CurrentAFT.PrimaryTensorInverse.densityResponse_apply] at hp
  apply (div_left_inj' (_root_.CurrentAFT.ActualControls.primaryReference_positive security color).ne').mp
  exact hp
open _root_.P2M8f8f5b7e renaming h377 → _p2mH377
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h376 (security order : ℕ) (horder : 1 ≤ order) (score : _root_.CurrentAFT.SelectedOrdinaryRoot.Input security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.SelectedOrdinaryRoot.numeratorLinear security order horder score) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.SelectedOrdinaryRoot.rawMass security (_root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security score))) := by
  change _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
    (_root_.CurrentAFT.BackgroundFamilies.primaryFamily _ _ order horder (_root_.CurrentAFT.SelectedOrdinaryRoot.densityLinear security score) (_root_.CurrentAFT.SelectedOrdinaryRoot.densityLinear_centered security score)) = _
  rw [_p2mH50, _p2mH377]
open _root_.P2M8f8f5b7e renaming h376 → _p2mH376
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h375 (security order : ℕ) (horder : 1 ≤ order) (score : _root_.CurrentAFT.SelectedOrdinaryRoot.Input security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.SelectedOrdinaryRoot.channel security order horder score) *
      (1 + _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.OrdinaryRaising.deviation security))) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm
        (_root_.CurrentAFT.SelectedOrdinaryRoot.rawMass security (_root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security score))) := by
  have hmul : _root_.CurrentAFT.SelectedOrdinaryRoot.channel security order horder score * _root_.CurrentAFT.OrdinaryRaising.positiveFamily security order horder =
      _root_.CurrentAFT.SelectedOrdinaryRoot.numeratorLinear security order horder score := by
    change (_root_.CurrentAFT.SelectedOrdinaryRoot.numeratorLinear security order horder score * _root_.CurrentAFT.OrdinaryRaising.positiveInverse security order horder) * _ = _
    unfold _root_.CurrentAFT.OrdinaryRaising.positiveInverse
    rw [mul_assoc, _p2mH128 _ _ order _ (_p2mH185 security order horder), mul_one]
  have h := congrArg (_root_.CurrentAFT.BackgroundEvaluation.evaluation security order) hmul
  rwa [map_mul, _p2mH184, _p2mH376] at h
open _root_.P2M8f8f5b7e renaming h375 → _p2mH375
end
open _root_.P2M8f8f5b7e renaming h375 → _p2mH375
open _root_.P2M8f8f5b7e renaming h376 → _p2mH376
open _root_.P2M8f8f5b7e renaming h377 → _p2mH377
end CurrentAFT.SelectedOrdinaryRootProperties
open _root_.P2M8f8f5b7e renaming h375 → _p2mH375
open _root_.P2M8f8f5b7e renaming h376 → _p2mH376
open _root_.P2M8f8f5b7e renaming h377 → _p2mH377
end
open _root_.P2M8f8f5b7e renaming h375 → _p2mH375
open _root_.P2M8f8f5b7e renaming h376 → _p2mH376
open _root_.P2M8f8f5b7e renaming h377 → _p2mH377
namespace CurrentAFT.RootReferenceExpectation
end CurrentAFT.RootReferenceExpectation
namespace CurrentAFT.SelectedOrdinaryRootProperties
end CurrentAFT.SelectedOrdinaryRootProperties
section
namespace CurrentAFT.SelectedOrdinaryMean
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds CoefficientHilbert SelectedOrdinaryRoot
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.SelectedOrdinaryMean.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.SelectedOrdinaryMean.safeDecidableEq
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h372 (security : ℕ) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security (_root_.CurrentAFT.SelectedOrdinaryMean.constantRoot security score) =
      _root_.CurrentAFT.SelectedOrdinaryMean.constantRoot security (_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ActualControls.bodyReference security) score) := rfl
open _root_.P2M8f8f5b7e renaming h372 → _p2mH372
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h373 (security : ℕ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ)
    (output : _root_.CurrentAFT.SelectedOrdinaryMean.Palette security) :
    _root_.CurrentAFT.SelectedOrdinaryRoot.pushLinear (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.SelectedOrdinaryRoot.rootEmbedding security root) score output =
      _root_.CurrentAFT.BodyChannelEvaluation.safeMass security score ((_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root.val : ℤ)).symm output) := by
  unfold _root_.CurrentAFT.SelectedOrdinaryRoot.pushLinear _root_.CurrentAFT.SelectedOrdinaryRoot.rootEmbedding _root_.CurrentAFT.BodyChannelEvaluation.safeMass _root_.CurrentAFT.BodyChannelEvaluation.weightedEmbedding
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.single_apply]
  apply Finset.sum_congr rfl
  intro center _
  have hequal : _root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root.val : ℤ) center.val = output ↔
      (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root.val : ℤ)).symm output = center.val := by
    constructor
    · intro h; exact ((_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root.val : ℤ)).symm_apply_eq.mpr h.symm)
    · intro h; exact (Equiv.apply_eq_iff_eq_symm_apply (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root.val : ℤ))).mpr h.symm
  by_cases h : _root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root.val : ℤ) center.val = output
  · rw [if_pos h, if_pos (hequal.mp h), mul_one]
  · rw [if_neg h, if_neg (fun h' => h (hequal.mpr h')), mul_zero]
open _root_.P2M8f8f5b7e renaming h373 → _p2mH373
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h374 (security : ℕ) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryRoot.rawMass security (_root_.CurrentAFT.SelectedOrdinaryMean.constantRoot security score) =
      _root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security score) := by
  funext output
  rw [_root_.CurrentAFT.SelectedOrdinaryRoot.rawMass_apply]
  change (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation (fun root =>
    _root_.CurrentAFT.SelectedOrdinaryRoot.pushLinear (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.SelectedOrdinaryRoot.rootEmbedding security root) score output) = _
  simp only [_p2mH373]
  change _ = (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).expectation (fun seed =>
    _root_.CurrentAFT.BodyChannelEvaluation.safeMass security score ((_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (_root_.CurrentAFT.DiffuseProfiles.actualBlur security seed)).symm output))
  apply _root_.CurrentAFT.RootReferenceExpectation.rootReference_seed_expectation security (fun value : ℤ =>
    _root_.CurrentAFT.BodyChannelEvaluation.safeMass security score ((_root_.CurrentAFT.ProposalPrimary.shiftEquiv security value).symm output))
  intro first second hequal
  rw [_root_.CurrentAFT.RootBackgroundPolynomial.shiftEquiv_eq_of_cast security first second hequal]
open _root_.P2M8f8f5b7e renaming h374 → _p2mH374
end
open _root_.P2M8f8f5b7e renaming h372 → _p2mH372
open _root_.P2M8f8f5b7e renaming h373 → _p2mH373
open _root_.P2M8f8f5b7e renaming h374 → _p2mH374
end CurrentAFT.SelectedOrdinaryMean
open _root_.P2M8f8f5b7e renaming h372 → _p2mH372
open _root_.P2M8f8f5b7e renaming h373 → _p2mH373
open _root_.P2M8f8f5b7e renaming h374 → _p2mH374
end
open _root_.P2M8f8f5b7e renaming h372 → _p2mH372
open _root_.P2M8f8f5b7e renaming h373 → _p2mH373
open _root_.P2M8f8f5b7e renaming h374 → _p2mH374
namespace CurrentAFT.SelectedOrdinaryMean
end CurrentAFT.SelectedOrdinaryMean
section
namespace CurrentAFT.SelectedOrdinaryHybrid
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion FirstHistogram
  ControlCoordinates ControlProduct ControlNorm GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse LocalCoefficientFamily LocalRaisingLinear LocalRaisingFirst LocalRaisingBounds CoefficientHilbert
  SelectedOrdinaryRoot SelectedOrdinaryMean
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.SelectedOrdinaryHybrid.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.SelectedOrdinaryHybrid.safeDecidableEq
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h370 (security order : ℕ) (horder : 1 ≤ order) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.SelectedOrdinaryHybrid.independentChannel security order horder score = _root_.CurrentAFT.RaisingChannels.bodyLeading security order horder score +
      _root_.CurrentAFT.RaisingChannels.bodyRaised security order horder score := by
  exact _p2mH181 security order horder _ _
open _root_.P2M8f8f5b7e renaming h370 → _p2mH370
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h371 (security order : ℕ) (horder : 1 ≤ order) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.SelectedOrdinaryHybrid.independentChannel security order horder score) *
      (1 + _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.OrdinaryRaising.deviation security))) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm
        (_root_.CurrentAFT.MarkedPairLeading.bodyConvolution security (_root_.CurrentAFT.BodyChannelEvaluation.safeMass security (_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ActualControls.bodyReference security) score)))) := by
  have h := congrArg (_root_.CurrentAFT.BackgroundEvaluation.evaluation security order)
    (_p2mH182 security order horder (_root_.CurrentAFT.CoefficientHilbert.centerLinear (_root_.CurrentAFT.ActualControls.bodyReference security) score) (_root_.CurrentAFT.CoefficientHilbert.center_mean _ score))
  rw [map_mul, _p2mH184, _p2mH62] at h
  exact h
open _root_.P2M8f8f5b7e renaming h371 → _p2mH371
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h369 (security order : ℕ) (horder : 1 ≤ order) (score : _root_.CurrentAFT.SelectedOrdinaryRoot.Input security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.SelectedOrdinaryHybrid.channel security order horder score) *
      (1 + _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.OrdinaryRaising.deviation security))) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm
        (_root_.CurrentAFT.SelectedOrdinaryRoot.rawMass security (_root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security score))) := by
  rw [_root_.CurrentAFT.SelectedOrdinaryHybrid.channel_apply, map_add, add_mul, _p2mH371,
    _p2mH375]
  rw [← _p2mH374, ← _p2mH372]
  rw [← map_add, ← map_add]
  change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm
    (_root_.CurrentAFT.SelectedOrdinaryRoot.rawMassLinear security (_root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security (_root_.CurrentAFT.SelectedOrdinaryMean.constantRoot security (_root_.CurrentAFT.SelectedOrdinaryMean.rootMean security score))) +
      _root_.CurrentAFT.SelectedOrdinaryRoot.rawMassLinear security (_root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security (_root_.CurrentAFT.SelectedOrdinaryMean.rootCenter security score)))) = _
  rw [← map_add, ← map_add]
  have hsplit : _root_.CurrentAFT.SelectedOrdinaryMean.constantRoot security (_root_.CurrentAFT.SelectedOrdinaryMean.rootMean security score) + _root_.CurrentAFT.SelectedOrdinaryMean.rootCenter security score = score := by
    change _root_.CurrentAFT.SelectedOrdinaryMean.constantRoot security (_root_.CurrentAFT.SelectedOrdinaryMean.rootMean security score) + (score - _root_.CurrentAFT.SelectedOrdinaryMean.constantRoot security (_root_.CurrentAFT.SelectedOrdinaryMean.rootMean security score)) = score
    abel
  rw [hsplit]
  rfl
open _root_.P2M8f8f5b7e renaming h369 → _p2mH369
end
open _root_.P2M8f8f5b7e renaming h369 → _p2mH369
open _root_.P2M8f8f5b7e renaming h370 → _p2mH370
open _root_.P2M8f8f5b7e renaming h371 → _p2mH371
end CurrentAFT.SelectedOrdinaryHybrid
open _root_.P2M8f8f5b7e renaming h369 → _p2mH369
open _root_.P2M8f8f5b7e renaming h370 → _p2mH370
open _root_.P2M8f8f5b7e renaming h371 → _p2mH371
end
open _root_.P2M8f8f5b7e renaming h369 → _p2mH369
open _root_.P2M8f8f5b7e renaming h370 → _p2mH370
open _root_.P2M8f8f5b7e renaming h371 → _p2mH371
namespace CurrentAFT.SelectedOrdinaryHybrid
end CurrentAFT.SelectedOrdinaryHybrid
section
namespace CurrentAFT.RootOrdinaryGroupedChannel
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  ControlCoordinates ControlProduct GradedControlAlgebra GradedControlNorm GradedControlStability
  GradedInverse LocalCoefficientFamily LocalRaisingLinear LocalRaisingBounds CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootOrdinaryGroupedChannel.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootOrdinaryGroupedChannel.safeDecidableEq
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h326 (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool) (score : _root_.CurrentAFT.RootOrdinaryGroupedChannel.Input security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootOrdinaryGroupedChannel.channel security order horder tagged score) *
      (1 + _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.OrdinaryRaising.deviation security))) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm
        (_root_.CurrentAFT.SelectedOrdinaryRoot.rawMass security (_root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security
          (_root_.CurrentAFT.RootOrdinaryGroupedChannel.toRaw security (_root_.CurrentAFT.RootOrdinaryGroupedChannel.projector security tagged score))))) :=
  _p2mH369 security order horder _
open _root_.P2M8f8f5b7e renaming h326 → _p2mH326
end
open _root_.P2M8f8f5b7e renaming h326 → _p2mH326
end CurrentAFT.RootOrdinaryGroupedChannel
open _root_.P2M8f8f5b7e renaming h326 → _p2mH326
end
open _root_.P2M8f8f5b7e renaming h326 → _p2mH326
section
namespace CurrentAFT.RootTaggedLocal
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  UniformBodyProfiles CycleRootExpansion RootBackgroundPolynomial PrimaryTensorInverse
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h353 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ)
    (color : _root_.CurrentAFT.ActualControls.Palette security) :
    (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * _root_.CurrentAFT.PrimaryTensorInverse.densityResponse security (_root_.CurrentAFT.RootTaggedLocal.rootLift security role queue input) color =
      _root_.CurrentAFT.RootTaggedLocal.rootMass security role queue input color := by
  rw [_root_.CurrentAFT.RootTaggedLocal.rootLift_apply, _p2mH214, _root_.CurrentAFT.RootTaggedLocal.profileDensity_apply]
  field_simp [(_root_.CurrentAFT.ActualControls.primaryReference_positive security color).ne']
open _root_.P2M8f8f5b7e renaming h353 → _p2mH353
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h354 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.CurrentAFT.DiffuseProfiles.activation security • _root_.CurrentAFT.FirstResponse.response security
      (fun color => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color * _root_.CurrentAFT.RootTaggedLocal.rootLift security role queue input color) =
        _root_.CurrentAFT.RootTaggedLocal.rootMass security role queue input := by
  funext color
  have h := _p2mH353 security role queue input color
  rw [_root_.CurrentAFT.PrimaryTensorInverse.densityResponse_apply] at h
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    _ = (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color *
        (_root_.CurrentAFT.DiffuseProfiles.activation security * _root_.CurrentAFT.FirstResponse.response security
          (fun point => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight point * _root_.CurrentAFT.RootTaggedLocal.rootLift security role queue input point) color /
            (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color) := by field_simp [(_root_.CurrentAFT.ActualControls.primaryReference_positive security color).ne']
    _ = _ := h
open _root_.P2M8f8f5b7e renaming h354 → _p2mH354
end
open _root_.P2M8f8f5b7e renaming h353 → _p2mH353
open _root_.P2M8f8f5b7e renaming h354 → _p2mH354
end CurrentAFT.RootTaggedLocal
open _root_.P2M8f8f5b7e renaming h353 → _p2mH353
open _root_.P2M8f8f5b7e renaming h354 → _p2mH354
end
open _root_.P2M8f8f5b7e renaming h353 → _p2mH353
open _root_.P2M8f8f5b7e renaming h354 → _p2mH354
namespace CurrentAFT.RootTaggedLocal
end CurrentAFT.RootTaggedLocal
namespace CurrentAFT.RootTaggedLocal.deviationProfile
end CurrentAFT.RootTaggedLocal.deviationProfile
namespace CurrentAFT.RootTaggedLocal.meanLaw
end CurrentAFT.RootTaggedLocal.meanLaw
namespace CurrentAFT.RootTaggedLocal.rootCost
end CurrentAFT.RootTaggedLocal.rootCost
namespace CurrentAFT.RootTaggedLocal.rootMass
end CurrentAFT.RootTaggedLocal.rootMass
namespace CurrentAFT.RootTaggedLocal.shiftedLaw
end CurrentAFT.RootTaggedLocal.shiftedLaw
section
namespace CurrentAFT.RootTaggedFamilies
open AFT ControlCoordinates GradedControlAlgebra GradedControlNorm DiffuseProfiles
  ProposalPrimary ActualControls UniformBodyProfiles CycleRootExpansion RootTaggedLocal
  BackgroundFamilies BackgroundRates BackgroundEvaluation BackgroundFirstEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  ActualControls.bodyReference CycleRootExpansion.rootReference
attribute [local instance] _root_.CurrentAFT.RootTaggedFamilies.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h346 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear security order horder role queue input) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.RootTaggedLocal.rootMass security role queue input)) := by
  rw [_root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear_apply, _p2mH50, _p2mH354]
open _root_.P2M8f8f5b7e renaming h346 → _p2mH346
end
open _root_.P2M8f8f5b7e renaming h346 → _p2mH346
end CurrentAFT.RootTaggedFamilies
open _root_.P2M8f8f5b7e renaming h346 → _p2mH346
end
open _root_.P2M8f8f5b7e renaming h346 → _p2mH346
namespace CurrentAFT.RootTaggedFamilies
end CurrentAFT.RootTaggedFamilies
namespace CurrentAFT.RootTaggedFamilies.rootFamilyLinear
end CurrentAFT.RootTaggedFamilies.rootFamilyLinear
namespace CurrentAFT.RootTaggedFamilies.rootKernelLinear
end CurrentAFT.RootTaggedFamilies.rootKernelLinear
section
namespace CurrentAFT.RootTaggedLegFirst
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  ActualBlockFock ActualBlockMean ActualCycleMeanMGF UniformBodyProfiles HistogramMean
  CycleRootExpansion RootTaggedLocal RootTaggedFamilies BackgroundEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference
attribute [local instance] _root_.CurrentAFT.RootTaggedLegFirst.finThreeDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h349 (security : ℕ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) (color : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.RootTaggedLegFirst.legHistogram security root color =
      _root_.CurrentAFT.HistogramMean.offBodyMean security color + (_root_.CurrentAFT.RootTaggedLocal.shiftedLaw security .attachment 0 root).weight color :=
  _p2mH24 security root.val color
open _root_.P2M8f8f5b7e renaming h349 → _p2mH349
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h350 (security : ℕ) (color : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.RootTaggedLegFirst.meanLegHistogram security color = _root_.CurrentAFT.HistogramMean.offBodyMean security color + (_root_.CurrentAFT.RootTaggedLocal.meanLaw security .attachment 0).weight color := by
  simp only [_root_.CurrentAFT.RootTaggedLegFirst.meanLegHistogram, _p2mH349, _root_.CurrentAFT.RootTaggedLocal.meanLaw, _root_.AFT.FiniteDist.mix_weight,
    _root_.AFT.FiniteDist.expectation, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, _root_.AFT.FiniteDist.sum_one, one_mul]
open _root_.P2M8f8f5b7e renaming h350 → _p2mH350
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h347 (security : ℕ) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) (color : _root_.CurrentAFT.ActualControls.Palette security) :
    _root_.CurrentAFT.RootTaggedLegFirst.legHistogram security root color - _root_.CurrentAFT.RootTaggedLegFirst.meanLegHistogram security color =
      _root_.CurrentAFT.RootTaggedLocal.deviationProfile security .attachment 0 root color := by
  rw [_p2mH349, _p2mH350]
  simp only [_root_.CurrentAFT.RootTaggedLocal.deviationProfile, Pi.sub_apply]
  ring
open _root_.P2M8f8f5b7e renaming h347 → _p2mH347
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h348 (security : ℕ) : _root_.CurrentAFT.RootTaggedLegFirst.legFirstMass security = _root_.CurrentAFT.RootTaggedLocal.rootMass security .attachment 0 := by
  apply LinearMap.ext
  intro input
  funext color
  simp only [_root_.CurrentAFT.RootTaggedLegFirst.legFirstMass, _root_.CurrentAFT.RootTaggedLocal.rootMass, LinearMap.coe_mk, AddHom.coe_mk, _p2mH347]
open _root_.P2M8f8f5b7e renaming h348 → _p2mH348
end
open _root_.P2M8f8f5b7e renaming h347 → _p2mH347
open _root_.P2M8f8f5b7e renaming h348 → _p2mH348
open _root_.P2M8f8f5b7e renaming h349 → _p2mH349
open _root_.P2M8f8f5b7e renaming h350 → _p2mH350
end CurrentAFT.RootTaggedLegFirst
open _root_.P2M8f8f5b7e renaming h347 → _p2mH347
open _root_.P2M8f8f5b7e renaming h348 → _p2mH348
open _root_.P2M8f8f5b7e renaming h349 → _p2mH349
open _root_.P2M8f8f5b7e renaming h350 → _p2mH350
end
open _root_.P2M8f8f5b7e renaming h347 → _p2mH347
open _root_.P2M8f8f5b7e renaming h348 → _p2mH348
open _root_.P2M8f8f5b7e renaming h349 → _p2mH349
open _root_.P2M8f8f5b7e renaming h350 → _p2mH350
namespace CurrentAFT.LocalCoefficientNorm
end CurrentAFT.LocalCoefficientNorm
namespace CurrentAFT.LocalCoefficientNorm.primaryMassEnergy
end CurrentAFT.LocalCoefficientNorm.primaryMassEnergy
namespace CurrentAFT.RootTaggedLegFirst
end CurrentAFT.RootTaggedLegFirst
namespace CurrentAFT.RootTaggedLegFirst.legFirstMass
end CurrentAFT.RootTaggedLegFirst.legFirstMass
namespace CurrentAFT.RootTaggedLegFirst.meanLegHistogram
end CurrentAFT.RootTaggedLegFirst.meanLegHistogram
section
namespace CurrentAFT.RootTaggedLegHigher
open AFT DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  ActualBlockFock PositiveFirstCoefficient CycleRootExpansion RootTaggedLocal
  PrimaryTensorInverse PhysicalBlockTensors BlockFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize ProposalPrimary.primaryLaw
  CycleRootExpansion.rootReference
attribute [local instance] _root_.CurrentAFT.RootTaggedLegHigher.finThreeDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h352 (security : ℕ) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    (∑ word, _root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear security input word) = (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation input := by
  unfold _root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, _root_.AFT.FiniteDist.sum_one, mul_one]
  rfl
open _root_.P2M8f8f5b7e renaming h352 → _p2mH352
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h351 (security : ℕ) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    (∑ word, _root_.CurrentAFT.RootTaggedLegHigher.massLinear security input word) = 0 := by
  rw [_root_.CurrentAFT.RootTaggedLegHigher.massLinear, LinearMap.comp_apply, _p2mH352, _p2mH18]
open _root_.P2M8f8f5b7e renaming h351 → _p2mH351
end
open _root_.P2M8f8f5b7e renaming h351 → _p2mH351
open _root_.P2M8f8f5b7e renaming h352 → _p2mH352
end CurrentAFT.RootTaggedLegHigher
open _root_.P2M8f8f5b7e renaming h351 → _p2mH351
open _root_.P2M8f8f5b7e renaming h352 → _p2mH352
end
open _root_.P2M8f8f5b7e renaming h351 → _p2mH351
open _root_.P2M8f8f5b7e renaming h352 → _p2mH352
namespace CurrentAFT.LocalReferenceEnergy.jointTripleMass
end CurrentAFT.LocalReferenceEnergy.jointTripleMass
namespace CurrentAFT.RootTaggedLegHigher
end CurrentAFT.RootTaggedLegHigher
namespace CurrentAFT.RootTaggedLegHigher.massLinear
end CurrentAFT.RootTaggedLegHigher.massLinear
namespace CurrentAFT.RootTaggedLegHigher.rawMassLinear
end CurrentAFT.RootTaggedLegHigher.rawMassLinear
namespace CurrentAFT.RootTaggedLegHigher.sourceLaw
end CurrentAFT.RootTaggedLegHigher.sourceLaw
section
namespace CurrentAFT.RootLegCoefficientFamily
open AFT DiffuseProfiles ProposalPrimary ActualControls
open ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
  LocalCoefficientFamily
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootLegCoefficientFamily.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootLegCoefficientFamily.classicalSubtypeDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h287 (security degree : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.RootLegCoefficientFamily.Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree) :
    _root_.CurrentAFT.PrimaryTensorInverse.tensorResponse security degree
      (_root_.CurrentAFT.RootLegCoefficientFamily.normalizedSelectedDensity security degree mass selected hdegree) =
        _root_.CurrentAFT.RootLegCoefficientFamily.selectedDensity security degree mass selected hdegree :=
  _p2mH216 security degree _
open _root_.P2M8f8f5b7e renaming h287 → _p2mH287
set_option maxRecDepth 8192
private def _root_.P2M8f8f5b7e.h411 {Source Target Color : Type*} (equiv : Source ≃ Target) :
    (Target → Color) ≃ (Source → Color) where
  toFun word := word ∘ equiv
  invFun word := word ∘ equiv.symm
  left_inv word := by funext index; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  right_inv word := by funext index; simp only [Function.comp_apply, Equiv.symm_apply_apply]
open _root_.P2M8f8f5b7e renaming h411 → CurrentAFT.RootLegCoefficientFamily.orderedWordEquiv
open _root_.P2M8f8f5b7e renaming h411 → _p2mH411
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h288 (security degree : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.RootLegCoefficientFamily.Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree) :
    _root_.CurrentAFT.LocalCoefficientFamily.primaryLeadingPolynomial security degree (_root_.CurrentAFT.RootLegCoefficientFamily.normalizedSelectedDensity security degree mass selected hdegree) =
      _root_.AFT.RepresentedPolynomial.referenceCoefficientForm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
        (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) mass selected := by
  unfold _root_.CurrentAFT.LocalCoefficientFamily.primaryLeadingPolynomial _root_.CurrentAFT.LocalCoefficientFamily.massPolynomial _root_.CurrentAFT.PrimaryTensorInverse.massLeading
  rw [_p2mH287]
  let equiv := Fintype.equivFinOfCardEq hdegree
  have hreindex := (_p2mH411 (Color := _root_.CurrentAFT.RootLegCoefficientFamily.Palette security) equiv).sum_comp
    (fun word : selected → _root_.CurrentAFT.RootLegCoefficientFamily.Palette security =>
      MvPolynomial.C (_root_.AFT.LocalTensors.referenceRestrictedComponent (fun _ : Fin 3 => _root_.CurrentAFT.ProposalPrimary.primaryLaw security)
        (fun _ : Fin 3 => _root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) mass selected word *
          ∏ index, (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight (word index)) *
        ∏ index, MvPolynomial.X (R := ℝ) (word index))
  change _ = ∑ word : selected → _root_.CurrentAFT.RootLegCoefficientFamily.Palette security, _
  apply Eq.trans ?_ hreindex
  apply Finset.sum_congr rfl
  intro word _
  have hweight := equiv.prod_comp (fun index : Fin degree => (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight (word index))
  have hmonomial := equiv.prod_comp (fun index : Fin degree => MvPolynomial.X (R := ℝ) (word index))
  simp only [_p2mH411, Equiv.coe_fn_mk, Function.comp_apply, hweight, hmonomial,
    _root_.CurrentAFT.RootLegCoefficientFamily.selectedDensity, _root_.CurrentAFT.PrimaryTensorInverse.referenceWeight]
  congr 1
  congr 1
  ring
open _root_.P2M8f8f5b7e renaming h288 → _p2mH288
end
open _root_.P2M8f8f5b7e renaming h287 → _p2mH287
open _root_.P2M8f8f5b7e renaming h288 → _p2mH288
open _root_.P2M8f8f5b7e renaming h411 → CurrentAFT.RootLegCoefficientFamily.orderedWordEquiv
open _root_.P2M8f8f5b7e renaming h411 → _p2mH411
end CurrentAFT.RootLegCoefficientFamily
open _root_.P2M8f8f5b7e renaming h287 → _p2mH287
open _root_.P2M8f8f5b7e renaming h288 → _p2mH288
open _root_.P2M8f8f5b7e renaming h411 → CurrentAFT.RootLegCoefficientFamily.orderedWordEquiv
open _root_.P2M8f8f5b7e renaming h411 → _p2mH411
end
open _root_.P2M8f8f5b7e renaming h287 → _p2mH287
open _root_.P2M8f8f5b7e renaming h288 → _p2mH288
namespace CurrentAFT.RootLegCoefficientFamily
end CurrentAFT.RootLegCoefficientFamily
namespace CurrentAFT.RootLegCoefficientFamily.higherFamily
end CurrentAFT.RootLegCoefficientFamily.higherFamily
namespace CurrentAFT.RootLegCoefficientFamily.selectedDensity
end CurrentAFT.RootLegCoefficientFamily.selectedDensity
namespace CurrentAFT.RootLegCoefficientLinear
end CurrentAFT.RootLegCoefficientLinear
namespace CurrentAFT.RootLegCoefficientLinear.higherFamilyLinear
end CurrentAFT.RootLegCoefficientLinear.higherFamilyLinear
namespace CurrentAFT.RootLegCoefficientLinear.rootHigherLinear
end CurrentAFT.RootLegCoefficientLinear.rootHigherLinear
namespace CurrentAFT.RootLegCoefficientLinear.selectedFamilyLinear
end CurrentAFT.RootLegCoefficientLinear.selectedFamilyLinear
section
namespace CurrentAFT.RootLegCoefficientEvaluation
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
  LocalCoefficientEvaluation RootLegCoefficientFamily LeadingEvaluation
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootLegCoefficientEvaluation.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootLegCoefficientEvaluation.classicalSubtypeDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h286 (security degree : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.RootLegCoefficientEvaluation.Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = degree)
    (bodyForms : _root_.CurrentAFT.ActualControls.SafePalette security → MvPolynomial (_root_.CurrentAFT.RootLegCoefficientEvaluation.Palette security) ℝ) :
    _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms
      (_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security degree mass selected hdegree).val =
        _root_.AFT.RepresentedPolynomial.referenceCoefficientForm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
          (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) mass selected := by
  change _root_.CurrentAFT.LeadingEvaluation.kernelPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms
    (_root_.CurrentAFT.ControlProduct.symmetrize (fun colors (_ : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) =>
      _root_.CurrentAFT.RootLegCoefficientFamily.normalizedSelectedDensity security degree mass selected hdegree colors)) = _
  rw [_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial_symmetrize, _p2mH152, _p2mH288]
open _root_.P2M8f8f5b7e renaming h286 → _p2mH286
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h285 (security order : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.RootLegCoefficientEvaluation.Palette security) → ℝ)
    (selected : Finset (Fin 3))
    (bodyForms : _root_.CurrentAFT.ActualControls.SafePalette security → MvPolynomial (_root_.CurrentAFT.RootLegCoefficientEvaluation.Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :
    _root_.CurrentAFT.LocalCoefficientEvaluation.evaluation security order bodyForms hbody (_root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily security order mass selected) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.referenceCoefficientForm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
          (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) mass selected) := by
  unfold _root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily
  split_ifs with hdegree
  · change _root_.CurrentAFT.LeadingEvaluation.familyLinear _ _ _ _ _ (Pi.single _ _) = _
    rw [_root_.CurrentAFT.LeadingEvaluation.familyLinear_single]
    change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms (_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val) = _
    rw [_p2mH286]
  · rw [map_zero]
    have hzero := _root_.CurrentAFT.LeadingEvaluation.homogeneousLinear_above (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm_homogeneous security) hbody order selected.card 0 (by omega)
      (_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp))
    change _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LeadingEvaluation.kernelPolynomial (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security)
      (_root_.CurrentAFT.LocalCoefficientEvaluation.primaryForm security) bodyForms (_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security selected.card mass selected (by simp)).val) = 0 at hzero
    rw [_p2mH286] at hzero
    exact hzero.symm
open _root_.P2M8f8f5b7e renaming h285 → _p2mH285
end
open _root_.P2M8f8f5b7e renaming h285 → _p2mH285
open _root_.P2M8f8f5b7e renaming h286 → _p2mH286
end CurrentAFT.RootLegCoefficientEvaluation
open _root_.P2M8f8f5b7e renaming h285 → _p2mH285
open _root_.P2M8f8f5b7e renaming h286 → _p2mH286
end
open _root_.P2M8f8f5b7e renaming h285 → _p2mH285
open _root_.P2M8f8f5b7e renaming h286 → _p2mH286
namespace CurrentAFT.RootLegCoefficientBounds
end CurrentAFT.RootLegCoefficientBounds
namespace CurrentAFT.RootLegCoefficientBounds.normalizedFactor
end CurrentAFT.RootLegCoefficientBounds.normalizedFactor
section
namespace CurrentAFT.RootMeanPrimary
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  UniformBodyProfiles CycleRootExpansion RootTaggedLocal PrimaryTensorInverse PrimaryMassFamilies
  ControlCoordinates GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  BackgroundFamilies BackgroundRates BackgroundEvaluation BackgroundFirstEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
attribute [local instance] _root_.CurrentAFT.RootMeanPrimary.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h322 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) :
    _root_.CurrentAFT.RootMeanPrimary.positiveAtom security order horder role queue (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0 := by
  unfold _root_.CurrentAFT.RootMeanPrimary.positiveAtom _root_.CurrentAFT.PrimaryMassFamilies.massCertificateFamily
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => arity.val.1.val) hequal
  change 0 = 1 at h
  omega
open _root_.P2M8f8f5b7e renaming h322 → _p2mH322
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h324 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) :
    _root_.CurrentAFT.RootMeanPrimary.positiveFamily security order horder role queue (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = (1 : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) := by
  change (1 : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) + _root_.CurrentAFT.RootMeanPrimary.positiveAtom security order horder role queue (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = _
  rw [_p2mH322, add_zero]
open _root_.P2M8f8f5b7e renaming h324 → _p2mH324
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h323 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootMeanPrimary.positiveFamily security order horder role queue) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.RootTaggedLocal.meanLaw security role queue).weight) := by
  unfold _root_.CurrentAFT.RootMeanPrimary.positiveFamily _root_.CurrentAFT.RootMeanPrimary.positiveAtom
  rw [map_add, map_one, _p2mH45, _p2mH48,
    _p2mH15 _ _ (_root_.CurrentAFT.RootTaggedLocal.meanLaw security role queue).sum_one, map_add, map_one]
  rfl
open _root_.P2M8f8f5b7e renaming h323 → _p2mH323
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h325 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ) :
    _root_.CurrentAFT.RootMeanPrimary.positiveInverse security order horder role queue * _root_.CurrentAFT.RootMeanPrimary.positiveFamily security order horder role queue = 1 :=
  _p2mH128 _ _ _ _ (_p2mH324 security order horder role queue)
open _root_.P2M8f8f5b7e renaming h325 → _p2mH325
end
open _root_.P2M8f8f5b7e renaming h322 → _p2mH322
open _root_.P2M8f8f5b7e renaming h323 → _p2mH323
open _root_.P2M8f8f5b7e renaming h324 → _p2mH324
open _root_.P2M8f8f5b7e renaming h325 → _p2mH325
end CurrentAFT.RootMeanPrimary
open _root_.P2M8f8f5b7e renaming h322 → _p2mH322
open _root_.P2M8f8f5b7e renaming h323 → _p2mH323
open _root_.P2M8f8f5b7e renaming h324 → _p2mH324
open _root_.P2M8f8f5b7e renaming h325 → _p2mH325
end
open _root_.P2M8f8f5b7e renaming h322 → _p2mH322
open _root_.P2M8f8f5b7e renaming h323 → _p2mH323
open _root_.P2M8f8f5b7e renaming h324 → _p2mH324
open _root_.P2M8f8f5b7e renaming h325 → _p2mH325
namespace CurrentAFT.RootMeanPrimary
end CurrentAFT.RootMeanPrimary
namespace CurrentAFT.RootMeanPrimary.meanProfile
end CurrentAFT.RootMeanPrimary.meanProfile
section
namespace CurrentAFT.PrimaryOnlyFamily
open AFT ControlCoordinates ControlProduct GradedControlAlgebra GradedInverse
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PrimaryOnlyFamily.classicalFinDecidableEq
variable {Primary Body : Type*} [Fintype Primary] [Fintype Body]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h213 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ) :
    _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly primary body order 0 := by intro arity _; rfl
open _root_.P2M8f8f5b7e renaming h213 → _p2mH213
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h209 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ) :
    _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly primary body order 1 := by
  intro arity hbody
  change _root_.CurrentAFT.GradedControlAlgebra.familyUnit primary body order arity = 0
  unfold _root_.CurrentAFT.GradedControlAlgebra.familyUnit
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun item : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => item.val.2.val) hequal
  change arity.val.2.val = 0 at h
  omega
open _root_.P2M8f8f5b7e renaming h209 → _p2mH209
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h208 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ)
    (first second : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order)
    (hfirst : _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly primary body order first) (hsecond : _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly primary body order second) :
    _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly primary body order (first + second) := by
  intro arity hbody
  simp only [Pi.add_apply, hfirst arity hbody, hsecond arity hbody, add_zero]
open _root_.P2M8f8f5b7e renaming h208 → _p2mH208
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h211 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ)
    (scalar : ℝ) (family : _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order) (hfamily : _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly primary body order family) :
    _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly primary body order (scalar • family) := by
  intro arity hbody
  simp only [Pi.smul_apply, hfamily arity hbody, smul_zero]
open _root_.P2M8f8f5b7e renaming h211 → _p2mH211
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h210 (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (hbody : arity.val.2.val = 0)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels primary body arity.val.1.val arity.val.2.val) :
    _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly primary body order (Pi.single arity kernel) := by
  intro output hpositive
  rw [Pi.single_eq_of_ne]
  intro hequal
  have h := congrArg (fun item : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => item.val.2.val) hequal
  change output.val.2.val = arity.val.2.val at h
  omega
open _root_.P2M8f8f5b7e renaming h210 → _p2mH210
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h212 {Index : Type*} (primary : _root_.AFT.FiniteDist Primary) (body : _root_.AFT.FiniteDist Body) (order : ℕ)
    (indices : Finset Index) (families : Index → _root_.CurrentAFT.GradedControlAlgebra.KernelFamily primary body order)
    (hfamily : ∀ index ∈ indices, _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly primary body order (families index)) :
    _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly primary body order (∑ index ∈ indices, families index) := by
  intro arity hbody
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero fun index hindex => hfamily index hindex arity hbody
open _root_.P2M8f8f5b7e renaming h212 → _p2mH212
end
open _root_.P2M8f8f5b7e renaming h208 → _p2mH208
open _root_.P2M8f8f5b7e renaming h209 → _p2mH209
open _root_.P2M8f8f5b7e renaming h210 → _p2mH210
open _root_.P2M8f8f5b7e renaming h211 → _p2mH211
open _root_.P2M8f8f5b7e renaming h212 → _p2mH212
open _root_.P2M8f8f5b7e renaming h213 → _p2mH213
end CurrentAFT.PrimaryOnlyFamily
open _root_.P2M8f8f5b7e renaming h208 → _p2mH208
open _root_.P2M8f8f5b7e renaming h209 → _p2mH209
open _root_.P2M8f8f5b7e renaming h210 → _p2mH210
open _root_.P2M8f8f5b7e renaming h211 → _p2mH211
open _root_.P2M8f8f5b7e renaming h212 → _p2mH212
open _root_.P2M8f8f5b7e renaming h213 → _p2mH213
end
open _root_.P2M8f8f5b7e renaming h208 → _p2mH208
open _root_.P2M8f8f5b7e renaming h209 → _p2mH209
open _root_.P2M8f8f5b7e renaming h210 → _p2mH210
open _root_.P2M8f8f5b7e renaming h211 → _p2mH211
open _root_.P2M8f8f5b7e renaming h212 → _p2mH212
open _root_.P2M8f8f5b7e renaming h213 → _p2mH213
namespace CurrentAFT.PrimaryOnlyFamily
end CurrentAFT.PrimaryOnlyFamily
section
namespace CurrentAFT.RootLegNormalized
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct
open GradedControlAlgebra GradedInverse RootLegCoefficientFamily RootLegCoefficientEvaluation LocalCoefficientEvaluation
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootLegNormalized.classicalFinDecidableEq
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h305 (security order : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.RootLegNormalized.Palette security) → ℝ) :
    _root_.CurrentAFT.RootLegNormalized.completeFamily security order mass (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) =
      (∑ word, mass word) • (1 : _root_.CurrentAFT.RootLegCoefficientFamily.Family security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) := by
  have hselected (selected : Finset (Fin 3)) (hnonempty : selected ≠ ∅) :
      _root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily security order mass selected (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = 0 := by
    unfold _root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily
    split_ifs with hdegree
    · rw [Pi.single_eq_of_ne]
      intro hequal
      have hcard := congrArg (fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => arity.val.1.val) hequal
      change 0 = selected.card at hcard
      exact hnonempty (Finset.card_eq_zero.mp hcard.symm)
    · rfl
  unfold _root_.CurrentAFT.RootLegNormalized.completeFamily
  simp only [Pi.add_apply, Pi.smul_apply, Finset.sum_apply]
  have hzero : (∑ selected ∈ (Finset.univ : Finset (Finset (Fin 3))).erase ∅,
      _root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily security order mass selected (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order)) = 0 := by
    apply Finset.sum_eq_zero
    intro selected hselectedmem
    exact hselected selected (Finset.mem_erase.mp hselectedmem).1
  rw [hzero, add_zero]
open _root_.P2M8f8f5b7e renaming h305 → CurrentAFT.RootLegNormalized.completeFamily_zeroArity
open _root_.P2M8f8f5b7e renaming h305 → _p2mH305
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h304 (security order : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.RootLegNormalized.Palette security) → ℝ)
    (bodyForms : _root_.CurrentAFT.ActualControls.SafePalette security → MvPolynomial (_root_.CurrentAFT.RootLegNormalized.Palette security) ℝ)
    (hbody : ∀ center, (bodyForms center).IsHomogeneous 1) :
    _root_.CurrentAFT.LocalCoefficientEvaluation.evaluation security order bodyForms hbody (_root_.CurrentAFT.RootLegNormalized.completeFamily security order mass) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight mass) := by
  unfold _root_.CurrentAFT.RootLegNormalized.completeFamily
  simp only [map_add, map_smul, map_one, map_sum, _p2mH285]
  have hexpand := _p2mH3 (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
    (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) (_root_.CurrentAFT.ActualControls.primaryReference_positive security) mass
  rw [hexpand]
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Finset (Fin 3)))
    (_root_.AFT.RepresentedPolynomial.referenceCoefficientForm (_root_.CurrentAFT.ProposalPrimary.primaryLaw security)
      (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security) mass) (Finset.mem_univ ∅)
  rw [_p2mH12] at hsplit
  rw [← hsplit, map_add, map_sum]
  have hconstant : _root_.CurrentAFT.TruncatedOutput.quotientMap order (MvPolynomial.C (∑ word, mass word)) =
      (∑ word, mass word) • (1 : _root_.CurrentAFT.TruncatedOutput.Polynomial (_root_.CurrentAFT.RootLegNormalized.Palette security) order) := by
    rw [Algebra.smul_def, mul_one]
    exact (_root_.CurrentAFT.TruncatedOutput.quotientMap order).commutes _
  rw [hconstant, add_comm]
open _root_.P2M8f8f5b7e renaming h304 → _p2mH304
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h306 (security order : ℕ) (law : _root_.AFT.FiniteDist (Fin 3 → _root_.CurrentAFT.RootLegNormalized.Palette security)) :
    _root_.CurrentAFT.RootLegNormalized.positiveFamily security order law (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = (1 : _root_.CurrentAFT.RootLegCoefficientFamily.Family security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) := by
  rw [_root_.CurrentAFT.RootLegNormalized.positiveFamily, _p2mH305, law.sum_one, one_smul]
open _root_.P2M8f8f5b7e renaming h306 → _p2mH306
end
open _root_.P2M8f8f5b7e renaming h304 → _p2mH304
open _root_.P2M8f8f5b7e renaming h305 → CurrentAFT.RootLegNormalized.completeFamily_zeroArity
open _root_.P2M8f8f5b7e renaming h305 → _p2mH305
open _root_.P2M8f8f5b7e renaming h306 → _p2mH306
end CurrentAFT.RootLegNormalized
open _root_.P2M8f8f5b7e renaming h304 → _p2mH304
open _root_.P2M8f8f5b7e renaming h305 → CurrentAFT.RootLegNormalized.completeFamily_zeroArity
open _root_.P2M8f8f5b7e renaming h305 → _p2mH305
open _root_.P2M8f8f5b7e renaming h306 → _p2mH306
end
open _root_.P2M8f8f5b7e renaming h304 → _p2mH304
open _root_.P2M8f8f5b7e renaming h305 → CurrentAFT.RootLegNormalized.completeFamily_zeroArity
open _root_.P2M8f8f5b7e renaming h305 → _p2mH305
open _root_.P2M8f8f5b7e renaming h306 → _p2mH306
namespace CurrentAFT.RootLegNormalized
end CurrentAFT.RootLegNormalized
namespace CurrentAFT.RootLegNormalized.positiveFamily
end CurrentAFT.RootLegNormalized.positiveFamily
section
namespace CurrentAFT.RootLegReciprocal
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls
  LocalReferenceEnergy ActualBlockFock RootIndependentBackground RootBackgroundPolynomial
  CycleRootExpansion RootTaggedLegHigher RootLegCoefficientFamily RootLegCoefficientNorm
  RootLegCoefficientLinear RootLegCoefficientBounds RootLegNormalized PrimaryOnlyFamily
  ControlCoordinates GradedControlAlgebra GradedControlNorm GradedControlStability GradedInverse GradedInverseNorm
  BackgroundFamilies BackgroundRates BackgroundEvaluation
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
attribute [local instance] _root_.CurrentAFT.RootLegReciprocal.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h308 (security : ℕ) :
    _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.RootLegReciprocal.meanPositiveLaw security) = _root_.CurrentAFT.LegPolynomialEvaluation.legGenerating security := by
  rw [_root_.CurrentAFT.RootLegReciprocal.meanPositiveLaw, _p2mH271]
  exact _p2mH274 security
open _root_.P2M8f8f5b7e renaming h308 → _p2mH308
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h310 (security order : ℕ) :
    _root_.CurrentAFT.RootLegReciprocal.positive security order (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) = (1 : _root_.CurrentAFT.BackgroundFamilies.ActualFamily security order) (_root_.CurrentAFT.GradedControlAlgebra.zeroArity order) :=
  _p2mH306 security order _
open _root_.P2M8f8f5b7e renaming h310 → _p2mH310
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h311 (security order : ℕ) : _root_.CurrentAFT.RootLegReciprocal.reciprocal security order * _root_.CurrentAFT.RootLegReciprocal.positive security order = 1 :=
  _p2mH128 _ _ _ _ (_p2mH310 security order)
open _root_.P2M8f8f5b7e renaming h311 → _p2mH311
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h312 (security order : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ) (selected : Finset (Fin 3)) :
    _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily security order mass selected) := by
  unfold _root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily
  split_ifs
  · exact _p2mH210 _ _ _ _ rfl _
  · exact _p2mH213 _ _ _
open _root_.P2M8f8f5b7e renaming h312 → _p2mH312
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h307 (security order : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.ActualControls.Palette security) → ℝ) :
    _root_.CurrentAFT.PrimaryOnlyFamily.PrimaryOnly (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order (_root_.CurrentAFT.RootLegNormalized.completeFamily security order mass) := by
  unfold _root_.CurrentAFT.RootLegNormalized.completeFamily
  apply _p2mH208
  · exact _p2mH211 _ _ _ _ _ (_p2mH209 _ _ _)
  · apply _p2mH212
    intro selected _
    exact _p2mH312 security order mass selected
open _root_.P2M8f8f5b7e renaming h307 → _p2mH307
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h309 (security order : ℕ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootLegReciprocal.positive security order) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LegPolynomialEvaluation.legGenerating security) := by
  have h := _p2mH304 security order (_root_.CurrentAFT.RootLegReciprocal.meanPositiveLaw security).weight
    (_root_.CurrentAFT.BackgroundEvaluation.bodyForm security) (_root_.CurrentAFT.BackgroundEvaluation.bodyForm_homogeneous security)
  have hpoly : _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.RootLegReciprocal.meanPositiveLaw security).weight =
      _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.RootLegReciprocal.meanPositiveLaw security) := by
    have huniform : (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight = _root_.CurrentAFT.FringeCertificate.uniformProfile security := by
      funext color
      rw [_root_.CurrentAFT.LocalReferenceEnergy.uniformReference_weight]
      simp only [_root_.CurrentAFT.FringeCertificate.uniformProfile, one_div]
    simp only [_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear, _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating, _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating,
      LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def, MvPolynomial.algebraMap_eq]
    rw [huniform]
  rw [hpoly, _p2mH308] at h
  exact h
open _root_.P2M8f8f5b7e renaming h309 → _p2mH309
end
open _root_.P2M8f8f5b7e renaming h307 → _p2mH307
open _root_.P2M8f8f5b7e renaming h308 → _p2mH308
open _root_.P2M8f8f5b7e renaming h309 → _p2mH309
open _root_.P2M8f8f5b7e renaming h310 → _p2mH310
open _root_.P2M8f8f5b7e renaming h311 → _p2mH311
open _root_.P2M8f8f5b7e renaming h312 → _p2mH312
end CurrentAFT.RootLegReciprocal
open _root_.P2M8f8f5b7e renaming h307 → _p2mH307
open _root_.P2M8f8f5b7e renaming h308 → _p2mH308
open _root_.P2M8f8f5b7e renaming h309 → _p2mH309
open _root_.P2M8f8f5b7e renaming h310 → _p2mH310
open _root_.P2M8f8f5b7e renaming h311 → _p2mH311
open _root_.P2M8f8f5b7e renaming h312 → _p2mH312
end
open _root_.P2M8f8f5b7e renaming h307 → _p2mH307
open _root_.P2M8f8f5b7e renaming h308 → _p2mH308
open _root_.P2M8f8f5b7e renaming h309 → _p2mH309
open _root_.P2M8f8f5b7e renaming h310 → _p2mH310
open _root_.P2M8f8f5b7e renaming h311 → _p2mH311
open _root_.P2M8f8f5b7e renaming h312 → _p2mH312
namespace CurrentAFT.RootBackgroundPolynomial.blockGenerating
end CurrentAFT.RootBackgroundPolynomial.blockGenerating
namespace CurrentAFT.RootLegReciprocal
end CurrentAFT.RootLegReciprocal
namespace CurrentAFT.RootLegReciprocal.meanPositiveLaw
end CurrentAFT.RootLegReciprocal.meanPositiveLaw
section
namespace CurrentAFT.RootUnselectedChannels
open AFT DiffuseProfiles ProposalPrimary ActualControls UniformBodyProfiles CycleRootExpansion
  RootTaggedLocal RootTaggedFamilies RootLegCoefficientFamily RootLegCoefficientLinear RootLegCoefficientBounds
  RootLegReciprocal PrimaryOnlyFamily ControlCoordinates GradedControlAlgebra
  GradedControlNorm GradedControlStability BackgroundFamilies BackgroundRates BackgroundEvaluation
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw bodyReference rootReference
attribute [local instance] _root_.CurrentAFT.RootUnselectedChannels.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h361 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) : _root_.CurrentAFT.RootUnselectedChannels.singletonChannel security order horder role queue input *
      _root_.CurrentAFT.RootMeanPrimary.positiveFamily security order horder role queue = _root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear security order horder role queue input := by
  change (_ * _root_.CurrentAFT.RootMeanPrimary.positiveInverse security order horder role queue) * _ = _
  rw [mul_assoc, _p2mH325, mul_one]
open _root_.P2M8f8f5b7e renaming h361 → _p2mH361
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h362 (security order : ℕ) (horder : 1 ≤ order) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootUnselectedChannels.singletonChannel security order horder role queue input) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.singleGenerating
        (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.RootTaggedLocal.meanLaw security role queue).weight) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.RootTaggedLocal.rootMass security role queue input)) := by
  rw [← _p2mH323 security order horder role queue,
    ← map_mul, _p2mH361, _p2mH346]
open _root_.P2M8f8f5b7e renaming h362 → _p2mH362
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h360 (security order : ℕ) (horder : 1 ≤ order) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.CurrentAFT.RootUnselectedChannels.legChannel security order horder input * _root_.CurrentAFT.RootLegReciprocal.positive security order = _root_.CurrentAFT.RootUnselectedChannels.legNumeratorLinear security order horder input := by
  change (_ * _root_.CurrentAFT.RootLegReciprocal.reciprocal security order) * _ = _
  rw [mul_assoc, _p2mH311, mul_one]
open _root_.P2M8f8f5b7e renaming h360 → _p2mH360
end
open _root_.P2M8f8f5b7e renaming h360 → _p2mH360
open _root_.P2M8f8f5b7e renaming h361 → _p2mH361
open _root_.P2M8f8f5b7e renaming h362 → _p2mH362
end CurrentAFT.RootUnselectedChannels
open _root_.P2M8f8f5b7e renaming h360 → _p2mH360
open _root_.P2M8f8f5b7e renaming h361 → _p2mH361
open _root_.P2M8f8f5b7e renaming h362 → _p2mH362
end
open _root_.P2M8f8f5b7e renaming h360 → _p2mH360
open _root_.P2M8f8f5b7e renaming h361 → _p2mH361
open _root_.P2M8f8f5b7e renaming h362 → _p2mH362
namespace CurrentAFT.RootMeanPrimary.positiveInverse
end CurrentAFT.RootMeanPrimary.positiveInverse
namespace CurrentAFT.RootUnselectedChannels
end CurrentAFT.RootUnselectedChannels
namespace CurrentAFT.RootUnselectedChannels.legNumeratorLinear
end CurrentAFT.RootUnselectedChannels.legNumeratorLinear
section
namespace CurrentAFT.RootLegFirstCoefficient
open AFT DiffuseProfiles ProposalPrimary ActualControls ControlCoordinates ControlProduct ControlNorm
  GradedControlAlgebra GradedControlNorm GradedControlStability RootLegCoefficientFamily RootLegCoefficientNorm
  RootLegNormalized RootLegReciprocal LocalRaisingFirst BackgroundFamilies LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootLegFirstCoefficient.classicalFinDecidableEq
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h293 (security order : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) → ℝ)
    (arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order) (hbody : 0 < arity.val.2.val) :
    _root_.CurrentAFT.RootLegNormalized.completeFamily security order mass arity = 0 := _p2mH307 security order mass arity hbody
open _root_.P2M8f8f5b7e renaming h293 → _p2mH293
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h297 (security : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) → ℝ)
    (slot : Fin 3) (hdegree : Fintype.card ({slot} : Finset (Fin 3)) = 1) (color : _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) :
    _root_.CurrentAFT.RootLegCoefficientFamily.selectedDensity security 1 mass {slot} hdegree (fun _ => color) =
      ((∑ word, if word slot = color then mass word else 0) -
        (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight color * ∑ word, mass word) /
          (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color := by
  unfold _root_.CurrentAFT.RootLegCoefficientFamily.selectedDensity
  rw [_root_.AFT.LocalTensors.referenceRestrictedComponent_singleton]
  rfl
open _root_.P2M8f8f5b7e renaming h297 → _p2mH297
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h300 (security : ℕ) (mass : (Fin 3 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) → ℝ)
    (selected : Finset (Fin 3)) (hdegree : Fintype.card selected = 1)
    (colors : Fin 1 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) (centers : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) :
    (_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security 1 mass selected hdegree).val colors centers =
      _root_.CurrentAFT.RootLegCoefficientFamily.normalizedSelectedDensity security 1 mass selected hdegree colors := by
  change _root_.CurrentAFT.ControlProduct.symmetrize (fun colors (_ : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security) =>
    _root_.CurrentAFT.RootLegCoefficientFamily.normalizedSelectedDensity security 1 mass selected hdegree colors) colors centers = _
  rw [_root_.CurrentAFT.ControlProduct.symmetrize_of_symmetric]
  intro primaryOrder bodyOrder input _
  congr 1
  funext index
  have hi : primaryOrder index = index := Subsingleton.elim _ _
  simp only [Function.comp_apply, hi]
open _root_.P2M8f8f5b7e renaming h300 → _p2mH300
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h299 (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 3 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) → ℝ) (slot : Fin 3) (color : _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) :
    _root_.CurrentAFT.BackgroundFamilies.primaryCoefficient (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder
      (_root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily security order mass {slot}) color =
      _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security (fun input =>
        ((∑ word, if word slot = input then mass word else 0) -
          (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight input * ∑ word, mass word) /
            (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight input) color := by
  have hsingle : _root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily security order mass {slot} =
      Pi.single (_root_.CurrentAFT.BackgroundFamilies.primaryArity order horder) (_root_.CurrentAFT.RootLegCoefficientFamily.selectedKernel security 1 mass {slot} (by simp)) := by
    unfold _root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily
    rw [dif_pos (by simpa using horder)]
    unfold _root_.CurrentAFT.RootLegCoefficientFamily.selectedArity _root_.CurrentAFT.BackgroundFamilies.primaryArity
    rfl
  rw [hsingle]
  unfold _root_.CurrentAFT.BackgroundFamilies.primaryCoefficient
  rw [Pi.single_eq_same]
  rw [_p2mH300]
  unfold _root_.CurrentAFT.RootLegCoefficientFamily.normalizedSelectedDensity
  change _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security
    (fun input => _root_.CurrentAFT.RootLegCoefficientFamily.selectedDensity security 1 mass {slot} _ (Fin.cons input Fin.elim0)) color = _
  apply congrArg (fun f => _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security f color)
  funext input
  have hword : Fin.cons input Fin.elim0 = (fun _ : Fin 1 => input) := by
    funext index
    have hi := Fin.eq_zero index
    subst index
    rfl
  rw [hword]
  exact _p2mH297 security mass slot _ input
open _root_.P2M8f8f5b7e renaming h299 → _p2mH299
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h298 (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 3 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) → ℝ) (selected : Finset (Fin 3)) (hcard : selected.card ≠ 1) :
    _root_.CurrentAFT.LocalRaisingFirst.primaryProjection (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder
      (_root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily security order mass selected) = 0 := by
  funext color
  unfold _root_.CurrentAFT.LocalRaisingFirst.primaryProjection _root_.CurrentAFT.BackgroundFamilies.primaryCoefficient _root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  split_ifs with hdegree
  · rw [Pi.single_eq_of_ne]
    · rfl
    · intro hequal
      have h := congrArg (fun arity : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => arity.val.1.val) hequal
      exact hcard h.symm
  · rfl
open _root_.P2M8f8f5b7e renaming h298 → _p2mH298
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h412 {Slot : Type*} [Fintype Slot] [DecidableEq Slot]
    (term : Finset Slot → ℝ) (hzero : ∀ selected, selected.card ≠ 1 → term selected = 0) :
    (∑ selected ∈ (Finset.univ : Finset (Finset Slot)).erase ∅, term selected) =
      ∑ slot, term {slot} := by
  let singles := (Finset.univ : Finset (Finset Slot)).filter (fun selected => selected.card = 1)
  have hsubset : singles ⊆ (Finset.univ : Finset (Finset Slot)).erase ∅ := by
    intro selected hselected
    apply Finset.mem_erase.mpr
    constructor
    · intro hequal
      have hcard := (Finset.mem_filter.mp hselected).2
      rw [hequal, Finset.card_empty] at hcard
      omega
    · exact Finset.mem_univ _
  have hreduce : (∑ selected ∈ singles, term selected) =
      ∑ selected ∈ (Finset.univ : Finset (Finset Slot)).erase ∅, term selected := by
    apply Finset.sum_subset hsubset
    intro selected _ hnot
    apply hzero
    intro hcard
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩)
  rw [← hreduce]
  symm
  apply Finset.sum_bij (fun slot _ => ({slot} : Finset Slot))
  · intro slot _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_singleton _⟩
  · intro first _ second _ hequal
    exact Finset.singleton_injective hequal
  · intro selected hselected
    obtain ⟨slot, hequal⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hselected).2
    exact ⟨slot, Finset.mem_univ _, hequal.symm⟩
  · intro slot _
    rfl
open _root_.P2M8f8f5b7e renaming h412 → CurrentAFT.RootLegFirstCoefficient.sum_nonempty_singletons
open _root_.P2M8f8f5b7e renaming h412 → _p2mH412
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h294 (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 3 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    _root_.CurrentAFT.BackgroundFamilies.primaryCoefficient (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder
      (_root_.CurrentAFT.RootLegNormalized.completeFamily security order mass) =
        _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security
          (fun color => _root_.AFT.LocalTensors.signedColorCount mass color / (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight color) := by
  change _root_.CurrentAFT.LocalRaisingFirst.primaryProjection (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order horder
    (_root_.CurrentAFT.RootLegNormalized.completeFamily security order mass) = _
  unfold _root_.CurrentAFT.RootLegNormalized.completeFamily
  rw [map_add, map_smul, _root_.CurrentAFT.LocalRaisingFirst.primaryProjection_one, smul_zero, zero_add, map_sum]
  funext color
  simp only [Finset.sum_apply]
  rw [_p2mH412 _ (fun selected hcard =>
    congrFun (_p2mH298 security order horder mass selected hcard) color)]
  simp only [_root_.CurrentAFT.LocalRaisingFirst.primaryProjection, LinearMap.coe_mk, AddHom.coe_mk, _p2mH299,
    hmass, mul_zero, sub_zero]
  have hsum : (∑ slot : Fin 3, _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security
      (fun input => (∑ word, if word slot = input then mass word else 0) /
        (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight input) color) =
      _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security
        (∑ slot : Fin 3, fun input => (∑ word, if word slot = input then mass word else 0) /
          (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).weight input) color := by
    rw [map_sum]
    simp only [Finset.sum_apply]
  rw [hsum]
  apply congrArg (fun f => _root_.CurrentAFT.PrimaryTensorInverse.densityInverse security f color)
  funext input
  simp only [Finset.sum_apply, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  unfold _root_.AFT.LocalTensors.signedColorCount
  apply Finset.sum_congr rfl
  intro word _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot _
  split_ifs <;> simp
open _root_.P2M8f8f5b7e renaming h294 → _p2mH294
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h296 (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 3 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    _root_.CurrentAFT.GradedInverse.VanishesBelow (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order 2
      (_root_.CurrentAFT.RootLegNormalized.completeFamily security order mass - _root_.CurrentAFT.RootLegFirstCoefficient.firstFamily security order horder mass) := by
  intro arity hsmall
  change _root_.CurrentAFT.RootLegNormalized.completeFamily security order mass arity - _root_.CurrentAFT.RootLegFirstCoefficient.firstFamily security order horder mass arity = 0
  by_cases hb : 0 < arity.val.2.val
  · rw [_p2mH293 security order mass arity hb]
    unfold _root_.CurrentAFT.RootLegFirstCoefficient.firstFamily _root_.CurrentAFT.BackgroundFamilies.primaryFamily
    rw [Pi.single_eq_of_ne, sub_zero]
    intro hequal
    have h := congrArg (fun item : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => item.val.2.val) hequal
    change arity.val.2.val = 0 at h
    omega
  · have hs : arity.val.2.val = 0 := by omega
    by_cases hr : arity.val.1.val = 0
    · have harity : arity = _root_.CurrentAFT.GradedControlAlgebra.zeroArity order := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hr) (Fin.ext hs)
      subst arity
      rw [_p2mH305, hmass, zero_smul]
      unfold _root_.CurrentAFT.RootLegFirstCoefficient.firstFamily _root_.CurrentAFT.BackgroundFamilies.primaryFamily
      rw [Pi.single_eq_of_ne, sub_zero]
      intro hequal
      have h := congrArg (fun item : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => item.val.1.val) hequal
      change 0 = 1 at h
      omega
    · have hrone : arity.val.1.val = 1 := by omega
      have harity : arity = _root_.CurrentAFT.BackgroundFamilies.primaryArity order horder := by
        apply Subtype.ext
        exact Prod.ext (Fin.ext hrone) (Fin.ext hs)
      subst arity
      apply sub_eq_zero.mpr
      unfold _root_.CurrentAFT.RootLegFirstCoefficient.firstFamily _root_.CurrentAFT.BackgroundFamilies.primaryFamily
      rw [Pi.single_eq_same]
      apply Subtype.ext
      funext (colors : Fin 1 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) (centers : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security)
      have hcolors : colors = (fun _ => colors 0) := by
        funext index
        have hi := Fin.eq_zero index
        subst index
        rfl
      have hcenters : centers = Fin.elim0 := Subsingleton.elim _ _
      rw [hcolors, hcenters]
      rfl
open _root_.P2M8f8f5b7e renaming h296 → _p2mH296
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h295 (security order : ℕ) (horder : 1 ≤ order)
    (mass : (Fin 3 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) → ℝ) (hmass : ∑ word, mass word = 0) :
    _root_.CurrentAFT.RootLegNormalized.completeFamily security order mass = _root_.CurrentAFT.RootLegFirstCoefficient.firstFamily security order horder mass + _root_.CurrentAFT.RootLegCoefficientFamily.higherFamily security order mass := by
  funext arity
  change _root_.CurrentAFT.RootLegNormalized.completeFamily security order mass arity = _root_.CurrentAFT.RootLegFirstCoefficient.firstFamily security order horder mass arity + _root_.CurrentAFT.RootLegCoefficientFamily.higherFamily security order mass arity
  by_cases hsmall : arity.val.1.val + arity.val.2.val < 2
  · rw [_root_.CurrentAFT.RootLegCoefficientFamily.higherFamily_vanishesBelow security order mass arity hsmall, add_zero]
    exact sub_eq_zero.mp (_p2mH296 security order horder mass hmass arity hsmall)
  · have hfirst : _root_.CurrentAFT.RootLegFirstCoefficient.firstFamily security order horder mass arity = 0 := by
      unfold _root_.CurrentAFT.RootLegFirstCoefficient.firstFamily _root_.CurrentAFT.BackgroundFamilies.primaryFamily
      rw [Pi.single_eq_of_ne]
      intro hequal
      have h := congrArg (fun item : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => item.val.1.val + item.val.2.val) hequal
      change arity.val.1.val + arity.val.2.val = 1 + 0 at h
      omega
    rw [hfirst, zero_add]
    unfold _root_.CurrentAFT.RootLegNormalized.completeFamily _root_.CurrentAFT.RootLegCoefficientFamily.higherFamily
    simp only [hmass, zero_smul, zero_add, Finset.sum_apply]
    symm
    apply Finset.sum_subset
    · intro selected hselected
      apply Finset.mem_erase.mpr
      constructor
      · intro hequal
        have hcard := (Finset.mem_filter.mp hselected).2
        rw [hequal, Finset.card_empty] at hcard
        omega
      · exact Finset.mem_univ _
    · intro selected _ hnot
      have hcard : selected.card < 2 := by
        by_contra! hcard
        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcard⟩)
      unfold _root_.CurrentAFT.RootLegCoefficientFamily.selectedFamily
      split_ifs with hdegree
      · rw [Pi.single_eq_of_ne]
        intro hequal
        have h := congrArg (fun item : _root_.CurrentAFT.GradedControlAlgebra.TruncatedArity order => item.val.1.val + item.val.2.val) hequal
        change arity.val.1.val + arity.val.2.val = selected.card + 0 at h
        omega
      · rfl
open _root_.P2M8f8f5b7e renaming h295 → _p2mH295
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h301 {Slot Color : Type*} [Fintype Slot] [Fintype Color]
    (law : _root_.AFT.FiniteDist (Slot → Color)) (color : Color) :
    _root_.AFT.LocalTensors.signedColorCount law.weight color =
      ∑ slot, (law.map (fun word => word slot)).weight color := by
  unfold _root_.AFT.LocalTensors.signedColorCount
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro slot _
  rw [_root_.AFT.FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro word _
  split_ifs <;> simp
open _root_.P2M8f8f5b7e renaming h301 → _p2mH301
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h302 (security : ℕ) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) (color : _root_.CurrentAFT.RootLegFirstCoefficient.Palette security) :
    _root_.AFT.LocalTensors.signedColorCount (_root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear security input) color =
      ∑ root, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root * input root *
        _root_.CurrentAFT.RootTaggedLegFirst.legHistogram security root color := by
  unfold _root_.AFT.LocalTensors.signedColorCount _root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro root _
  have hhist := _p2mH301 (_root_.CurrentAFT.ActualBlockFock.primaryLawAt security root.val) color
  unfold _root_.CurrentAFT.RootTaggedLegFirst.legHistogram
  rw [← hhist]
  unfold _root_.AFT.LocalTensors.signedColorCount
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  ring
open _root_.P2M8f8f5b7e renaming h302 → _p2mH302
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h303 (security : ℕ) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.AFT.LocalTensors.signedColorCount (_root_.CurrentAFT.RootTaggedLegHigher.massLinear security input) =
      _root_.CurrentAFT.RootTaggedLocal.rootMass security .attachment 0 input := by
  funext color
  change _root_.AFT.LocalTensors.signedColorCount (_root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear security
    (_root_.AFT.TensorChannel.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) input)) color = _
  rw [_p2mH302]
  rw [← _p2mH348]
  simp only [_root_.AFT.TensorChannel.center_apply, _root_.CurrentAFT.RootTaggedLegFirst.legFirstMass, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.CurrentAFT.RootTaggedLegFirst.meanLegHistogram, _root_.AFT.FiniteDist.expectation, mul_sub, sub_mul, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro root _
  ring
open _root_.P2M8f8f5b7e renaming h303 → _p2mH303
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h291 (security order : ℕ) (horder : 1 ≤ order) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.CurrentAFT.RootLegFirstCoefficient.firstScore security order horder (_root_.CurrentAFT.RootTaggedLegHigher.massLinear security input) =
      _root_.CurrentAFT.RootTaggedLocal.rootLift security .attachment 0 input := by
  unfold _root_.CurrentAFT.RootLegFirstCoefficient.firstScore
  rw [_p2mH294 security order horder _ (_p2mH351 security input),
    _p2mH303, _root_.CurrentAFT.RootTaggedLocal.rootLift_apply]
  congr 1
  funext color
  exact (_root_.CurrentAFT.RootTaggedLocal.profileDensity_apply security _ color).symm
open _root_.P2M8f8f5b7e renaming h291 → _p2mH291
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h290 (security order : ℕ) (horder : 1 ≤ order) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.CurrentAFT.RootLegFirstCoefficient.firstFamily security order horder (_root_.CurrentAFT.RootTaggedLegHigher.massLinear security input) =
      _root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear security order horder .attachment 0 input := by
  unfold _root_.CurrentAFT.RootLegFirstCoefficient.firstFamily
  rw [_root_.CurrentAFT.RootTaggedFamilies.rootFamilyLinear_apply]
  have hscore := _p2mH291 security order horder input
  funext arity
  by_cases hequal : arity = _root_.CurrentAFT.BackgroundFamilies.primaryArity order horder
  · subst arity
    simp only [_root_.CurrentAFT.BackgroundFamilies.primaryFamily, Pi.single_eq_same]
    apply Subtype.ext
    change (fun colors : Fin 1 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security => fun _ : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security =>
      _root_.CurrentAFT.RootLegFirstCoefficient.firstScore security order horder (_root_.CurrentAFT.RootTaggedLegHigher.massLinear security input) (colors 0)) =
        (fun colors : Fin 1 → _root_.CurrentAFT.RootLegFirstCoefficient.Palette security => fun _ : Fin 0 → _root_.CurrentAFT.ActualControls.SafePalette security =>
          _root_.CurrentAFT.RootTaggedLocal.rootLift security .attachment 0 input (colors 0))
    funext colors centers
    exact congrFun hscore (colors 0)
  · simp only [_root_.CurrentAFT.BackgroundFamilies.primaryFamily, Pi.single_eq_of_ne hequal]
open _root_.P2M8f8f5b7e renaming h290 → _p2mH290
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h289 (security order : ℕ) (horder : 1 ≤ order) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.CurrentAFT.RootLegNormalized.completeFamily security order (_root_.CurrentAFT.RootTaggedLegHigher.massLinear security input) =
      _root_.CurrentAFT.RootUnselectedChannels.legNumeratorLinear security order horder input := by
  rw [_p2mH295 security order horder _ (_p2mH351 security input), _p2mH290]
  rw [_root_.CurrentAFT.RootUnselectedChannels.legNumeratorLinear, LinearMap.add_apply, _root_.CurrentAFT.RootLegCoefficientLinear.rootHigherLinear_apply]
  rfl
open _root_.P2M8f8f5b7e renaming h289 → _p2mH289
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h292 (security order : ℕ) (horder : 1 ≤ order) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootUnselectedChannels.legChannel security order horder input) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.LegPolynomialEvaluation.legGenerating security) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
          (_root_.CurrentAFT.RootTaggedLegHigher.massLinear security input)) := by
  rw [← _p2mH309, ← map_mul, _p2mH360,
    ← _p2mH289]
  exact _p2mH304 security order _ _ _
open _root_.P2M8f8f5b7e renaming h292 → _p2mH292
end
open _root_.P2M8f8f5b7e renaming h289 → _p2mH289
open _root_.P2M8f8f5b7e renaming h290 → _p2mH290
open _root_.P2M8f8f5b7e renaming h291 → _p2mH291
open _root_.P2M8f8f5b7e renaming h292 → _p2mH292
open _root_.P2M8f8f5b7e renaming h293 → _p2mH293
open _root_.P2M8f8f5b7e renaming h294 → _p2mH294
open _root_.P2M8f8f5b7e renaming h295 → _p2mH295
open _root_.P2M8f8f5b7e renaming h296 → _p2mH296
open _root_.P2M8f8f5b7e renaming h297 → _p2mH297
open _root_.P2M8f8f5b7e renaming h298 → _p2mH298
open _root_.P2M8f8f5b7e renaming h299 → _p2mH299
open _root_.P2M8f8f5b7e renaming h300 → _p2mH300
open _root_.P2M8f8f5b7e renaming h301 → _p2mH301
open _root_.P2M8f8f5b7e renaming h302 → _p2mH302
open _root_.P2M8f8f5b7e renaming h303 → _p2mH303
open _root_.P2M8f8f5b7e renaming h412 → CurrentAFT.RootLegFirstCoefficient.sum_nonempty_singletons
open _root_.P2M8f8f5b7e renaming h412 → _p2mH412
end CurrentAFT.RootLegFirstCoefficient
open _root_.P2M8f8f5b7e renaming h289 → _p2mH289
open _root_.P2M8f8f5b7e renaming h290 → _p2mH290
open _root_.P2M8f8f5b7e renaming h291 → _p2mH291
open _root_.P2M8f8f5b7e renaming h292 → _p2mH292
open _root_.P2M8f8f5b7e renaming h293 → _p2mH293
open _root_.P2M8f8f5b7e renaming h294 → _p2mH294
open _root_.P2M8f8f5b7e renaming h295 → _p2mH295
open _root_.P2M8f8f5b7e renaming h296 → _p2mH296
open _root_.P2M8f8f5b7e renaming h297 → _p2mH297
open _root_.P2M8f8f5b7e renaming h298 → _p2mH298
open _root_.P2M8f8f5b7e renaming h299 → _p2mH299
open _root_.P2M8f8f5b7e renaming h300 → _p2mH300
open _root_.P2M8f8f5b7e renaming h301 → _p2mH301
open _root_.P2M8f8f5b7e renaming h302 → _p2mH302
open _root_.P2M8f8f5b7e renaming h303 → _p2mH303
open _root_.P2M8f8f5b7e renaming h412 → CurrentAFT.RootLegFirstCoefficient.sum_nonempty_singletons
open _root_.P2M8f8f5b7e renaming h412 → _p2mH412
end
open _root_.P2M8f8f5b7e renaming h289 → _p2mH289
open _root_.P2M8f8f5b7e renaming h290 → _p2mH290
open _root_.P2M8f8f5b7e renaming h291 → _p2mH291
open _root_.P2M8f8f5b7e renaming h292 → _p2mH292
open _root_.P2M8f8f5b7e renaming h293 → _p2mH293
open _root_.P2M8f8f5b7e renaming h294 → _p2mH294
open _root_.P2M8f8f5b7e renaming h295 → _p2mH295
open _root_.P2M8f8f5b7e renaming h296 → _p2mH296
open _root_.P2M8f8f5b7e renaming h297 → _p2mH297
open _root_.P2M8f8f5b7e renaming h298 → _p2mH298
open _root_.P2M8f8f5b7e renaming h299 → _p2mH299
open _root_.P2M8f8f5b7e renaming h300 → _p2mH300
open _root_.P2M8f8f5b7e renaming h301 → _p2mH301
open _root_.P2M8f8f5b7e renaming h302 → _p2mH302
open _root_.P2M8f8f5b7e renaming h303 → _p2mH303
namespace CurrentAFT.RootLegFirstCoefficient
end CurrentAFT.RootLegFirstCoefficient
namespace CurrentAFT.RootLegFirstCoefficient.firstScore
end CurrentAFT.RootLegFirstCoefficient.firstScore
namespace CurrentAFT.RootLegFirstCoefficient.sum_nonempty_singletons
end CurrentAFT.RootLegFirstCoefficient.sum_nonempty_singletons
section
namespace CurrentAFT.RootUnselectedBlockChannel
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls LocalReferenceEnergy
  ActualBlockFock UniformBodyProfiles CycleSelections CycleRootExpansion RootTaggedLocal
  RootTaggedFamilies RootUnselectedChannels RootLegCoefficientBounds RootLegCoefficientLinear
  RootLegFirstCoefficient PrimaryOnlyFamily BackgroundFamilies BackgroundRates BackgroundEvaluation
  ControlCoordinates GradedControlAlgebra GradedControlNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize primaryLaw bodyReference rootReference
attribute [local instance] _root_.CurrentAFT.RootUnselectedBlockChannel.classicalFinDecidableEq
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h359 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security) (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootUnselectedBlockChannel.channel security order horder queue block input) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue block) =
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootUnselectedBlockChannel.numeratorPolynomial security queue input block) := by
  rcases block with leg | singleton
  · exact _p2mH292 security order horder input
  · rcases singleton with center | point
    · exact _p2mH362 security order horder .free 0 input
    · exact _p2mH362 security order horder .queue queue input
open _root_.P2M8f8f5b7e renaming h359 → _p2mH359
end
open _root_.P2M8f8f5b7e renaming h359 → _p2mH359
end CurrentAFT.RootUnselectedBlockChannel
open _root_.P2M8f8f5b7e renaming h359 → _p2mH359
end
open _root_.P2M8f8f5b7e renaming h359 → _p2mH359
namespace CurrentAFT.LocalRaisingFirst
end CurrentAFT.LocalRaisingFirst
namespace CurrentAFT.LocalRaisingFirst.primaryProjection
end CurrentAFT.LocalRaisingFirst.primaryProjection
namespace CurrentAFT.LocalRaisingFirst.sum_nonempty_singletons
end CurrentAFT.LocalRaisingFirst.sum_nonempty_singletons
namespace CurrentAFT.RootUnselectedBlockChannel
end CurrentAFT.RootUnselectedBlockChannel
namespace CurrentAFT.RootUnselectedBlockChannel.channel
end CurrentAFT.RootUnselectedBlockChannel.channel
section
namespace CurrentAFT.RootUnselectedGrouped
open AFT ActualBlockFock CycleRootExpansion RootTaggedFamilies RootUnselectedChannels
  RootLegCoefficientFamily RootLegCoefficientLinear GradedInverse LocalRaisingFirst
  ControlCoordinates GradedControlAlgebra BackgroundFamilies
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootUnselectedGrouped.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h363 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security) (score : _root_.CurrentAFT.RootUnselectedGrouped.Input security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootUnselectedGrouped.channel security order horder queue block score) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue block) =
        _root_.CurrentAFT.TruncatedOutput.quotientMap order
          (_root_.CurrentAFT.RootUnselectedBlockChannel.numeratorPolynomial security queue (_root_.CurrentAFT.RootUnselectedGrouped.extractLinear security score) block) :=
  _p2mH359 security order horder queue block (_root_.CurrentAFT.RootUnselectedGrouped.extractLinear security score)
open _root_.P2M8f8f5b7e renaming h363 → _p2mH363
end
open _root_.P2M8f8f5b7e renaming h363 → _p2mH363
end CurrentAFT.RootUnselectedGrouped
open _root_.P2M8f8f5b7e renaming h363 → _p2mH363
end
open _root_.P2M8f8f5b7e renaming h363 → _p2mH363
namespace AFT.JointPhysicalChannel
end AFT.JointPhysicalChannel
section
namespace CurrentAFT.TaggedPhysicalFock
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst
  PhysicalFockRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.TaggedPhysicalFock.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.dimension Parameters.legCount BackgroundRates.radius
  ProposalPrimary.primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h381 (security : ℕ) (compensatorRoot attachmentRoot : ℤ)
    (score : _root_.CurrentAFT.FirstHistogram.Palette security → ℝ) :
    _root_.CurrentAFT.TaggedPhysicalFock.averagedPairedChannel security compensatorRoot attachmentRoot score =
      ∑ scalar, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar •
        _root_.CurrentAFT.PairedReferenceEnergy.pairedMassAt security compensatorRoot attachmentRoot scalar score := by
  simp only [_root_.CurrentAFT.TaggedPhysicalFock.averagedPairedChannel, LinearMap.sum_apply, LinearMap.smul_apply, _root_.CurrentAFT.PairedReferenceEnergy.pairedMassLinear_apply]
open _root_.P2M8f8f5b7e renaming h381 → _p2mH381
end
open _root_.P2M8f8f5b7e renaming h381 → _p2mH381
end CurrentAFT.TaggedPhysicalFock
open _root_.P2M8f8f5b7e renaming h381 → _p2mH381
end
open _root_.P2M8f8f5b7e renaming h381 → _p2mH381
namespace CurrentAFT.SafeControlGroups
end CurrentAFT.SafeControlGroups
namespace CurrentAFT.SafeControlGroups.reference
end CurrentAFT.SafeControlGroups.reference
namespace CurrentAFT.TaggedPhysicalFock
end CurrentAFT.TaggedPhysicalFock
namespace CurrentAFT.TaggedPhysicalFock.averagedPairedChannel
end CurrentAFT.TaggedPhysicalFock.averagedPairedChannel
section
namespace CurrentAFT.OrdinaryPhysicalFock
open AFT DiffuseProfiles ProposalPrimary LocalReferenceEnergy PhysicalFockRates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.OrdinaryPhysicalFock.classicalFinDecidableEq
attribute [local irreducible] Parameters.base Parameters.dimension ProposalPrimary.centerLaw
  BackgroundRates.ordinaryPool BackgroundRates.radius
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h180 (security : ℕ) (score : _root_.CurrentAFT.OrdinaryPhysicalFock.SafePalette security → ℝ) (color : _root_.CurrentAFT.OrdinaryPhysicalFock.SafePalette security) :
    _root_.CurrentAFT.OrdinaryPhysicalFock.extendDensity security score color.val = score color := by
  simp only [_root_.CurrentAFT.OrdinaryPhysicalFock.extendDensity, LinearMap.coe_mk, AddHom.coe_mk, dif_pos color.property]
open _root_.P2M8f8f5b7e renaming h180 → _p2mH180
end
open _root_.P2M8f8f5b7e renaming h180 → _p2mH180
end CurrentAFT.OrdinaryPhysicalFock
open _root_.P2M8f8f5b7e renaming h180 → _p2mH180
end
open _root_.P2M8f8f5b7e renaming h180 → _p2mH180
namespace CurrentAFT.CycleRootExpansion
end CurrentAFT.CycleRootExpansion
namespace CurrentAFT.CycleRootExpansion.componentResponse
end CurrentAFT.CycleRootExpansion.componentResponse
namespace CurrentAFT.CycleRootExpansion.expectationLinear
end CurrentAFT.CycleRootExpansion.expectationLinear
namespace CurrentAFT.CycleRootExpansion.rootLaw
end CurrentAFT.CycleRootExpansion.rootLaw
section
namespace CurrentAFT.SelectedRootComponent
open AFT CycleSelections CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize
attribute [local instance] _root_.CurrentAFT.SelectedRootComponent.currentModulusNeZero
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h380 (security count : ℕ)
    (labels : _root_.CurrentAFT.CycleSelections.Selection (_root_.CurrentAFT.Parameters.bodySize security) count)
    (word : _root_.CurrentAFT.CycleRootExpansion.Vertex security → _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security count labels (word ∘ labels) =
      _root_.AFT.Hoeffding.densityComponent (fun _ => _root_.CurrentAFT.CycleRootExpansion.rootReference security) (_root_.CurrentAFT.CycleRootExpansion.rootLaw security).weight
        (Finset.univ.map labels) word := by
  unfold _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient _root_.CurrentAFT.CycleSelections.centeredRootDensity
  rw [_root_.AFT.FiniteDist.expectation_map]
  simp only [_root_.AFT.FiniteDist.expectation, _root_.AFT.Hoeffding.densityComponent, Finset.prod_map,
    Function.comp_apply, _root_.CurrentAFT.SupportedHoeffding.centeredRootAtom_eq]
  congr 3
  exact Subsingleton.elim _ _
open _root_.P2M8f8f5b7e renaming h380 → _p2mH380
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h378 {Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    (security count : ℕ) (labels : _root_.CurrentAFT.CycleSelections.Selection (_root_.CurrentAFT.Parameters.bodySize security) count)
    (test : (_root_.CurrentAFT.CycleRootExpansion.Vertex security → _root_.CurrentAFT.CycleRootExpansion.Root security) → Value) :
    _root_.CurrentAFT.CycleRootExpansion.actualComponent security (Finset.univ.map labels) test =
      ∑ word, ((_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security)).weight word *
        _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security count labels (word ∘ labels)) • test word := by
  simp only [_root_.CurrentAFT.CycleRootExpansion.actualComponent, _root_.CurrentAFT.CycleRootExpansion.componentResponse, LinearMap.coe_mk, AddHom.coe_mk,
    _p2mH380]
open _root_.P2M8f8f5b7e renaming h378 → _p2mH378
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h379 (security count : ℕ)
    (labels : _root_.CurrentAFT.CycleSelections.Selection (_root_.CurrentAFT.Parameters.bodySize security) count) (index : Fin count) :
    _root_.AFT.Hoeffding.CenteredAt (fun _ => _root_.CurrentAFT.CycleRootExpansion.rootReference security) index
      (_root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security count labels) := by
  let joint := (_root_.CurrentAFT.CycleRootExpansion.rootLaw security).map (fun roots slot => roots (labels slot))
  have hmarginal (slot : Fin count) :
      joint.map (fun roots => roots slot) = _root_.CurrentAFT.CycleRootExpansion.rootReference security := by
    dsimp only [joint]
    rw [_root_.AFT.FiniteDist.map_map]
    exact _p2mH96 security (labels slot)
  have hcanonical := _root_.CurrentAFT.SupportedHoeffding.densityComponent_canonical_of_support
    (fun _ : Fin count => _root_.CurrentAFT.CycleRootExpansion.rootReference security) joint.weight
    (_p2mH93 joint (fun _ => _root_.CurrentAFT.CycleRootExpansion.rootReference security) hmarginal) Finset.univ
  have hequal : _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security count labels =
      _root_.AFT.Hoeffding.densityComponent (fun _ : Fin count => _root_.CurrentAFT.CycleRootExpansion.rootReference security) joint.weight Finset.univ := by
    funext word
    simp only [_root_.CurrentAFT.CycleRootExpansion.selectedCoefficient, _root_.CurrentAFT.CycleSelections.centeredRootDensity, _root_.AFT.FiniteDist.expectation,
      _root_.AFT.Hoeffding.densityComponent, _root_.CurrentAFT.SupportedHoeffding.centeredRootAtom_eq, joint]
    congr 3
    exact Subsingleton.elim _ _
  rw [hequal]
  exact hcanonical.2 index (Finset.mem_univ index)
open _root_.P2M8f8f5b7e renaming h379 → _p2mH379
end
open _root_.P2M8f8f5b7e renaming h378 → _p2mH378
open _root_.P2M8f8f5b7e renaming h379 → _p2mH379
open _root_.P2M8f8f5b7e renaming h380 → _p2mH380
end CurrentAFT.SelectedRootComponent
open _root_.P2M8f8f5b7e renaming h378 → _p2mH378
open _root_.P2M8f8f5b7e renaming h379 → _p2mH379
open _root_.P2M8f8f5b7e renaming h380 → _p2mH380
end
open _root_.P2M8f8f5b7e renaming h378 → _p2mH378
open _root_.P2M8f8f5b7e renaming h379 → _p2mH379
open _root_.P2M8f8f5b7e renaming h380 → _p2mH380
namespace CurrentAFT.CycleRootExpansion.actualComponent
end CurrentAFT.CycleRootExpansion.actualComponent
namespace CurrentAFT.CycleRootExpansion.selectedCoefficient
end CurrentAFT.CycleRootExpansion.selectedCoefficient
namespace CurrentAFT.CycleSelections.centeredRootDensity
end CurrentAFT.CycleSelections.centeredRootDensity
namespace CurrentAFT.GroupedSourceNorm
end CurrentAFT.GroupedSourceNorm
namespace CurrentAFT.GroupedSourceNorm.globalReference
end CurrentAFT.GroupedSourceNorm.globalReference
namespace CurrentAFT.GroupedSourceNorm.groupReference
end CurrentAFT.GroupedSourceNorm.groupReference
namespace CurrentAFT.GroupedSourceNorm.wordEquiv
end CurrentAFT.GroupedSourceNorm.wordEquiv
namespace CurrentAFT.PairedRootPlacement
end CurrentAFT.PairedRootPlacement
namespace CurrentAFT.PairedRootPlacement.groupRootSlots
end CurrentAFT.PairedRootPlacement.groupRootSlots
namespace CurrentAFT.PairedRootPlacement.selectedRootEquiv
end CurrentAFT.PairedRootPlacement.selectedRootEquiv
namespace CurrentAFT.PairedRootPlacement.selectedRootSlots
end CurrentAFT.PairedRootPlacement.selectedRootSlots
namespace CurrentAFT.RaisingPatternBudget
end CurrentAFT.RaisingPatternBudget
namespace CurrentAFT.RaisingPatternBudget.roleReference
end CurrentAFT.RaisingPatternBudget.roleReference
namespace CurrentAFT.RaisingPatternBudget.roleReference.match_1
end CurrentAFT.RaisingPatternBudget.roleReference.match_1
namespace CurrentAFT.RaisingPatternKernel
end CurrentAFT.RaisingPatternKernel
namespace CurrentAFT.RaisingPatternKernel.inputJoint
end CurrentAFT.RaisingPatternKernel.inputJoint
namespace CurrentAFT.RaisingPatternKernel.localWeight
end CurrentAFT.RaisingPatternKernel.localWeight
namespace CurrentAFT.RaisingPatternKernel.patternKernel
end CurrentAFT.RaisingPatternKernel.patternKernel
namespace CurrentAFT.RaisingPatternKernel.totalBody
end CurrentAFT.RaisingPatternKernel.totalBody
namespace CurrentAFT.RaisingPatternKernel.totalPrimary
end CurrentAFT.RaisingPatternKernel.totalPrimary
namespace CurrentAFT.SelectedRootComponent
end CurrentAFT.SelectedRootComponent
section
namespace CurrentAFT.PairedRootInput
open AFT ActualBlockFock TaggedSelection PairedRootPlacement RaisingPatternBudget
  GradedControlAlgebra ControlNorm ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PairedRootInput.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootInput.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootInput.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h201 {security : ℕ} (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security) :
    Finset.univ.map (_root_.CurrentAFT.PairedRootInput.labels tagged layout) = tagged.map layout.toEmbedding := by
  simp only [_root_.CurrentAFT.PairedRootInput.labels, ← Finset.map_map, Finset.map_univ_equiv]
  congr 1
  ext index
  simp
open _root_.P2M8f8f5b7e renaming h201 → _p2mH201
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h199 {Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    {security : ℕ} (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (test : (_root_.CurrentAFT.CycleRootExpansion.Vertex security → _root_.CurrentAFT.CycleRootExpansion.Root security) → Value) :
    _root_.CurrentAFT.CycleRootExpansion.actualComponent security (tagged.map layout.toEmbedding) test =
      ∑ word, ((_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security =>
          _root_.CurrentAFT.CycleRootExpansion.rootReference security)).weight word *
        _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security tagged.card (_root_.CurrentAFT.PairedRootInput.labels tagged layout)
          (word ∘ _root_.CurrentAFT.PairedRootInput.labels tagged layout)) • test word := by
  rw [← _p2mH201 tagged layout]
  have h := _p2mH378 security tagged.card (_root_.CurrentAFT.PairedRootInput.labels tagged layout) test
  convert h using 1
  congr 3
  exact Subsingleton.elim _ _
open _root_.P2M8f8f5b7e renaming h199 → _p2mH199
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h200 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (index : Fin tagged.card) :
    _root_.CurrentAFT.PairedRootInput.labels tagged layout index =
      layout (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged index)) := by
  simp only [_root_.CurrentAFT.PairedRootInput.labels, _root_.CurrentAFT.PairedRootInput.sourceEmbedding, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, _root_.CurrentAFT.PairedRootPlacement.tag_image]
  rfl
open _root_.P2M8f8f5b7e renaming h200 → _p2mH200
end
open _root_.P2M8f8f5b7e renaming h199 → _p2mH199
open _root_.P2M8f8f5b7e renaming h200 → _p2mH200
open _root_.P2M8f8f5b7e renaming h201 → _p2mH201
end CurrentAFT.PairedRootInput
open _root_.P2M8f8f5b7e renaming h199 → _p2mH199
open _root_.P2M8f8f5b7e renaming h200 → _p2mH200
open _root_.P2M8f8f5b7e renaming h201 → _p2mH201
end
open _root_.P2M8f8f5b7e renaming h199 → _p2mH199
open _root_.P2M8f8f5b7e renaming h200 → _p2mH200
open _root_.P2M8f8f5b7e renaming h201 → _p2mH201
namespace CurrentAFT.PairedRootInput
end CurrentAFT.PairedRootInput
namespace CurrentAFT.PairedRootInput.controlKernel
end CurrentAFT.PairedRootInput.controlKernel
namespace CurrentAFT.PairedRootInput.controlReference
end CurrentAFT.PairedRootInput.controlReference
namespace CurrentAFT.PairedRootInput.controlReference.match_1
end CurrentAFT.PairedRootInput.controlReference.match_1
namespace CurrentAFT.PairedRootInput.jointInput
end CurrentAFT.PairedRootInput.jointInput
namespace CurrentAFT.PairedRootInput.labels
end CurrentAFT.PairedRootInput.labels
namespace CurrentAFT.PairedRootInput.sourceEmbedding
end CurrentAFT.PairedRootInput.sourceEmbedding
section
namespace CurrentAFT.PairedRootCentering
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  ControlCoordinates RaisingPatternBudget
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PairedRootCentering.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootCentering.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootCentering.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h197 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (index : Fin tagged.card) :
    _root_.AFT.Hoeffding.CenteredAt (fun _ => _root_.CurrentAFT.CycleRootExpansion.rootReference security)
      (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged index) (_root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout) := by
  intro roots
  change (∑ root, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root *
    _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security tagged.card (_root_.CurrentAFT.PairedRootInput.labels tagged layout)
      (Function.update roots (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged index) root ∘ _root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged)) = 0
  simp_rw [Function.update_comp_eq_of_injective roots (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged).injective]
  have h := _p2mH379 security tagged.card (_root_.CurrentAFT.PairedRootInput.labels tagged layout) index
  convert h (roots ∘ _root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged) using 1
open _root_.P2M8f8f5b7e renaming h197 → _p2mH197
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h198 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (slot : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged)) (hslot : slot ∉ Set.range (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged))
    (roots : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) → _root_.CurrentAFT.CycleRootExpansion.Root security)
    (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout (Function.update roots slot root) = _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout roots := by
  unfold _root_.CurrentAFT.PairedRootCentering.rootDensity
  rw [Function.update_comp_eq_of_forall_ne roots root]
  intro index hequal
  exact hslot ⟨index, hequal⟩
open _root_.P2M8f8f5b7e renaming h198 → _p2mH198
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h194 (security : ℕ) {r s : ℕ}
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (role : _root_.CurrentAFT.RaisingPatternBudget.Role r s) (word : (other : _root_.CurrentAFT.RaisingPatternBudget.Role r s) → _root_.CurrentAFT.RaisingPatternBudget.RoleInput security r s other) :
    (_root_.CurrentAFT.RaisingPatternBudget.roleReference security r s role).expectation
      (fun control => _root_.CurrentAFT.RaisingPatternKernel.inputJoint security kernel (Function.update word role control)) = 0 := by
  cases role with
  | inl index =>
    have hword (control : _root_.CurrentAFT.ActualControls.Palette security) :
        _root_.CurrentAFT.RaisingPatternKernel.inputJoint security kernel (Function.update word (.inl index) control) =
          kernel.val (Function.update (fun i => word (.inl i)) index control) (fun i => word (.inr i)) := by
      unfold _root_.CurrentAFT.RaisingPatternKernel.inputJoint
      apply congrArg₂ kernel.val
      · funext other
        by_cases hequal : other = index
        · subst other
          simp
        · simp [hequal]
      · funext other
        simp
    simp_rw [hword]
    exact kernel.property.1 index _ _
  | inr index =>
    have hword (control : _root_.CurrentAFT.ActualControls.SafePalette security) :
        _root_.CurrentAFT.RaisingPatternKernel.inputJoint security kernel (Function.update word (.inr index) control) =
          kernel.val (fun i => word (.inl i)) (Function.update (fun i => word (.inr i)) index control) := by
      unfold _root_.CurrentAFT.RaisingPatternKernel.inputJoint
      apply congrArg₂ kernel.val
      · funext other
        simp
      · funext other
        by_cases hequal : other = index
        · subst other
          simp
        · simp [hequal]
    simp_rw [hword]
    exact kernel.property.2.1 index _ _
open _root_.P2M8f8f5b7e renaming h194 → _p2mH194
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h196 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (roots : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) → _root_.CurrentAFT.CycleRootExpansion.Root security)
    (controls : (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged) → _root_.CurrentAFT.PairedRootInput.ControlInput selection tagged group) :
    _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel
      (_root_.CurrentAFT.GroupedSourceNorm.wordEquiv (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged) (roots, controls)) =
      _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout roots * _root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel controls := rfl
open _root_.P2M8f8f5b7e renaming h196 → _p2mH196
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h193 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (controls : (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged) → _root_.CurrentAFT.PairedRootInput.ControlInput selection tagged group)
    (role : _root_.CurrentAFT.RaisingPatternBudget.Role r s) :
    (_root_.CurrentAFT.RaisingPatternBudget.roleReference security r s role).expectation (fun control =>
      _root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel (Function.update controls (.inl role) control)) = 0 := by
  have hequal (control : _root_.CurrentAFT.RaisingPatternBudget.RoleInput security r s role) :
      (fun index => Function.update controls (.inl role) control (.inl index)) =
        Function.update (fun index => controls (.inl index)) role control := by
    funext index
    by_cases hequal : index = role
    · subst index
      simp
    · simp [hequal]
  unfold _root_.CurrentAFT.PairedRootInput.controlKernel
  simp_rw [hequal]
  exact _p2mH194 security kernel role _
open _root_.P2M8f8f5b7e renaming h193 → _p2mH193
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h195 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (roots : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) → _root_.CurrentAFT.CycleRootExpansion.Root security)
    (controls : (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged) → _root_.CurrentAFT.PairedRootInput.ControlInput selection tagged group)
    (role : _root_.CurrentAFT.RaisingPatternBudget.Role r s) :
    (_root_.CurrentAFT.RaisingPatternBudget.roleReference security r s role).expectation (fun control =>
      _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel
        (_root_.CurrentAFT.GroupedSourceNorm.wordEquiv (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged)
          (roots, Function.update controls (.inl role) control))) = 0 := by
  simp_rw [_p2mH196]
  have h := _p2mH193 selection tagged kernel controls role
  unfold _root_.AFT.FiniteDist.expectation at *
  calc
    _ = _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout roots *
        ∑ control, (_root_.CurrentAFT.RaisingPatternBudget.roleReference security r s role).weight control *
          _root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel (Function.update controls (.inl role) control) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro control _
      ring
    _ = 0 := by rw [h, mul_zero]
open _root_.P2M8f8f5b7e renaming h195 → _p2mH195
end
open _root_.P2M8f8f5b7e renaming h193 → _p2mH193
open _root_.P2M8f8f5b7e renaming h194 → _p2mH194
open _root_.P2M8f8f5b7e renaming h195 → _p2mH195
open _root_.P2M8f8f5b7e renaming h196 → _p2mH196
open _root_.P2M8f8f5b7e renaming h197 → _p2mH197
open _root_.P2M8f8f5b7e renaming h198 → _p2mH198
end CurrentAFT.PairedRootCentering
open _root_.P2M8f8f5b7e renaming h193 → _p2mH193
open _root_.P2M8f8f5b7e renaming h194 → _p2mH194
open _root_.P2M8f8f5b7e renaming h195 → _p2mH195
open _root_.P2M8f8f5b7e renaming h196 → _p2mH196
open _root_.P2M8f8f5b7e renaming h197 → _p2mH197
open _root_.P2M8f8f5b7e renaming h198 → _p2mH198
end
open _root_.P2M8f8f5b7e renaming h193 → _p2mH193
open _root_.P2M8f8f5b7e renaming h194 → _p2mH194
open _root_.P2M8f8f5b7e renaming h195 → _p2mH195
open _root_.P2M8f8f5b7e renaming h196 → _p2mH196
open _root_.P2M8f8f5b7e renaming h197 → _p2mH197
open _root_.P2M8f8f5b7e renaming h198 → _p2mH198
section
namespace CurrentAFT.GroupedRootUpdates
open AFT GroupedSourceNorm
open scoped Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.GroupedRootUpdates.classicalSigmaDecidableEq
variable {Group Root : Type*} [DecidableEq Group] (Slots Control : Group → Type*)
  [∀ group, DecidableEq (Slots group)]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h131 (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (slot : Slots group) (value : Root) :
    _root_.CurrentAFT.GroupedRootUpdates.roots Slots Control (_root_.CurrentAFT.GroupedRootUpdates.updateRoot Slots Control word group slot value) =
      Function.update (_root_.CurrentAFT.GroupedRootUpdates.roots Slots Control word) ⟨group, slot⟩ value := by
  funext point
  rcases point with ⟨other, point⟩
  by_cases hequal : other = group
  · subst other
    by_cases hslot : point = slot
    · subst point
      simp [_root_.CurrentAFT.GroupedRootUpdates.roots, _root_.CurrentAFT.GroupedRootUpdates.updateRoot]
    · simp [_root_.CurrentAFT.GroupedRootUpdates.roots, _root_.CurrentAFT.GroupedRootUpdates.updateRoot, hslot]
  · simp [_root_.CurrentAFT.GroupedRootUpdates.roots, _root_.CurrentAFT.GroupedRootUpdates.updateRoot, hequal]
open _root_.P2M8f8f5b7e renaming h131 → _p2mH131
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h130 (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (slot : Slots group) (value : Root) :
    _root_.CurrentAFT.GroupedRootUpdates.controls Slots Control (_root_.CurrentAFT.GroupedRootUpdates.updateRoot Slots Control word group slot value) = _root_.CurrentAFT.GroupedRootUpdates.controls Slots Control word := by
  funext other
  by_cases hequal : other = group
  · subst other
    simp [_root_.CurrentAFT.GroupedRootUpdates.controls, _root_.CurrentAFT.GroupedRootUpdates.updateRoot]
  · simp [_root_.CurrentAFT.GroupedRootUpdates.controls, _root_.CurrentAFT.GroupedRootUpdates.updateRoot, hequal]
open _root_.P2M8f8f5b7e renaming h130 → _p2mH130
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h132 (word : (group : Group) → (Slots group → Root) × Control group)
    (group : Group) (sample : (Slots group → Root) × Control group) (slot : Slots group) (value : Root) :
    _root_.CurrentAFT.GroupedRootUpdates.updateRoot Slots Control (Function.update word group sample) group slot value =
      Function.update word group (Function.update sample.1 slot value, sample.2) := by
  simp only [_root_.CurrentAFT.GroupedRootUpdates.updateRoot, Function.update_self, Function.update_idem]
open _root_.P2M8f8f5b7e renaming h132 → _p2mH132
end
open _root_.P2M8f8f5b7e renaming h130 → _p2mH130
open _root_.P2M8f8f5b7e renaming h131 → _p2mH131
open _root_.P2M8f8f5b7e renaming h132 → _p2mH132
end CurrentAFT.GroupedRootUpdates
open _root_.P2M8f8f5b7e renaming h130 → _p2mH130
open _root_.P2M8f8f5b7e renaming h131 → _p2mH131
open _root_.P2M8f8f5b7e renaming h132 → _p2mH132
end
open _root_.P2M8f8f5b7e renaming h130 → _p2mH130
open _root_.P2M8f8f5b7e renaming h131 → _p2mH131
open _root_.P2M8f8f5b7e renaming h132 → _p2mH132
namespace AFT.DependentTensorChannel
end AFT.DependentTensorChannel
namespace AFT.DependentTensorChannel.apply
end AFT.DependentTensorChannel.apply
namespace AFT.DependentTensorChannel.applyFin
end AFT.DependentTensorChannel.applyFin
namespace AFT.DependentTensorChannel.applyFin.match_1
end AFT.DependentTensorChannel.applyFin.match_1
section
namespace CurrentAFT.DependentTensorComposition
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input Middle Output : Index → Type*}
  [∀ index, Fintype (Input index)] [∀ index, Fintype (Middle index)] [∀ index, Fintype (Output index)]
set_option maxRecDepth 8192
omit [∀ index, Fintype (Output index)] in
theorem _root_.P2M8f8f5b7e.h101
    (first : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Middle index → ℝ))
    (second : ∀ index, (Middle index → ℝ) →ₗ[ℝ] (Output index → ℝ))
    (input : ((index : Index) → Input index) → ℝ) :
    _root_.AFT.DependentTensorChannel.apply (fun index => (second index).comp (first index)) input =
      _root_.AFT.DependentTensorChannel.apply second (_root_.AFT.DependentTensorChannel.apply first input) := by
  funext output
  unfold _root_.AFT.DependentTensorChannel.apply
  simp only [LinearMap.comp_apply]
  have hcolumn (index : Index) (source : Input index) :
      second index (first index (Pi.single source 1)) (output index) =
        ∑ middle, first index (Pi.single source 1) middle *
          second index (Pi.single middle 1) (output index) :=
    _root_.AFT.TensorChannel.channel_sum_single (second index) _ _
  simp_rw [hcolumn]
  simp_rw [Fintype.prod_sum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro middle _
  apply Finset.sum_congr rfl
  intro source _
  rw [Finset.prod_mul_distrib]
  ring
open _root_.P2M8f8f5b7e renaming h101 → _p2mH101
end
open _root_.P2M8f8f5b7e renaming h101 → _p2mH101
end CurrentAFT.DependentTensorComposition
open _root_.P2M8f8f5b7e renaming h101 → _p2mH101
end
open _root_.P2M8f8f5b7e renaming h101 → _p2mH101
namespace CurrentAFT.DependentTensorComposition
end CurrentAFT.DependentTensorComposition
section
namespace CurrentAFT.DependentTensorFixedInput
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h102 (count : ℕ) {Input : Fin count → Type*}
    (projector : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Input index → ℝ))
    (kernel : ((index : Fin count) → Input index) → ℝ)
    (hfixed : ∀ index word, projector index
      (fun value => kernel (Function.update word index value)) =
        fun value => kernel (Function.update word index value)) :
    _root_.AFT.DependentTensorChannel.applyFin count projector kernel = kernel := by
  induction count with
  | zero =>
      funext word
      change kernel (fun index => Fin.elim0 index) = kernel word
      congr 1
      funext index
      exact Fin.elim0 index
  | succ count ih =>
      have htail (first : Input 0) :
          ∀ index word, projector index.succ
            (fun value => kernel (Fin.cons first (Function.update word index value))) =
              fun value => kernel (Fin.cons first (Function.update word index value)) := by
        intro index word
        simpa only [Fin.cons_update] using hfixed index.succ (Fin.cons first word)
      have ht (first : Input 0) :
          _root_.AFT.DependentTensorChannel.applyFin count (fun index => projector index.succ)
            (fun rest => kernel (Fin.cons first rest)) =
              fun rest => kernel (Fin.cons first rest) :=
        ih (fun index => projector index.succ) (fun rest => kernel (Fin.cons first rest))
          (htail first)
      funext output
      change projector 0 (fun first =>
        _root_.AFT.DependentTensorChannel.applyFin count (fun index => projector index.succ)
          (fun rest => kernel (Fin.cons first rest)) (fun index => output index.succ))
            (output 0) = kernel output
      simp_rw [ht]
      have hcons : Fin.cons (output 0) (fun index => output index.succ) = output := by
        funext index
        refine Fin.cases ?_ (fun index => ?_) index <;> rfl
      have hh := congrFun (hfixed 0
        (Fin.cons (output 0) (fun index => output index.succ))) (output 0)
      simp only [Fin.update_cons_zero] at hh
      rw [hcons] at hh
      exact hh
open _root_.P2M8f8f5b7e renaming h102 → _p2mH102
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input : Index → Type*} [∀ index, Fintype (Input index)]
set_option maxRecDepth 8192
omit [Fintype Index] [∀ index, Fintype (Input index)] in
private theorem _root_.P2M8f8f5b7e.h399 {Index' : Type*} [DecidableEq Index']
    (equiv : Index' ≃ Index) (word : ∀ index, Input (equiv index))
    (index : Index') (value : Input (equiv index)) :
    Equiv.piCongrLeft Input equiv (Function.update word index value) =
      Function.update (Equiv.piCongrLeft Input equiv word) (equiv index) value := by
  simpa only [Equiv.piCongrLeft, Equiv.symm_symm] using
    Function.piCongrLeft'_symm_update Input equiv.symm word index value
open _root_.P2M8f8f5b7e renaming h399 → _p2mH399
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h103
    (projector : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Input index → ℝ))
    (kernel : ((index : Index) → Input index) → ℝ)
    (hfixed : ∀ index word, projector index
      (fun value => kernel (Function.update word index value)) =
        fun value => kernel (Function.update word index value)) :
    _root_.AFT.DependentTensorChannel.apply projector kernel = kernel := by
  let equiv : Fin (Fintype.card Index) ≃ Index := (Fintype.equivFin Index).symm
  have hfixed' (index : Fin (Fintype.card Index)) (word : ∀ index, Input (equiv index)) :
      projector (equiv index)
        (fun value => kernel (Equiv.piCongrLeft Input equiv (Function.update word index value))) =
          fun value => kernel (Equiv.piCongrLeft Input equiv (Function.update word index value)) := by
    simpa only [_p2mH399] using
      hfixed (equiv index) (Equiv.piCongrLeft Input equiv word)
  have hh := _p2mH102 (Fintype.card Index) (fun index => projector (equiv index))
    (fun word => kernel (Equiv.piCongrLeft Input equiv word)) hfixed'
  funext output
  have heq := congrFun hh ((Equiv.piCongrLeft Input equiv).symm output)
  rw [_root_.AFT.DependentTensorChannel.applyFin_formula] at heq
  have hreindex :
      (∑ point : (index : Fin (Fintype.card Index)) → Input (equiv index),
        kernel (Equiv.piCongrLeft Input equiv point) *
          ∏ index, projector (equiv index) (Pi.single (point index) 1)
            (((Equiv.piCongrLeft Input equiv).symm output) index)) =
        _root_.AFT.DependentTensorChannel.apply projector kernel output := by
    unfold _root_.AFT.DependentTensorChannel.apply
    rw [← (Equiv.piCongrLeft Input equiv).sum_comp]
    apply Finset.sum_congr rfl
    intro point _
    congr 1
    rw [← equiv.prod_comp]
    simp only [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_symm_apply]
  rw [hreindex] at heq
  simpa only [Equiv.apply_symm_apply] using heq
open _root_.P2M8f8f5b7e renaming h103 → _p2mH103
end
open _root_.P2M8f8f5b7e renaming h102 → _p2mH102
open _root_.P2M8f8f5b7e renaming h103 → _p2mH103
open _root_.P2M8f8f5b7e renaming h399 → _p2mH399
end CurrentAFT.DependentTensorFixedInput
open _root_.P2M8f8f5b7e renaming h102 → _p2mH102
open _root_.P2M8f8f5b7e renaming h103 → _p2mH103
open _root_.P2M8f8f5b7e renaming h399 → _p2mH399
end
open _root_.P2M8f8f5b7e renaming h102 → _p2mH102
open _root_.P2M8f8f5b7e renaming h103 → _p2mH103
namespace CurrentAFT.DependentTensorFixedInput
end CurrentAFT.DependentTensorFixedInput
namespace CurrentAFT.GroupedRootUpdates
end CurrentAFT.GroupedRootUpdates
namespace CurrentAFT.GroupedRootUpdates.controls
end CurrentAFT.GroupedRootUpdates.controls
namespace CurrentAFT.GroupedRootUpdates.roots
end CurrentAFT.GroupedRootUpdates.roots
namespace CurrentAFT.GroupedRootUpdates.updateRoot
end CurrentAFT.GroupedRootUpdates.updateRoot
namespace CurrentAFT.PairedRootCentering
end CurrentAFT.PairedRootCentering
section
namespace CurrentAFT.PairedRootProjection
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  PairedRootCentering ControlCoordinates GroupedRootUpdates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.classicalSigmaDecidableEq
attribute [local instance] _root_.CurrentAFT.PairedRootProjection.slotDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h205 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (slot : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged)) :
    slot ∈ Set.range (_root_.CurrentAFT.PairedRootInput.sourceEmbedding selection tagged) ↔ _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged slot ∈ tagged := by
  constructor
  · rintro ⟨index, rfl⟩
    change _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged (_root_.CurrentAFT.PairedRootPlacement.tagEmbedding selection tagged (tagged.equivFin.symm index)) ∈ tagged
    rw [_root_.CurrentAFT.PairedRootPlacement.tag_image]
    exact (tagged.equivFin.symm index).property
  · intro hslot
    refine ⟨tagged.equivFin ⟨_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged slot, hslot⟩, ?_⟩
    apply (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged).injective
    simp only [_root_.CurrentAFT.PairedRootInput.sourceEmbedding, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      Equiv.symm_apply_apply, _root_.CurrentAFT.PairedRootPlacement.tag_image]
open _root_.P2M8f8f5b7e renaming h205 → _p2mH205
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h202 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) :
    _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel word =
      _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout (_root_.CurrentAFT.GroupedRootUpdates.roots (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged) word) *
        _root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel (_root_.CurrentAFT.GroupedRootUpdates.controls (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged) word) := rfl
open _root_.P2M8f8f5b7e renaming h202 → _p2mH202
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h206 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged)
    (slot : _root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged group)
    (htag : _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged) :
    (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation (fun value =>
      _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel
        (_root_.CurrentAFT.GroupedRootUpdates.updateRoot (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged) word group slot value)) = 0 := by
  obtain ⟨index, hindex⟩ := (_p2mH205 selection tagged ⟨group, slot⟩).mpr htag
  simp_rw [_p2mH202, _p2mH131, _p2mH130]
  rw [← hindex]
  unfold _root_.AFT.FiniteDist.expectation
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul, _p2mH197 selection tagged layout index, zero_mul]
open _root_.P2M8f8f5b7e renaming h206 → _p2mH206
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h207 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged)
    (slot : _root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged group)
    (htag : _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨group, slot⟩ ∉ tagged) (value : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel
      (_root_.CurrentAFT.GroupedRootUpdates.updateRoot (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged) word group slot value) =
        _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel word := by
  rw [_p2mH202, _p2mH131, _p2mH130, _p2mH202]
  rw [_p2mH198 selection tagged layout ⟨group, slot⟩
    (fun h => htag ((_p2mH205 selection tagged ⟨group, slot⟩).mp h))]
open _root_.P2M8f8f5b7e renaming h207 → _p2mH207
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h204 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged) :
    _root_.CurrentAFT.PairedRootProjection.projector selection tagged group (fun sample => _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel (Function.update word group sample)) =
      fun sample => _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel (Function.update word group sample) := by
  apply _p2mH269
  intro item hitem
  obtain ⟨slot, _, rfl⟩ := List.mem_map.mp hitem
  by_cases htag : _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨group, slot⟩ ∈ tagged
  · simp only [htag, decide_true, _root_.CurrentAFT.RootCoordinateProjection.coordinate, if_true]
    apply _p2mH268
    intro sample
    simp_rw [← _p2mH132]
    exact _p2mH206 selection tagged layout kernel (Function.update word group sample) group slot htag
  · simp only [htag, decide_false, _root_.CurrentAFT.RootCoordinateProjection.coordinate, Bool.false_eq_true, if_false]
    apply _p2mH267
    intro sample value
    rw [← _p2mH132]
    exact _p2mH207 selection tagged layout kernel (Function.update word group sample) group slot htag value
open _root_.P2M8f8f5b7e renaming h204 → _p2mH204
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h203 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.AFT.DependentTensorChannel.apply (_root_.CurrentAFT.PairedRootProjection.projector selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) =
      _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel :=
  _p2mH103 _ _ (fun group word =>
    _p2mH204 selection tagged layout kernel word group)
open _root_.P2M8f8f5b7e renaming h203 → _p2mH203
end
open _root_.P2M8f8f5b7e renaming h202 → _p2mH202
open _root_.P2M8f8f5b7e renaming h203 → _p2mH203
open _root_.P2M8f8f5b7e renaming h204 → _p2mH204
open _root_.P2M8f8f5b7e renaming h205 → _p2mH205
open _root_.P2M8f8f5b7e renaming h206 → _p2mH206
open _root_.P2M8f8f5b7e renaming h207 → _p2mH207
end CurrentAFT.PairedRootProjection
open _root_.P2M8f8f5b7e renaming h202 → _p2mH202
open _root_.P2M8f8f5b7e renaming h203 → _p2mH203
open _root_.P2M8f8f5b7e renaming h204 → _p2mH204
open _root_.P2M8f8f5b7e renaming h205 → _p2mH205
open _root_.P2M8f8f5b7e renaming h206 → _p2mH206
open _root_.P2M8f8f5b7e renaming h207 → _p2mH207
end
open _root_.P2M8f8f5b7e renaming h202 → _p2mH202
open _root_.P2M8f8f5b7e renaming h203 → _p2mH203
open _root_.P2M8f8f5b7e renaming h204 → _p2mH204
open _root_.P2M8f8f5b7e renaming h205 → _p2mH205
open _root_.P2M8f8f5b7e renaming h206 → _p2mH206
open _root_.P2M8f8f5b7e renaming h207 → _p2mH207
namespace CurrentAFT.ActualRootGroupedChannel
end CurrentAFT.ActualRootGroupedChannel
namespace CurrentAFT.ActualRootGroupedChannel.channel
end CurrentAFT.ActualRootGroupedChannel.channel
namespace CurrentAFT.GroupedFamilyComposition
end CurrentAFT.GroupedFamilyComposition
section
namespace CurrentAFT.ActualRootResponse
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  GradedControlAlgebra ControlCoordinates LocalCoefficientFamily GradedInverse ControlNorm
open Filter
open scoped BigOperators Classical Topology
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualRootResponse.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootResponse.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootResponse.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h37 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout kernel =
      _root_.CurrentAFT.GroupedFamilyTensor.response (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) order
        (_root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) := rfl
open _root_.P2M8f8f5b7e renaming h37 → _p2mH37
end
open _root_.P2M8f8f5b7e renaming h37 → _p2mH37
end CurrentAFT.ActualRootResponse
open _root_.P2M8f8f5b7e renaming h37 → _p2mH37
end
open _root_.P2M8f8f5b7e renaming h37 → _p2mH37
namespace CurrentAFT.RootOrdinaryGroupedChannel
end CurrentAFT.RootOrdinaryGroupedChannel
section
namespace CurrentAFT.RootLocalDenominators
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst IndependentPairedReference
  PositiveFirstCoefficient ActualBlockFock RootTaggedSelected RootReferenceExpectation
  RootBackgroundPolynomial RootIndependentBackground BodyRootAverages BackgroundPolynomialEvaluation
  BackgroundEndpointLaw CycleRootExpansion ControlCoordinates GradedControlAlgebra GradedControlNorm
  LocalCoefficientFamily LocalRaisingBounds NormalizedLocalPolynomial
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootLocalDenominators.classicalFinDecidableEq
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h321 (security : ℕ) (firstComp secondComp firstAttach secondAttach : ℤ)
    (hcomp : (firstComp : _root_.CurrentAFT.CycleRootExpansion.Root security) = (secondComp : _root_.CurrentAFT.CycleRootExpansion.Root security))
    (hattach : (firstAttach : _root_.CurrentAFT.CycleRootExpansion.Root security) = (secondAttach : _root_.CurrentAFT.CycleRootExpansion.Root security))
    (scalar : _root_.CurrentAFT.FirstHistogram.Scalar security) :
    _root_.CurrentAFT.PositiveFirstCoefficient.positiveFourLaw security firstComp firstAttach scalar = _root_.CurrentAFT.PositiveFirstCoefficient.positiveFourLaw security secondComp secondAttach scalar := by
  have hc : _root_.CurrentAFT.PairedReferenceEnergy.compensatorAt security firstComp = _root_.CurrentAFT.PairedReferenceEnergy.compensatorAt security secondComp := by
    unfold _root_.CurrentAFT.PairedReferenceEnergy.compensatorAt
    rw [_root_.CurrentAFT.RootBackgroundPolynomial.shiftEquiv_eq_of_cast security firstComp secondComp hcomp]
  have ha : _root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security firstAttach scalar = _root_.CurrentAFT.LocalReferenceEnergy.attachmentAt security secondAttach scalar := by
    unfold _root_.CurrentAFT.LocalReferenceEnergy.attachmentAt
    rw [_root_.CurrentAFT.RootBackgroundPolynomial.shiftEquiv_eq_of_cast security (firstAttach + scalar.val) (secondAttach + scalar.val)
      (by simp only [Int.cast_add, hattach])]
  simp only [_root_.CurrentAFT.PositiveFirstCoefficient.positiveFourLaw, hc, _root_.CurrentAFT.PositiveFirstCoefficient.positiveTripleLaw, ha]
open _root_.P2M8f8f5b7e renaming h321 → _p2mH321
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h316 (security : ℕ) (word : Fin 4 → _root_.CurrentAFT.RootLocalDenominators.Palette security) :
    (_root_.CurrentAFT.RootTaggedSelected.sourceLaw security).expectation (fun sample =>
      (_root_.CurrentAFT.PositiveFirstCoefficient.positiveFourLaw security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2).weight word) =
      (_root_.CurrentAFT.NormalizedLocalPolynomial.independentPositiveLaw security).weight word := by
  rw [_root_.CurrentAFT.IndependentReferenceEnergy.independentPositive_mixture]
  unfold _root_.CurrentAFT.RootTaggedSelected.sourceLaw _root_.CurrentAFT.RootTaggedSelected.rootsLaw _root_.CurrentAFT.IndependentReferenceEnergy.rootLaw
  rw [_root_.AFT.FiniteDist.expectation_prod, _root_.AFT.FiniteDist.expectation_comm, _root_.AFT.FiniteDist.expectation_prod]
  apply congrArg (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).expectation
  funext scalar
  rw [_root_.AFT.FiniteDist.expectation_prod]
  calc
    _ = (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).expectation (fun comp =>
        (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation (fun attach =>
          (_root_.CurrentAFT.PositiveFirstCoefficient.positiveFourLaw security (_root_.CurrentAFT.DiffuseProfiles.actualBlur security comp) (attach.val : ℤ) scalar).weight word)) := by
      apply _root_.CurrentAFT.RootReferenceExpectation.rootReference_seed_expectation security (fun comp : ℤ =>
        (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation (fun attach =>
          (_root_.CurrentAFT.PositiveFirstCoefficient.positiveFourLaw security comp (attach.val : ℤ) scalar).weight word))
      intro first second hequal
      apply congrArg (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation
      funext attach
      rw [_p2mH321 security first second (attach.val : ℤ) (attach.val : ℤ) hequal rfl scalar]
    _ = _ := by
      rw [_root_.AFT.FiniteDist.expectation_prod]
      apply congrArg (_root_.CurrentAFT.DiffuseProfiles.actualSeedLaw security).expectation
      funext comp
      apply _root_.CurrentAFT.RootReferenceExpectation.rootReference_seed_expectation security (fun attach : ℤ =>
        (_root_.CurrentAFT.PositiveFirstCoefficient.positiveFourLaw security (_root_.CurrentAFT.DiffuseProfiles.actualBlur security comp) attach scalar).weight word)
      intro first second hequal
      rw [_p2mH321 security (_root_.CurrentAFT.DiffuseProfiles.actualBlur security comp) (_root_.CurrentAFT.DiffuseProfiles.actualBlur security comp)
        first second rfl hequal scalar]
open _root_.P2M8f8f5b7e renaming h316 → _p2mH316
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h314 {Color : Type*} [Fintype Color] (reference : Color → ℝ)
    (first : _root_.AFT.FiniteDist Color) (tail : _root_.AFT.FiniteDist (Fin 3 → Color)) :
    _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating ((first.prod tail).map (fun draw => Fin.cons draw.1 draw.2))
      (fun word : Fin 4 → Color => ∏ index, _root_.AFT.RepresentedPolynomial.centeredFactor reference (word index)) =
      _root_.AFT.RepresentedPolynomial.singleGenerating reference first.weight * _root_.CurrentAFT.BackgroundPolynomialEvaluation.finiteGenerating tail (fun word => ∏ index, _root_.AFT.RepresentedPolynomial.centeredFactor reference (word index)) := by
  rw [_p2mH42]
  simp only [Function.comp_def, Fin.prod_univ_succ]
  exact _p2mH54 first tail (_root_.AFT.RepresentedPolynomial.centeredFactor reference)
    (fun word => ∏ index : Fin 3, _root_.AFT.RepresentedPolynomial.centeredFactor reference (word index))
open _root_.P2M8f8f5b7e renaming h314 → _p2mH314
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h320 (security : ℕ) (comp attach : ℤ) (scalar : _root_.CurrentAFT.FirstHistogram.Scalar security) :
    _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.PositiveFirstCoefficient.positiveFourLaw security comp attach scalar) =
      _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.FringeCertificate.uniformProfile security) (_root_.CurrentAFT.PairedReferenceEnergy.compensatorAt security comp).weight *
        _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.PositiveFirstCoefficient.positiveTripleLaw security attach scalar) :=
  _p2mH314 (_root_.CurrentAFT.FringeCertificate.uniformProfile security) (_root_.CurrentAFT.PairedReferenceEnergy.compensatorAt security comp)
    (_root_.CurrentAFT.PositiveFirstCoefficient.positiveTripleLaw security attach scalar)
open _root_.P2M8f8f5b7e renaming h320 → _p2mH320
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h313 (security : ℕ) :
    (_root_.CurrentAFT.CycleRootExpansion.rootReference security).mix (fun root => _root_.CurrentAFT.PairedReferenceEnergy.compensatorAt security (root.val : ℤ)) =
      _root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security := by
  unfold _root_.CurrentAFT.PairedReferenceEnergy.compensatorAt
  rw [_p2mH276, _p2mH81]
open _root_.P2M8f8f5b7e renaming h313 → _p2mH313
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h315 (security : ℕ) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.NormalizedLocalPolynomial.independentPositiveLaw security).weight =
      _root_.CurrentAFT.RootLocalDenominators.primaryPolynomial security := by
  have hmass : (_root_.CurrentAFT.NormalizedLocalPolynomial.independentPositiveLaw security).weight =
      ∑ sample : _root_.CurrentAFT.RootTaggedSelected.Sample security, (_root_.CurrentAFT.RootTaggedSelected.sourceLaw security).weight sample •
        (_root_.CurrentAFT.PositiveFirstCoefficient.positiveFourLaw security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2).weight := by
    funext word
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, _root_.AFT.FiniteDist.expectation] using (_p2mH316 security word).symm
  rw [hmass, map_sum]
  simp only [map_smul, _root_.CurrentAFT.RootLocalDenominators.generating_eq_block, _p2mH320]
  have hleg := _p2mH274 security
  simp only [_root_.CurrentAFT.ActualBlockFock.primaryLawAt, _p2mH271] at hleg
  rw [show _root_.CurrentAFT.RootLocalDenominators.primaryPolynomial security =
    (∑ comp : _root_.CurrentAFT.CycleRootExpansion.Root security, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight comp •
      _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.FringeCertificate.uniformProfile security) (_root_.CurrentAFT.PairedReferenceEnergy.compensatorAt security (comp.val : ℤ)).weight) *
    (∑ attach : _root_.CurrentAFT.CycleRootExpansion.Root security, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight attach •
      ∑ scalar, (_root_.CurrentAFT.DiffuseProfiles.scalarLaw security).weight scalar • _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.PositiveFirstCoefficient.positiveTripleLaw security (attach.val : ℤ) scalar)) from by
    rw [hleg, ← _p2mH277, _p2mH313]
    rfl]
  simp only [_root_.CurrentAFT.RootTaggedSelected.sourceLaw, _root_.CurrentAFT.RootTaggedSelected.rootsLaw, Fintype.sum_prod_type, _root_.AFT.FiniteDist.prod_weight]
  symm
  rw [Finset.sum_mul]
  simp only [Finset.mul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro comp _
  apply Finset.sum_congr rfl
  intro attach _
  apply Finset.sum_congr rfl
  intro scalar _
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
  congr 1
  ring
open _root_.P2M8f8f5b7e renaming h315 → _p2mH315
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h318 (security : ℕ) : _root_.CurrentAFT.RootLocalDenominators.ordinaryPolynomial security =
    1 + _root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.OrdinaryRaising.deviation security) := by
  rw [_root_.CurrentAFT.RootLocalDenominators.ordinaryPolynomial, _p2mH15 _ _ (_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security).sum_one]
  rfl
open _root_.P2M8f8f5b7e renaming h318 → _p2mH318
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h317 (security : ℕ) (queue : ℤ) :
    _root_.CurrentAFT.RootTaggedLocal.meanLaw security .free queue = _root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security := by
  unfold _root_.CurrentAFT.RootTaggedLocal.meanLaw _root_.CurrentAFT.RootTaggedLocal.shiftedLaw _root_.CurrentAFT.UniformBodyProfiles.preRootLaw
  rw [_p2mH276, _p2mH81]
open _root_.P2M8f8f5b7e renaming h317 → _p2mH317
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h319 (security : ℕ) (queue : ℤ) (index : Fin (_root_.CurrentAFT.ActualBlockFock.centerCount security)) :
    _root_.CurrentAFT.RootLocalDenominators.ordinaryPolynomial security = _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue (.inr (.inl index)) := by
  rw [_root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial, _p2mH317, _root_.CurrentAFT.RootLocalDenominators.uniformReference_eq]
  rfl
open _root_.P2M8f8f5b7e renaming h319 → _p2mH319
end
open _root_.P2M8f8f5b7e renaming h313 → _p2mH313
open _root_.P2M8f8f5b7e renaming h314 → _p2mH314
open _root_.P2M8f8f5b7e renaming h315 → _p2mH315
open _root_.P2M8f8f5b7e renaming h316 → _p2mH316
open _root_.P2M8f8f5b7e renaming h317 → _p2mH317
open _root_.P2M8f8f5b7e renaming h318 → _p2mH318
open _root_.P2M8f8f5b7e renaming h319 → _p2mH319
open _root_.P2M8f8f5b7e renaming h320 → _p2mH320
open _root_.P2M8f8f5b7e renaming h321 → _p2mH321
end CurrentAFT.RootLocalDenominators
open _root_.P2M8f8f5b7e renaming h313 → _p2mH313
open _root_.P2M8f8f5b7e renaming h314 → _p2mH314
open _root_.P2M8f8f5b7e renaming h315 → _p2mH315
open _root_.P2M8f8f5b7e renaming h316 → _p2mH316
open _root_.P2M8f8f5b7e renaming h317 → _p2mH317
open _root_.P2M8f8f5b7e renaming h318 → _p2mH318
open _root_.P2M8f8f5b7e renaming h319 → _p2mH319
open _root_.P2M8f8f5b7e renaming h320 → _p2mH320
open _root_.P2M8f8f5b7e renaming h321 → _p2mH321
end
open _root_.P2M8f8f5b7e renaming h313 → _p2mH313
open _root_.P2M8f8f5b7e renaming h314 → _p2mH314
open _root_.P2M8f8f5b7e renaming h315 → _p2mH315
open _root_.P2M8f8f5b7e renaming h316 → _p2mH316
open _root_.P2M8f8f5b7e renaming h317 → _p2mH317
open _root_.P2M8f8f5b7e renaming h318 → _p2mH318
open _root_.P2M8f8f5b7e renaming h319 → _p2mH319
open _root_.P2M8f8f5b7e renaming h320 → _p2mH320
open _root_.P2M8f8f5b7e renaming h321 → _p2mH321
namespace CurrentAFT.LocalRaisingBounds.positiveInverse
end CurrentAFT.LocalRaisingBounds.positiveInverse
namespace CurrentAFT.RootCoordinateProjection.coordinate
end CurrentAFT.RootCoordinateProjection.coordinate
namespace CurrentAFT.RootCoordinateProjection.sequence.match_1
end CurrentAFT.RootCoordinateProjection.sequence.match_1
namespace CurrentAFT.RootLocalDenominators
end CurrentAFT.RootLocalDenominators
namespace CurrentAFT.RootLocalDenominators.ordinaryPolynomial
end CurrentAFT.RootLocalDenominators.ordinaryPolynomial
namespace CurrentAFT.RootPrimaryGroupedChannel
end CurrentAFT.RootPrimaryGroupedChannel
namespace CurrentAFT.RootPrimaryGroupedChannel.cost
end CurrentAFT.RootPrimaryGroupedChannel.cost
namespace CurrentAFT.RootPrimaryGroupedChannel.minimumDegree
end CurrentAFT.RootPrimaryGroupedChannel.minimumDegree
namespace CurrentAFT.RootPrimaryGroupedChannel.pairEquiv
end CurrentAFT.RootPrimaryGroupedChannel.pairEquiv
namespace CurrentAFT.RootPrimaryGroupedChannel.pairLinear
end CurrentAFT.RootPrimaryGroupedChannel.pairLinear
namespace CurrentAFT.RootPrimaryGroupedChannel.projectedScore
end CurrentAFT.RootPrimaryGroupedChannel.projectedScore
namespace CurrentAFT.RootTaggedSelectedChannel
end CurrentAFT.RootTaggedSelectedChannel
namespace CurrentAFT.RootTaggedSelectedChannel.curryLinear
end CurrentAFT.RootTaggedSelectedChannel.curryLinear
namespace CurrentAFT.RootUnselectedBlockChannel.channel.match_1
end CurrentAFT.RootUnselectedBlockChannel.channel.match_1
namespace CurrentAFT.RootUnselectedBlockChannel.positivePolynomial
end CurrentAFT.RootUnselectedBlockChannel.positivePolynomial
section
namespace CurrentAFT.RootSelectedPhysicalColumns
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst PhysicalSynthesis
  RootTaggedSelected RootBackgroundPolynomial BackgroundPolynomialEvaluation
  CycleRootExpansion LocalCoefficientFamily RootLocalDenominators
  ControlCoordinates GradedControlAlgebra
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootSelectedPhysicalColumns.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootSelectedPhysicalColumns.safeDecidableEq
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h342 (security order : ℕ) (tagged : Fin 2 → Bool)
    (score : _root_.CurrentAFT.RootPrimaryGroupedChannel.Input security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootPrimaryGroupedChannel.channel security order tagged score) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootLocalDenominators.primaryPolynomial security) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootSelectedPhysicalColumns.primaryNumerator security (_root_.CurrentAFT.RootPrimaryGroupedChannel.centeredScore security tagged score)) := by
  rw [← _p2mH315]
  rw [_p2mH336, _root_.CurrentAFT.RootSelectedPhysicalColumns.primaryNumerator_eq]
open _root_.P2M8f8f5b7e renaming h342 → _p2mH342
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h343 {Source Output : Type*} [Fintype Source] [Fintype Output]
    (law : _root_.AFT.FiniteDist Source) (embedding : Source → Output) (reference : Output → ℝ) (score : Source → ℝ) :
    _root_.AFT.RepresentedPolynomial.singleGenerating reference (_root_.CurrentAFT.SelectedOrdinaryRoot.pushLinear law embedding score) =
      ∑ source, (law.weight source * score source) • _root_.AFT.RepresentedPolynomial.centeredFactor reference (embedding source) := by
  unfold _root_.AFT.RepresentedPolynomial.singleGenerating _root_.CurrentAFT.SelectedOrdinaryRoot.pushLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp only [apply_ite, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true,
    MvPolynomial.smul_eq_C_mul]
open _root_.P2M8f8f5b7e renaming h343 → _p2mH343
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h340 (security : ℕ) (score : _root_.CurrentAFT.SelectedOrdinaryRoot.Input security → ℝ)
    (hmass : ∑ color, _root_.CurrentAFT.SelectedOrdinaryRoot.rawMass security score color = 0) :
    _root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.SelectedOrdinaryRoot.rawMass security score) = _root_.CurrentAFT.RootSelectedPhysicalColumns.ordinaryNumerator security score := by
  rw [← _p2mH16 (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight _ hmass]
  have hmassEq : _root_.CurrentAFT.SelectedOrdinaryRoot.rawMass security score =
      ∑ root : _root_.CurrentAFT.CycleRootExpansion.Root security, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root •
        _root_.CurrentAFT.SelectedOrdinaryRoot.pushLinear (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.SelectedOrdinaryRoot.rootEmbedding security root) (fun center => score (root, center)) := by
    funext color
    simp only [_root_.CurrentAFT.SelectedOrdinaryRoot.rawMass_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmassEq]
  unfold _root_.AFT.RepresentedPolynomial.singleGenerating
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro root _
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  change MvPolynomial.C ((_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root) *
    _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.SelectedOrdinaryRoot.pushLinear (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.SelectedOrdinaryRoot.rootEmbedding security root) (fun center => score (root, center))) = _
  rw [_p2mH343, MvPolynomial.smul_eq_C_mul]
open _root_.P2M8f8f5b7e renaming h340 → _p2mH340
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h341 (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool)
    (score : _root_.CurrentAFT.RootOrdinaryGroupedChannel.Input security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootOrdinaryGroupedChannel.channel security order horder tagged score) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootLocalDenominators.ordinaryPolynomial security) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootSelectedPhysicalColumns.ordinaryNumerator security (_root_.CurrentAFT.SelectedOrdinaryRoot.controlCenterLinear security
        (_root_.CurrentAFT.RootOrdinaryGroupedChannel.toRaw security (_root_.CurrentAFT.RootOrdinaryGroupedChannel.projector security tagged score)))) := by
  rw [_p2mH318, map_add, map_one, _p2mH326,
    _p2mH340 security _ (_root_.CurrentAFT.SelectedOrdinaryRoot.centeredMass_zero security _)]
open _root_.P2M8f8f5b7e renaming h341 → _p2mH341
end
open _root_.P2M8f8f5b7e renaming h340 → _p2mH340
open _root_.P2M8f8f5b7e renaming h341 → _p2mH341
open _root_.P2M8f8f5b7e renaming h342 → _p2mH342
open _root_.P2M8f8f5b7e renaming h343 → _p2mH343
end CurrentAFT.RootSelectedPhysicalColumns
open _root_.P2M8f8f5b7e renaming h340 → _p2mH340
open _root_.P2M8f8f5b7e renaming h341 → _p2mH341
open _root_.P2M8f8f5b7e renaming h342 → _p2mH342
open _root_.P2M8f8f5b7e renaming h343 → _p2mH343
end
open _root_.P2M8f8f5b7e renaming h340 → _p2mH340
open _root_.P2M8f8f5b7e renaming h341 → _p2mH341
open _root_.P2M8f8f5b7e renaming h342 → _p2mH342
open _root_.P2M8f8f5b7e renaming h343 → _p2mH343
section
namespace CurrentAFT.RootSelectedControlCenter
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  ControlCoordinates GradedControlAlgebra CoefficientHilbert
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootSelectedControlCenter.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootSelectedControlCenter.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootSelectedControlCenter.classicalSigmaDecidableEq
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
section Generic
variable {RootData Control : Type*} [Fintype Control]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h337 (law : _root_.AFT.FiniteDist Control) (score : (RootData × Control) → ℝ)
    (hcentered : ∀ roots, law.expectation (fun control => score (roots, control)) = 0) :
    _root_.CurrentAFT.RootSelectedControlCenter.centerControl law score = score := by
  funext sample
  change score sample - law.expectation (fun control => score (sample.1, control)) = _
  rw [hcentered, sub_zero]
open _root_.P2M8f8f5b7e renaming h337 → _p2mH337
end Generic
open _root_.P2M8f8f5b7e renaming h337 → _p2mH337
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h413 {Group Root : Type*} [Fintype Group] [DecidableEq Group] [Fintype Root]
    (RootSlots Controls : Group → Type*) [∀ group, Fintype (RootSlots group)] [∀ group, Fintype (Controls group)]
    (roots : Sigma RootSlots → Root) (controls : (group : Group) → Controls group)
    (group : Group) (control : Controls group) :
    _root_.CurrentAFT.GroupedSourceNorm.wordEquiv RootSlots Controls (roots, Function.update controls group control) =
      Function.update (_root_.CurrentAFT.GroupedSourceNorm.wordEquiv RootSlots Controls (roots, controls)) group
        ((fun slot => roots ⟨group, slot⟩), control) := by
  funext other
  by_cases hequal : other = group
  · subst other
    simp only [Function.update_self, _root_.CurrentAFT.GroupedSourceNorm.wordEquiv, Equiv.coe_fn_mk]
  · simp only [_root_.CurrentAFT.GroupedSourceNorm.wordEquiv, Equiv.coe_fn_mk, Function.update_of_ne hequal]
open _root_.P2M8f8f5b7e renaming h413 → _p2mH413
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h339 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged) (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged) :
    _root_.CurrentAFT.RootSelectedControlCenter.projector selection tagged group (fun sample => _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel (Function.update word group sample)) =
      fun sample => _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel (Function.update word group sample) := by
  rcases group with role | kept
  · apply _p2mH337
    intro roots
    let baseWord : _root_.CurrentAFT.PairedRootInput.GroupInput selection tagged := Function.update word (.inl role) (roots, word (.inl role) |>.2)
    let global := (_root_.CurrentAFT.GroupedSourceNorm.wordEquiv (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged)).symm baseWord
    have h := _p2mH195 selection tagged layout kernel global.1 global.2 role
    have hword (control : _root_.CurrentAFT.RaisingPatternBudget.RoleInput security r s role) :
        _root_.CurrentAFT.GroupedSourceNorm.wordEquiv (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged)
          (global.1, Function.update global.2 (.inl role) control) =
            Function.update word (.inl role) (roots, control) := by
      rw [_p2mH413]
      have hequal : _root_.CurrentAFT.GroupedSourceNorm.wordEquiv (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged) global = baseWord :=
        Equiv.apply_symm_apply _ baseWord
      have hroot : (fun slot => global.1 ⟨.inl role, slot⟩) = roots := by
        change (baseWord (.inl role)).1 = roots
        simp only [baseWord, Function.update_self]
      rw [hroot]
      change Function.update (_root_.CurrentAFT.GroupedSourceNorm.wordEquiv (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) (_root_.CurrentAFT.PairedRootInput.ControlInput selection tagged) global)
        (.inl role) (roots, control) = _
      rw [hequal]
      simp only [baseWord, Function.update_idem]
    simpa only [hword, _root_.CurrentAFT.PairedRootInput.ControlInput, Sum.elim_inl] using h
  · rfl
open _root_.P2M8f8f5b7e renaming h339 → _p2mH339
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h338 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.AFT.DependentTensorChannel.apply (_root_.CurrentAFT.RootSelectedControlCenter.projector selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) =
      _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel :=
  _p2mH103 _ _ (fun group word => _p2mH339 selection tagged layout kernel word group)
open _root_.P2M8f8f5b7e renaming h338 → _p2mH338
end
open _root_.P2M8f8f5b7e renaming h337 → _p2mH337
open _root_.P2M8f8f5b7e renaming h338 → _p2mH338
open _root_.P2M8f8f5b7e renaming h339 → _p2mH339
open _root_.P2M8f8f5b7e renaming h413 → _p2mH413
end CurrentAFT.RootSelectedControlCenter
open _root_.P2M8f8f5b7e renaming h337 → _p2mH337
open _root_.P2M8f8f5b7e renaming h338 → _p2mH338
open _root_.P2M8f8f5b7e renaming h339 → _p2mH339
open _root_.P2M8f8f5b7e renaming h413 → _p2mH413
end
open _root_.P2M8f8f5b7e renaming h337 → _p2mH337
open _root_.P2M8f8f5b7e renaming h338 → _p2mH338
open _root_.P2M8f8f5b7e renaming h339 → _p2mH339
namespace CurrentAFT.RootSelectedControlCenter
end CurrentAFT.RootSelectedControlCenter
namespace CurrentAFT.RootSelectedControlCenter.centerControl
end CurrentAFT.RootSelectedControlCenter.centerControl
namespace CurrentAFT.RootSelectedControlCenter.projector
end CurrentAFT.RootSelectedControlCenter.projector
namespace CurrentAFT.RootSelectedPhysicalColumns
end CurrentAFT.RootSelectedPhysicalColumns
section
namespace CurrentAFT.RootSelectedPhysicalLinear
open AFT DiffuseProfiles ProposalPrimary ActualControls CycleRootExpansion
  LocalCoefficientFamily RootTaggedSelected RootSelectedPhysicalColumns RootLocalDenominators
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootSelectedPhysicalLinear.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootSelectedPhysicalLinear.safeDecidableEq
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h345 (security order : ℕ) (tagged : Fin 2 → Bool) (score : _root_.CurrentAFT.RootPrimaryGroupedChannel.Input security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootPrimaryGroupedChannel.channel security order tagged score) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootLocalDenominators.primaryPolynomial security) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootSelectedPhysicalLinear.primaryProjected security tagged score) :=
  _p2mH342 security order tagged score
open _root_.P2M8f8f5b7e renaming h345 → _p2mH345
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h344 (security order : ℕ) (horder : 1 ≤ order) (tagged : Bool) (score : _root_.CurrentAFT.RootOrdinaryGroupedChannel.Input security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootOrdinaryGroupedChannel.channel security order horder tagged score) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootLocalDenominators.ordinaryPolynomial security) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootSelectedPhysicalLinear.ordinaryProjected security tagged score) :=
  _p2mH341 security order horder tagged score
open _root_.P2M8f8f5b7e renaming h344 → _p2mH344
end
open _root_.P2M8f8f5b7e renaming h344 → _p2mH344
open _root_.P2M8f8f5b7e renaming h345 → _p2mH345
end CurrentAFT.RootSelectedPhysicalLinear
open _root_.P2M8f8f5b7e renaming h344 → _p2mH344
open _root_.P2M8f8f5b7e renaming h345 → _p2mH345
end
open _root_.P2M8f8f5b7e renaming h344 → _p2mH344
open _root_.P2M8f8f5b7e renaming h345 → _p2mH345
namespace CurrentAFT.PairedOutputProduct
end CurrentAFT.PairedOutputProduct
namespace CurrentAFT.PairedOutputProduct.remaining
end CurrentAFT.PairedOutputProduct.remaining
namespace CurrentAFT.PairedOutputProduct.selectedBodies
end CurrentAFT.PairedOutputProduct.selectedBodies
namespace CurrentAFT.PairedOutputProduct.selectedPairs
end CurrentAFT.PairedOutputProduct.selectedPairs
namespace CurrentAFT.PairedRootInput.reference
end CurrentAFT.PairedRootInput.reference
namespace CurrentAFT.RootGroupedSourceFormula
end CurrentAFT.RootGroupedSourceFormula
namespace CurrentAFT.RootGroupedSourceFormula.completedTest
end CurrentAFT.RootGroupedSourceFormula.completedTest
namespace CurrentAFT.RootGroupedSourceFormula.controlWeightedTest
end CurrentAFT.RootGroupedSourceFormula.controlWeightedTest
section
namespace CurrentAFT.TypedTaggedPhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection TaggedOutputFock
  JointTaggedPhysicalFock PairedOutputPlacement LocalReferenceEnergy
  RootBackgroundPolynomial BackgroundPolynomialEvaluation RootLocalDenominators
  CycleRootExpansion ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.TypedTaggedPhysical.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.TypedTaggedPhysical.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.TypedTaggedPhysical.classicalSigmaDecidableEq
attribute [local instance] _root_.CurrentAFT.TypedTaggedPhysical.actualGroupDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
section Generic
variable {Index Color : Type*} [Fintype Index] [Fintype Color]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h392 (slots : Index → Type*) [∀ index, Fintype (slots index)]
    (reference : Color → ℝ) (mass : (index : Index) → (slots index → Color) → ℝ) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference
      (fun word : Sigma slots → Color => ∏ index, mass index (fun slot => word ⟨index, slot⟩)) =
      ∏ index, _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference (mass index) := by
  have hequiv := (Equiv.piCurry (fun index (_ : slots index) => Color)).sum_comp
    (fun word => ∏ index, MvPolynomial.C (mass index (word index)) *
      ∏ slot, _root_.AFT.RepresentedPolynomial.centeredFactor reference (word index slot))
  unfold _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.smul_eq_C_mul,
    map_prod, Fintype.prod_sigma]
  calc
    _ = ∑ word : Sigma slots → Color,
        ∏ index, (MvPolynomial.C (mass index (fun slot => word ⟨index, slot⟩)) *
          ∏ slot, _root_.AFT.RepresentedPolynomial.centeredFactor reference (word ⟨index, slot⟩)) := by
      simp only [Finset.prod_mul_distrib]
    _ = ∑ word : (index : Index) → slots index → Color,
        ∏ index, (MvPolynomial.C (mass index (word index)) *
          ∏ slot, _root_.AFT.RepresentedPolynomial.centeredFactor reference (word index slot)) := hequiv
    _ = _ := (Fintype.prod_sum (fun index (word : slots index → Color) =>
      MvPolynomial.C (mass index word) * ∏ slot, _root_.AFT.RepresentedPolynomial.centeredFactor reference (word slot))).symm
open _root_.P2M8f8f5b7e renaming h392 → _p2mH392
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h393 {Left Right : Type*} [Fintype Left] [Fintype Right]
    (reference : Color → ℝ) (first : (Left → Color) → ℝ) (second : (Right → Color) → ℝ) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference
      (fun word : Left ⊕ Right → Color => first (word ∘ Sum.inl) * second (word ∘ Sum.inr)) =
      _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference first * _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference second := by
  unfold _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, MvPolynomial.smul_eq_C_mul]
  rw [← (Equiv.sumArrowEquivProdArrow Left Right Color).symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.sumArrowEquivProdArrow, Equiv.coe_fn_symm_mk,
    Fintype.prod_sum_type, Function.comp_def, Sum.elim_inl, Sum.elim_inr, map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro firstWord _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro secondWord _
  ring
open _root_.P2M8f8f5b7e renaming h393 → _p2mH393
end Generic
open _root_.P2M8f8f5b7e renaming h392 → _p2mH392
open _root_.P2M8f8f5b7e renaming h393 → _p2mH393
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h391 (security r s : ℕ) (compensator attachment : Fin r → ℤ)
    (body : Fin s → ℤ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.TypedTaggedPhysical.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.JointTaggedPhysicalFock.jointMass security r s compensator attachment body kernel) =
      ∑ input : Fin (r + s) → _root_.CurrentAFT.JointTaggedPhysicalFock.Group security,
        _root_.CurrentAFT.JointTaggedPhysicalFock.finiteKernel kernel input • ∏ index,
          _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
            (_root_.CurrentAFT.JointTaggedPhysicalFock.physicalChannel security r s compensator attachment body index (Pi.single (input index) 1)) := by
  have hmass : _root_.CurrentAFT.JointTaggedPhysicalFock.jointMass security r s compensator attachment body kernel =
      ∑ input : Fin (r + s) → _root_.CurrentAFT.JointTaggedPhysicalFock.Group security,
        _root_.CurrentAFT.JointTaggedPhysicalFock.finiteKernel kernel input • fun word => ∏ index,
          _root_.CurrentAFT.JointTaggedPhysicalFock.physicalChannel security r s compensator attachment body index (Pi.single (input index) 1)
            (fun slot => word ⟨index, slot⟩) := by
    funext word
    simp only [_root_.CurrentAFT.JointTaggedPhysicalFock.jointMass, _root_.AFT.JointPhysicalChannel.mass, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmass, map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro input _
  congr 1
  exact _p2mH392 (_root_.CurrentAFT.JointTaggedPhysicalFock.physicalSlots r s) (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight _
open _root_.P2M8f8f5b7e renaming h391 → _p2mH391
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h390 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (queue : ℤ)
    (roots : _root_.CurrentAFT.ActualBlockFock.BlockIndex security → ℤ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.TypedTaggedPhysical.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue roots kernel =
      _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.TypedTaggedPhysical.selectedMass selection roots kernel) *
        ∏ index : selection.kept, _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security (_root_.CurrentAFT.TypedTaggedPhysical.blockLaw security queue roots index.val) := by
  unfold _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial _root_.CurrentAFT.TypedTaggedPhysical.conditionalMass _root_.AFT.BlockProducts.taggedBlockMass
  rw [_p2mH393]
  congr 1
  unfold _root_.AFT.BlockProducts.blockMass
  rw [_p2mH392]
  apply Finset.prod_congr rfl
  intro index _
  exact _root_.CurrentAFT.RootLocalDenominators.generating_eq_block security _
open _root_.P2M8f8f5b7e renaming h390 → _p2mH390
end
open _root_.P2M8f8f5b7e renaming h390 → _p2mH390
open _root_.P2M8f8f5b7e renaming h391 → _p2mH391
open _root_.P2M8f8f5b7e renaming h392 → _p2mH392
open _root_.P2M8f8f5b7e renaming h393 → _p2mH393
end CurrentAFT.TypedTaggedPhysical
open _root_.P2M8f8f5b7e renaming h390 → _p2mH390
open _root_.P2M8f8f5b7e renaming h391 → _p2mH391
open _root_.P2M8f8f5b7e renaming h392 → _p2mH392
open _root_.P2M8f8f5b7e renaming h393 → _p2mH393
end
open _root_.P2M8f8f5b7e renaming h390 → _p2mH390
open _root_.P2M8f8f5b7e renaming h391 → _p2mH391
open _root_.P2M8f8f5b7e renaming h392 → _p2mH392
open _root_.P2M8f8f5b7e renaming h393 → _p2mH393
section
namespace CurrentAFT.FinitePolynomialTensor
open AFT
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input Middle : Index → Type*} [∀ index, Fintype (Input index)] [∀ index, Fintype (Middle index)]
  {Value : Type*} [CommRing Value] [Algebra ℝ Value]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h117 {Source : Type*} [Fintype Source]
    (channel : (Source → ℝ) →ₗ[ℝ] Value) (score : Source → ℝ) :
    channel score = ∑ source, score source • channel (Pi.single source 1) := by
  classical
  have hscore : score = ∑ source, score source • (Pi.single source 1 : Source → ℝ) := by
    funext point
    simp [Pi.single_apply]
  conv_lhs => rw [hscore]
  simp only [map_sum, map_smul]
open _root_.P2M8f8f5b7e renaming h117 → _p2mH117
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h119
    (preprocess : ∀ index, (Input index → ℝ) →ₗ[ℝ] (Middle index → ℝ))
    (channels : ∀ index, (Middle index → ℝ) →ₗ[ℝ] Value)
    (input : ((index : Index) → Input index) → ℝ) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis (fun index => (channels index).comp (preprocess index)) input =
      _root_.CurrentAFT.FinitePolynomialTensor.synthesis channels (_root_.AFT.DependentTensorChannel.apply preprocess input) := by
  unfold _root_.CurrentAFT.FinitePolynomialTensor.synthesis
  simp only [LinearMap.comp_apply]
  have hcolumn (index : Index) (source : Input index) :
      channels index (preprocess index (Pi.single source 1)) =
        ∑ middle, preprocess index (Pi.single source 1) middle • channels index (Pi.single middle 1) :=
    _p2mH117 (channels index) _
  simp_rw [hcolumn, Fintype.prod_sum]
  simp only [Finset.prod_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  unfold _root_.AFT.DependentTensorChannel.apply
  simp only [Finset.sum_smul]
open _root_.P2M8f8f5b7e renaming h119 → _p2mH119
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h120
    (channels physical : ∀ index, (Input index → ℝ) →ₗ[ℝ] Value) (denominator : Index → Value)
    (hcolumn : ∀ index source, channels index (Pi.single source 1) * denominator index =
      physical index (Pi.single source 1))
    (input : ((index : Index) → Input index) → ℝ) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis channels input * (∏ index, denominator index) = _root_.CurrentAFT.FinitePolynomialTensor.synthesis physical input := by
  unfold _root_.CurrentAFT.FinitePolynomialTensor.synthesis
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro source _
  rw [smul_mul_assoc, ← Finset.prod_mul_distrib]
  simp only [hcolumn]
open _root_.P2M8f8f5b7e renaming h120 → _p2mH120
variable {Output : Type*} [CommRing Output] [Algebra ℝ Output]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h118 (map : Value →ₐ[ℝ] Output)
    (channels : ∀ index, (Input index → ℝ) →ₗ[ℝ] Value)
    (input : ((index : Index) → Input index) → ℝ) :
    map (_root_.CurrentAFT.FinitePolynomialTensor.synthesis channels input) = _root_.CurrentAFT.FinitePolynomialTensor.synthesis (fun index => map.toLinearMap.comp (channels index)) input := by
  simp only [_root_.CurrentAFT.FinitePolynomialTensor.synthesis, map_sum, map_smul, map_prod, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
open _root_.P2M8f8f5b7e renaming h118 → _p2mH118
end
open _root_.P2M8f8f5b7e renaming h117 → _p2mH117
open _root_.P2M8f8f5b7e renaming h118 → _p2mH118
open _root_.P2M8f8f5b7e renaming h119 → _p2mH119
open _root_.P2M8f8f5b7e renaming h120 → _p2mH120
end CurrentAFT.FinitePolynomialTensor
open _root_.P2M8f8f5b7e renaming h117 → _p2mH117
open _root_.P2M8f8f5b7e renaming h118 → _p2mH118
open _root_.P2M8f8f5b7e renaming h119 → _p2mH119
open _root_.P2M8f8f5b7e renaming h120 → _p2mH120
end
open _root_.P2M8f8f5b7e renaming h117 → _p2mH117
open _root_.P2M8f8f5b7e renaming h118 → _p2mH118
open _root_.P2M8f8f5b7e renaming h119 → _p2mH119
open _root_.P2M8f8f5b7e renaming h120 → _p2mH120
namespace CurrentAFT.FinitePolynomialTensor
end CurrentAFT.FinitePolynomialTensor
namespace CurrentAFT.FinitePolynomialTensor.synthesis
end CurrentAFT.FinitePolynomialTensor.synthesis
namespace CurrentAFT.TypedTaggedPhysical
end CurrentAFT.TypedTaggedPhysical
section
namespace CurrentAFT.TypedRolePolynomial
open AFT AFT.RepresentedPolynomial ActualBlockFock JointTaggedPhysicalFock
  LocalReferenceEnergy ControlCoordinates RaisingPatternBudget TaggedPhysicalFock
  OrdinaryPhysicalFock
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.TypedRolePolynomial.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.TypedRolePolynomial.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.TypedRolePolynomial.actualGroupDecidableEq
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw
section Generic
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {Input Output : Index → Type*} [∀ index, Fintype (Input index)]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h382 (projection : ∀ index, Output index → Input index)
    (kernel : ((index : Index) → Input index) → ℝ) (output : ∀ index, Output index) :
    _root_.AFT.DependentTensorChannel.apply (fun index => _root_.CurrentAFT.TypedRolePolynomial.pullbackLinear (projection index)) kernel output =
      kernel (fun index => projection index (output index)) := by
  unfold _root_.AFT.DependentTensorChannel.apply
  rw [Finset.sum_eq_single (fun index => projection index (output index))]
  · simp only [_root_.CurrentAFT.TypedRolePolynomial.pullbackLinear, LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same,
      Finset.prod_const_one, mul_one]
  · intro source _ hsource
    have hsome : ∃ index, source index ≠ projection index (output index) := by
      by_contra hnone
      apply hsource
      funext index
      exact not_not.mp (not_exists.mp hnone index)
    obtain ⟨index, hindex⟩ := hsome
    have hzero : _root_.CurrentAFT.TypedRolePolynomial.pullbackLinear (projection index) (Pi.single (source index) 1) (output index) = 0 :=
      Pi.single_eq_of_ne (Ne.symm hindex) 1
    rw [Finset.prod_eq_zero (Finset.mem_univ index) hzero, mul_zero]
  · simp
open _root_.P2M8f8f5b7e renaming h382 → _p2mH382
end Generic
open _root_.P2M8f8f5b7e renaming h382 → _p2mH382
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h386 (security r s : ℕ) (role : _root_.CurrentAFT.RaisingPatternBudget.Role r s) :
    (_root_.CurrentAFT.TypedRolePolynomial.reduce security r s role).comp (_root_.CurrentAFT.TypedRolePolynomial.lift security r s role) = LinearMap.id := by
  apply LinearMap.ext
  intro score
  funext output
  cases role
  · change (_root_.CurrentAFT.ActualControls.bodyReference security).expectation (fun _ => score output) = score output
    exact _root_.AFT.FiniteDist.expectation_const _ _
  · change (_root_.CurrentAFT.ProposalPrimary.primaryLaw security).expectation (fun _ => score output) = score output
    exact _root_.AFT.FiniteDist.expectation_const _ _
open _root_.P2M8f8f5b7e renaming h386 → _p2mH386
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h388 (security : ℕ) {r s : ℕ}
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.TypedRolePolynomial.typedKernel security kernel.val = _root_.CurrentAFT.RaisingPatternKernel.inputJoint security kernel := rfl
open _root_.P2M8f8f5b7e renaming h388 → _p2mH388
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h389 (security r s : ℕ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.TypedRolePolynomial.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.AFT.DependentTensorChannel.apply (_root_.CurrentAFT.TypedRolePolynomial.lift security r s) (_root_.CurrentAFT.TypedRolePolynomial.typedKernel security kernel) =
      _root_.CurrentAFT.JointTaggedPhysicalFock.unpairedKernel kernel := by
  funext word
  rw [show _root_.CurrentAFT.TypedRolePolynomial.lift security r s = fun role => _root_.CurrentAFT.TypedRolePolynomial.pullbackLinear (_root_.CurrentAFT.TypedRolePolynomial.roleProjection security r s role) from rfl,
    _p2mH382]
  rfl
open _root_.P2M8f8f5b7e renaming h389 → _p2mH389
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h387 (security r s : ℕ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.TypedRolePolynomial.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.AFT.DependentTensorChannel.apply (_root_.CurrentAFT.TypedRolePolynomial.reduce security r s) (_root_.CurrentAFT.JointTaggedPhysicalFock.unpairedKernel kernel) =
      _root_.CurrentAFT.TypedRolePolynomial.typedKernel security kernel := by
  rw [← _p2mH389 security r s kernel, ← _p2mH101]
  have hchannels : (fun role => (_root_.CurrentAFT.TypedRolePolynomial.reduce security r s role).comp (_root_.CurrentAFT.TypedRolePolynomial.lift security r s role)) =
      fun role => _root_.CurrentAFT.TypedRolePolynomial.pullbackLinear (fun value : _root_.CurrentAFT.RaisingPatternBudget.RoleInput security r s role => value) := by
    funext role
    rw [_p2mH386]
    rfl
  rw [hchannels]
  funext word
  exact _p2mH382 _ _ _
open _root_.P2M8f8f5b7e renaming h387 → _p2mH387
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h383 (security r s : ℕ) (compensator attachment : Fin r → ℤ) (body : Fin s → ℤ)
    (role : _root_.CurrentAFT.RaisingPatternBudget.Role r s) (score : _root_.CurrentAFT.JointTaggedPhysicalFock.Group security → ℝ) :
    _root_.CurrentAFT.TypedRolePolynomial.common security r s compensator attachment body role score =
      _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
        (_root_.CurrentAFT.JointTaggedPhysicalFock.roleChannel security r s compensator attachment body role score) := by
  cases role <;> rfl
open _root_.P2M8f8f5b7e renaming h383 → _p2mH383
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h384 (security r s : ℕ) (compensator attachment : Fin r → ℤ)
    (body : Fin s → ℤ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.TypedRolePolynomial.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.TypedRolePolynomial.common security r s compensator attachment body) (_root_.CurrentAFT.JointTaggedPhysicalFock.unpairedKernel kernel) =
      _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.TypedRolePolynomial.raw security r s compensator attachment body)
        (_root_.CurrentAFT.TypedRolePolynomial.typedKernel security kernel) := by
  rw [show _root_.CurrentAFT.TypedRolePolynomial.common security r s compensator attachment body =
      fun role => (_root_.CurrentAFT.TypedRolePolynomial.raw security r s compensator attachment body role).comp (_root_.CurrentAFT.TypedRolePolynomial.reduce security r s role) from rfl,
    _p2mH119, _p2mH387]
open _root_.P2M8f8f5b7e renaming h384 → _p2mH384
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h385 (security r s : ℕ) (compensator attachment : Fin r → ℤ)
    (body : Fin s → ℤ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.TypedRolePolynomial.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.JointTaggedPhysicalFock.jointMass security r s compensator attachment body kernel) =
      _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.TypedRolePolynomial.raw security r s compensator attachment body)
        (_root_.CurrentAFT.TypedRolePolynomial.typedKernel security kernel) := by
  rw [← _p2mH384 security r s compensator attachment body kernel,
    _p2mH391]
  unfold _root_.CurrentAFT.FinitePolynomialTensor.synthesis
  rw [← (Equiv.piCongrLeft (fun _ : Fin (r + s) => _root_.CurrentAFT.JointTaggedPhysicalFock.Group security)
    (finSumFinEquiv : _root_.CurrentAFT.RaisingPatternBudget.Role r s ≃ Fin (r + s))).sum_comp]
  apply Finset.sum_congr rfl
  intro input _
  have hkernel : _root_.CurrentAFT.JointTaggedPhysicalFock.finiteKernel kernel
      (Equiv.piCongrLeft (fun _ : Fin (r + s) => _root_.CurrentAFT.JointTaggedPhysicalFock.Group security) finSumFinEquiv input) =
      _root_.CurrentAFT.JointTaggedPhysicalFock.unpairedKernel kernel input := by
    unfold _root_.CurrentAFT.JointTaggedPhysicalFock.finiteKernel
    congr 1
    funext role
    exact Equiv.piCongrLeft_apply_apply (fun _ : Fin (r + s) => _root_.CurrentAFT.JointTaggedPhysicalFock.Group security)
      finSumFinEquiv input role
  rw [hkernel]
  congr 1
  rw [← finSumFinEquiv.prod_comp]
  apply Finset.prod_congr rfl
  intro role _
  simp only [_root_.CurrentAFT.JointTaggedPhysicalFock.physicalChannel, Equiv.piCongrLeft_apply_apply, _p2mH383]
  exact congrArg (fun other : _root_.CurrentAFT.RaisingPatternBudget.Role r s => _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
    (_root_.CurrentAFT.JointTaggedPhysicalFock.roleChannel security r s compensator attachment body other (Pi.single (input role) 1)))
      ((finSumFinEquiv : _root_.CurrentAFT.RaisingPatternBudget.Role r s ≃ Fin (r + s)).symm_apply_apply role)
open _root_.P2M8f8f5b7e renaming h385 → _p2mH385
end
open _root_.P2M8f8f5b7e renaming h382 → _p2mH382
open _root_.P2M8f8f5b7e renaming h383 → _p2mH383
open _root_.P2M8f8f5b7e renaming h384 → _p2mH384
open _root_.P2M8f8f5b7e renaming h385 → _p2mH385
open _root_.P2M8f8f5b7e renaming h386 → _p2mH386
open _root_.P2M8f8f5b7e renaming h387 → _p2mH387
open _root_.P2M8f8f5b7e renaming h388 → _p2mH388
open _root_.P2M8f8f5b7e renaming h389 → _p2mH389
end CurrentAFT.TypedRolePolynomial
open _root_.P2M8f8f5b7e renaming h382 → _p2mH382
open _root_.P2M8f8f5b7e renaming h383 → _p2mH383
open _root_.P2M8f8f5b7e renaming h384 → _p2mH384
open _root_.P2M8f8f5b7e renaming h385 → _p2mH385
open _root_.P2M8f8f5b7e renaming h386 → _p2mH386
open _root_.P2M8f8f5b7e renaming h387 → _p2mH387
open _root_.P2M8f8f5b7e renaming h388 → _p2mH388
open _root_.P2M8f8f5b7e renaming h389 → _p2mH389
end
open _root_.P2M8f8f5b7e renaming h382 → _p2mH382
open _root_.P2M8f8f5b7e renaming h383 → _p2mH383
open _root_.P2M8f8f5b7e renaming h384 → _p2mH384
open _root_.P2M8f8f5b7e renaming h385 → _p2mH385
open _root_.P2M8f8f5b7e renaming h386 → _p2mH386
open _root_.P2M8f8f5b7e renaming h387 → _p2mH387
open _root_.P2M8f8f5b7e renaming h388 → _p2mH388
open _root_.P2M8f8f5b7e renaming h389 → _p2mH389
namespace CurrentAFT.JointTaggedPhysicalFock
end CurrentAFT.JointTaggedPhysicalFock
namespace CurrentAFT.JointTaggedPhysicalFock.physicalChannel
end CurrentAFT.JointTaggedPhysicalFock.physicalChannel
namespace CurrentAFT.RootUnselectedGrouped
end CurrentAFT.RootUnselectedGrouped
namespace CurrentAFT.RootUnselectedGrouped.extractLinear
end CurrentAFT.RootUnselectedGrouped.extractLinear
namespace CurrentAFT.RootUnselectedGrouped.inputEquiv
end CurrentAFT.RootUnselectedGrouped.inputEquiv
namespace CurrentAFT.TypedRolePolynomial
end CurrentAFT.TypedRolePolynomial
namespace CurrentAFT.TypedRolePolynomial.pullbackLinear
end CurrentAFT.TypedRolePolynomial.pullbackLinear
namespace CurrentAFT.TypedRolePolynomial.reduce
end CurrentAFT.TypedRolePolynomial.reduce
namespace CurrentAFT.TypedRolePolynomial.roleProjection
end CurrentAFT.TypedRolePolynomial.roleProjection
section
namespace CurrentAFT.RootUnselectedPhysicalLinear
open AFT AFT.RepresentedPolynomial ActualBlockFock CycleRootExpansion DiffuseProfiles
  ProposalPrimary ActualControls LocalReferenceEnergy RootTaggedLocal UniformBodyProfiles
  RootUnselectedGrouped RootUnselectedBlockChannel RootIndependentBackground
  RootLocalDenominators BodyRootAverages
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootUnselectedPhysicalLinear.classicalFinDecidableEq
attribute [local irreducible] Parameters.base primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h367 (security : ℕ) (queue : ℤ) (block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security) (root : _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.RootUnselectedPhysicalLinear.positiveAt security queue block root = _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security
      (_root_.CurrentAFT.TypedTaggedPhysical.blockLaw security queue (fun _ => root.val) block) := by
  rcases block with leg | (center | point)
  · rfl
  · change _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.RootTaggedLocal.shiftedLaw security .free 0 root).weight =
      _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security
        (_root_.CurrentAFT.ActualBlockFock.singletonLaw ((_root_.CurrentAFT.ProposalPrimary.centerLaw security).map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security root.val)))
    rw [_p2mH278, ← _root_.CurrentAFT.RootLocalDenominators.uniformReference_eq]
    rfl
  · change _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.RootTaggedLocal.shiftedLaw security .queue queue root).weight =
      _root_.CurrentAFT.RootBackgroundPolynomial.blockGenerating security
        (_root_.CurrentAFT.ActualBlockFock.singletonLaw ((_root_.CurrentAFT.ProposalPrimary.safeLaw security).map (_root_.CurrentAFT.ProposalPrimary.shiftEquiv security (root.val + queue))))
    rw [_p2mH278, ← _root_.CurrentAFT.RootLocalDenominators.uniformReference_eq]
    congr 1
    unfold _root_.CurrentAFT.RootTaggedLocal.shiftedLaw _root_.CurrentAFT.UniformBodyProfiles.preRootLaw
    rw [_p2mH85, add_comm queue]
open _root_.P2M8f8f5b7e renaming h367 → _p2mH367
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h414 {Color : Type*} [Fintype Color]
    (law : _root_.AFT.FiniteDist Color) (input value : Color → ℝ) :
    (∑ point, law.weight point * _root_.AFT.TensorChannel.center law input point * value point) =
      ∑ point, law.weight point * input point * (value point - law.expectation value) := by
  calc
    _ = law.expectation (fun point => input point * value point) - law.expectation input * law.expectation value := by
      simp only [_root_.AFT.TensorChannel.center_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
      congr 1
      · unfold _root_.AFT.FiniteDist.expectation
        apply Finset.sum_congr rfl
        intro point _
        ring
      · unfold _root_.AFT.FiniteDist.expectation
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro point _
        ring
    _ = _ := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      simp only [_root_.AFT.FiniteDist.expectation, mul_assoc]
open _root_.P2M8f8f5b7e renaming h414 → CurrentAFT.RootUnselectedPhysicalLinear.covariance_center
open _root_.P2M8f8f5b7e renaming h414 → _p2mH414
set_option maxRecDepth 8192
private def _root_.P2M8f8f5b7e.h415 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) (color : _root_.CurrentAFT.RootUnselectedPhysicalLinear.Palette security) : ℝ :=
  ∑ root, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root * input root * (_root_.CurrentAFT.RootTaggedLocal.shiftedLaw security role queue root).weight color
open _root_.P2M8f8f5b7e renaming h415 → CurrentAFT.RootUnselectedPhysicalLinear.singletonMass
open _root_.P2M8f8f5b7e renaming h415 → _p2mH415
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h416 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _p2mH415 security role queue (_root_.AFT.TensorChannel.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) input) =
      _root_.CurrentAFT.RootTaggedLocal.rootMass security role queue input := by
  funext color
  have hh := _p2mH414 (_root_.CurrentAFT.CycleRootExpansion.rootReference security) input
    (fun root => (_root_.CurrentAFT.RootTaggedLocal.shiftedLaw security role queue root).weight color)
  simpa only [_p2mH415, _root_.CurrentAFT.RootTaggedLocal.rootMass, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.CurrentAFT.RootTaggedLocal.deviationProfile, Pi.sub_apply, _root_.CurrentAFT.RootTaggedLocal.meanLaw, _root_.AFT.FiniteDist.mix_weight, _root_.AFT.FiniteDist.expectation] using hh
open _root_.P2M8f8f5b7e renaming h416 → _p2mH416
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h418 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    (∑ color, _p2mH415 security role queue input color) = (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation input := by
  unfold _p2mH415
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, _root_.AFT.FiniteDist.sum_one, mul_one]
  rfl
open _root_.P2M8f8f5b7e renaming h418 → CurrentAFT.RootUnselectedPhysicalLinear.singletonMass_sum
open _root_.P2M8f8f5b7e renaming h418 → _p2mH418
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h417 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_p2mH415 security role queue input) =
      ∑ root, ((_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root * input root) •
        _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.RootTaggedLocal.shiftedLaw security role queue root).weight := by
  unfold _root_.AFT.RepresentedPolynomial.singleGenerating _p2mH415
  simp only [map_sum, map_mul, Finset.sum_mul, MvPolynomial.smul_eq_C_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro root _
  apply Finset.sum_congr rfl
  intro color _
  ring
open _root_.P2M8f8f5b7e renaming h417 → _p2mH417
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h419 (security : ℕ) (role : _root_.CurrentAFT.UniformBodyProfiles.BodyRole) (queue : ℤ)
    (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.AFT.RepresentedPolynomial.profileForm (_root_.CurrentAFT.RootTaggedLocal.rootMass security role queue input) =
      ∑ root, ((_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root * _root_.AFT.TensorChannel.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) input root) •
        _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.RootTaggedLocal.shiftedLaw security role queue root).weight := by
  rw [← _p2mH416]
  rw [← _p2mH16 (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight _
    ((_p2mH418 security role queue _).trans (_p2mH18 _ _)), _p2mH417]
open _root_.P2M8f8f5b7e renaming h419 → _p2mH419
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h366 (security : ℕ) (queue : ℤ) (block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security)
    (input : _root_.CurrentAFT.CycleRootExpansion.Root security → ℝ) :
    _root_.CurrentAFT.RootUnselectedBlockChannel.numeratorPolynomial security queue input block =
      _root_.CurrentAFT.RootUnselectedPhysicalLinear.rawRoot security queue block (_root_.AFT.TensorChannel.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) input) := by
  rcases block with leg | (center | point)
  · change _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear security (_root_.AFT.TensorChannel.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) input)) = _
    have hmass : _root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear security (_root_.AFT.TensorChannel.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) input) =
        ∑ root, ((_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root * _root_.AFT.TensorChannel.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) input root) •
          (_root_.CurrentAFT.ActualBlockFock.primaryLawAt security root.val).weight := by
      funext word
      simp only [_root_.CurrentAFT.RootTaggedLegHigher.rawMassLinear, LinearMap.coe_mk, AddHom.coe_mk,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hmass, map_sum]
    simp only [map_smul, _root_.CurrentAFT.RootLocalDenominators.generating_eq_block, _root_.CurrentAFT.RootUnselectedPhysicalLinear.rawRoot, _root_.CurrentAFT.RootUnselectedPhysicalLinear.positiveAt,
      LinearMap.coe_mk, AddHom.coe_mk]
  · exact _p2mH419 security .free 0 input
  · exact _p2mH419 security .queue queue input
open _root_.P2M8f8f5b7e renaming h366 → _p2mH366
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h365 (security : ℕ) (score : _root_.CurrentAFT.RootUnselectedGrouped.Input security → ℝ) :
    _root_.CurrentAFT.RootUnselectedGrouped.extractLinear security (_root_.CurrentAFT.RootCoordinateProjection.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (0 : Fin 1) score) =
      _root_.AFT.TensorChannel.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (_root_.CurrentAFT.RootUnselectedGrouped.extractLinear security score) := by
  funext root
  change score ((_root_.CurrentAFT.RootUnselectedGrouped.inputEquiv security).symm root) - (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation
    (fun value => score (Function.update ((_root_.CurrentAFT.RootUnselectedGrouped.inputEquiv security).symm root).1 0 value,
      ((_root_.CurrentAFT.RootUnselectedGrouped.inputEquiv security).symm root).2)) = _
  congr 1
  apply congrArg (_root_.CurrentAFT.CycleRootExpansion.rootReference security).expectation
  funext value
  congr 1
  apply Prod.ext
  · funext index
    rw [Fin.eq_zero index]
    simp only [Function.update_self]
    rfl
  · rfl
open _root_.P2M8f8f5b7e renaming h365 → _p2mH365
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h368 (security : ℕ) (queue : ℤ) (block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security)
    (score : _root_.CurrentAFT.RootUnselectedGrouped.Input security → ℝ) :
    _root_.CurrentAFT.RootUnselectedPhysicalLinear.projected security queue block score = _root_.CurrentAFT.RootUnselectedBlockChannel.numeratorPolynomial security queue (_root_.CurrentAFT.RootUnselectedGrouped.extractLinear security score) block := by
  change _root_.CurrentAFT.RootUnselectedPhysicalLinear.rawRoot security queue block (_root_.CurrentAFT.RootUnselectedGrouped.extractLinear security (_root_.CurrentAFT.RootCoordinateProjection.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) 0 score)) = _
  rw [_p2mH365, _p2mH366]
open _root_.P2M8f8f5b7e renaming h368 → _p2mH368
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h364 (security order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security) (score : _root_.CurrentAFT.RootUnselectedGrouped.Input security → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.RootUnselectedGrouped.channel security order horder queue block score) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue block) =
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootUnselectedPhysicalLinear.projected security queue block score) := by
  rw [_p2mH368]
  exact _p2mH363 security order horder queue block score
open _root_.P2M8f8f5b7e renaming h364 → _p2mH364
end
open _root_.P2M8f8f5b7e renaming h364 → _p2mH364
open _root_.P2M8f8f5b7e renaming h365 → _p2mH365
open _root_.P2M8f8f5b7e renaming h366 → _p2mH366
open _root_.P2M8f8f5b7e renaming h367 → _p2mH367
open _root_.P2M8f8f5b7e renaming h368 → _p2mH368
open _root_.P2M8f8f5b7e renaming h414 → CurrentAFT.RootUnselectedPhysicalLinear.covariance_center
open _root_.P2M8f8f5b7e renaming h414 → _p2mH414
open _root_.P2M8f8f5b7e renaming h415 → CurrentAFT.RootUnselectedPhysicalLinear.singletonMass
open _root_.P2M8f8f5b7e renaming h415 → _p2mH415
open _root_.P2M8f8f5b7e renaming h416 → _p2mH416
open _root_.P2M8f8f5b7e renaming h417 → _p2mH417
open _root_.P2M8f8f5b7e renaming h418 → CurrentAFT.RootUnselectedPhysicalLinear.singletonMass_sum
open _root_.P2M8f8f5b7e renaming h418 → _p2mH418
open _root_.P2M8f8f5b7e renaming h419 → _p2mH419
end CurrentAFT.RootUnselectedPhysicalLinear
open _root_.P2M8f8f5b7e renaming h364 → _p2mH364
open _root_.P2M8f8f5b7e renaming h365 → _p2mH365
open _root_.P2M8f8f5b7e renaming h366 → _p2mH366
open _root_.P2M8f8f5b7e renaming h367 → _p2mH367
open _root_.P2M8f8f5b7e renaming h368 → _p2mH368
open _root_.P2M8f8f5b7e renaming h414 → CurrentAFT.RootUnselectedPhysicalLinear.covariance_center
open _root_.P2M8f8f5b7e renaming h414 → _p2mH414
open _root_.P2M8f8f5b7e renaming h415 → CurrentAFT.RootUnselectedPhysicalLinear.singletonMass
open _root_.P2M8f8f5b7e renaming h415 → _p2mH415
open _root_.P2M8f8f5b7e renaming h416 → _p2mH416
open _root_.P2M8f8f5b7e renaming h417 → _p2mH417
open _root_.P2M8f8f5b7e renaming h418 → CurrentAFT.RootUnselectedPhysicalLinear.singletonMass_sum
open _root_.P2M8f8f5b7e renaming h418 → _p2mH418
open _root_.P2M8f8f5b7e renaming h419 → _p2mH419
end
open _root_.P2M8f8f5b7e renaming h364 → _p2mH364
open _root_.P2M8f8f5b7e renaming h365 → _p2mH365
open _root_.P2M8f8f5b7e renaming h366 → _p2mH366
open _root_.P2M8f8f5b7e renaming h367 → _p2mH367
open _root_.P2M8f8f5b7e renaming h368 → _p2mH368
namespace CurrentAFT.ActualRootResponse
end CurrentAFT.ActualRootResponse
namespace CurrentAFT.RootSelectedPhysicalColumns.ordinaryNumerator
end CurrentAFT.RootSelectedPhysicalColumns.ordinaryNumerator
namespace CurrentAFT.RootSelectedPhysicalLinear
end CurrentAFT.RootSelectedPhysicalLinear
namespace CurrentAFT.RootUnselectedPhysicalLinear
end CurrentAFT.RootUnselectedPhysicalLinear
namespace CurrentAFT.RootUnselectedPhysicalLinear.covariance_center
end CurrentAFT.RootUnselectedPhysicalLinear.covariance_center
namespace CurrentAFT.RootUnselectedPhysicalLinear.positiveAt
end CurrentAFT.RootUnselectedPhysicalLinear.positiveAt
namespace CurrentAFT.RootUnselectedPhysicalLinear.positiveAt.match_1
end CurrentAFT.RootUnselectedPhysicalLinear.positiveAt.match_1
namespace CurrentAFT.RootUnselectedPhysicalLinear.rawRoot
end CurrentAFT.RootUnselectedPhysicalLinear.rawRoot
namespace CurrentAFT.RootUnselectedPhysicalLinear.singletonMass
end CurrentAFT.RootUnselectedPhysicalLinear.singletonMass
namespace CurrentAFT.RootUnselectedPhysicalLinear.singletonMass_sum
end CurrentAFT.RootUnselectedPhysicalLinear.singletonMass_sum
section
namespace CurrentAFT.ActualRootPhysicalResponse
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  CycleRootExpansion ControlCoordinates GradedControlAlgebra LocalCoefficientFamily
  RootLocalDenominators FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalProdDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootPhysicalResponse.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h395 : (Finset.univ : Finset (Fin 1)).toList = [0] := by
  apply Finset.toList_eq_singleton_iff.mpr
  ext index
  rw [Fin.eq_zero index]
  simp
open _root_.P2M8f8f5b7e renaming h395 → _p2mH395
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h34 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (index : Fin r) :
    _root_.CurrentAFT.PairedRootProjection.projector selection tagged (.inl (.inl index)) =
      _root_.CurrentAFT.RootPrimaryGroupedChannel.projector security (_root_.CurrentAFT.ActualRootGroupedChannel.primaryFlags selection tagged index) := rfl
open _root_.P2M8f8f5b7e renaming h34 → _p2mH34
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h33 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (index : Fin s) :
    _root_.CurrentAFT.PairedRootProjection.projector selection tagged (.inl (.inr index)) =
      _root_.CurrentAFT.RootOrdinaryGroupedChannel.projector security (_root_.CurrentAFT.ActualRootGroupedChannel.ordinaryFlag selection tagged index) := by
  change _root_.CurrentAFT.RootCoordinateProjection.sequence (_root_.CurrentAFT.CycleRootExpansion.rootReference security)
    ((Finset.univ : Finset (Fin 1)).toList.map (fun slot =>
      (slot, decide (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨.inl (.inr index), slot⟩ ∈ tagged)))) = _
  simp only [_p2mH395, List.map_cons, List.map_nil, _root_.CurrentAFT.RootCoordinateProjection.sequence,
    LinearMap.comp_id]
  rfl
open _root_.P2M8f8f5b7e renaming h33 → _p2mH33
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h31 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (index : _root_.CurrentAFT.PairedRootPlacement.HitKept selection tagged) :
    _root_.CurrentAFT.PairedRootProjection.projector selection tagged (.inr index) =
      _root_.CurrentAFT.RootCoordinateProjection.center (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (0 : Fin 1) := by
  change _root_.CurrentAFT.RootCoordinateProjection.sequence (_root_.CurrentAFT.CycleRootExpansion.rootReference security)
    ((Finset.univ : Finset (Fin 1)).toList.map (fun slot =>
      (slot, decide (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨.inr index, slot⟩ ∈ tagged)))) = _
  simp only [_p2mH395, List.map_cons, List.map_nil, _root_.CurrentAFT.RootCoordinateProjection.sequence,
    LinearMap.comp_id]
  have hroot : _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ⟨.inr index, (0 : Fin 1)⟩ = index.val.val := rfl
  rw [hroot]
  simp only [index.property, decide_true, _root_.CurrentAFT.RootCoordinateProjection.coordinate, if_true]
open _root_.P2M8f8f5b7e renaming h31 → _p2mH31
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h32 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged) (score : _root_.CurrentAFT.ActualRootGroupedChannel.Input selection tagged group → ℝ) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection tagged group score) *
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.ActualRootPhysicalResponse.localDenominator queue selection tagged group) =
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.ActualRootPhysicalResponse.projectedPhysical queue selection tagged group score) := by
  rcases group with (primary | ordinary) | kept
  · change _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.RootPrimaryGroupedChannel.channel security order (_root_.CurrentAFT.ActualRootGroupedChannel.primaryFlags selection tagged primary) score) *
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootLocalDenominators.primaryPolynomial security) = _
    simp only [_root_.CurrentAFT.ActualRootPhysicalResponse.projectedPhysical, _root_.CurrentAFT.ActualRootPhysicalResponse.rawPhysical, _root_.CurrentAFT.RootSelectedControlCenter.projector, _p2mH34]
    exact _p2mH345 security order _ score
  · change _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.RootOrdinaryGroupedChannel.channel security order horder (_root_.CurrentAFT.ActualRootGroupedChannel.ordinaryFlag selection tagged ordinary) score) *
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootLocalDenominators.ordinaryPolynomial security) = _
    simp only [_root_.CurrentAFT.ActualRootPhysicalResponse.projectedPhysical, _root_.CurrentAFT.ActualRootPhysicalResponse.rawPhysical, _root_.CurrentAFT.RootSelectedControlCenter.projector, _p2mH33]
    exact _p2mH344 security order horder _ score
  · change _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.RootUnselectedGrouped.channel security order horder queue kept.val.val score) *
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue kept.val.val) = _
    simp only [_root_.CurrentAFT.ActualRootPhysicalResponse.projectedPhysical, _root_.CurrentAFT.ActualRootPhysicalResponse.rawPhysical, _root_.CurrentAFT.RootSelectedControlCenter.projector, _p2mH31,
      LinearMap.id_comp]
    exact _p2mH364 security order horder queue kept.val.val score
open _root_.P2M8f8f5b7e renaming h32 → _p2mH32
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h36 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.ActualRootPhysicalResponse.projectedPhysical queue selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) =
      _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.ActualRootPhysicalResponse.rawPhysical queue selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) := by
  change _root_.CurrentAFT.FinitePolynomialTensor.synthesis (fun group =>
    ((_root_.CurrentAFT.ActualRootPhysicalResponse.rawPhysical queue selection tagged group).comp (_root_.CurrentAFT.RootSelectedControlCenter.projector selection tagged group)).comp
      (_root_.CurrentAFT.PairedRootProjection.projector selection tagged group)) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) = _
  rw [_p2mH119, _p2mH203,
    _p2mH119, _p2mH338]
open _root_.P2M8f8f5b7e renaming h36 → _p2mH36
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h35 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout kernel) *
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (∏ group, _root_.CurrentAFT.ActualRootPhysicalResponse.localDenominator queue selection tagged group) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.ActualRootPhysicalResponse.rawPhysical queue selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel)) := by
  have hresponse : _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout kernel) =
      _root_.CurrentAFT.FinitePolynomialTensor.synthesis (fun group => (_root_.CurrentAFT.BackgroundEvaluation.evaluation security order).toLinearMap.comp
        (_root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection tagged group))
          (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) := by
    rw [_p2mH37, _root_.CurrentAFT.GroupedFamilyIdentity.response_eq]
    simp only [map_sum, map_smul, map_prod, _root_.CurrentAFT.FinitePolynomialTensor.synthesis, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [hresponse, map_prod]
  rw [_p2mH120
    (fun group => (_root_.CurrentAFT.BackgroundEvaluation.evaluation security order).toLinearMap.comp
      (_root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection tagged group))
    (fun group => (_root_.CurrentAFT.TruncatedOutput.quotientMap order).toLinearMap.comp (_root_.CurrentAFT.ActualRootPhysicalResponse.projectedPhysical queue selection tagged group))
    (fun group => _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.ActualRootPhysicalResponse.localDenominator queue selection tagged group))
    (fun group source => by
      simpa only [LinearMap.comp_apply, AlgHom.toLinearMap_apply] using
        _p2mH32 order horder queue selection tagged group (Pi.single source 1))]
  rw [← _p2mH118, _p2mH36]
open _root_.P2M8f8f5b7e renaming h35 → _p2mH35
end
open _root_.P2M8f8f5b7e renaming h31 → _p2mH31
open _root_.P2M8f8f5b7e renaming h32 → _p2mH32
open _root_.P2M8f8f5b7e renaming h33 → _p2mH33
open _root_.P2M8f8f5b7e renaming h34 → _p2mH34
open _root_.P2M8f8f5b7e renaming h35 → _p2mH35
open _root_.P2M8f8f5b7e renaming h36 → _p2mH36
open _root_.P2M8f8f5b7e renaming h395 → _p2mH395
end CurrentAFT.ActualRootPhysicalResponse
open _root_.P2M8f8f5b7e renaming h31 → _p2mH31
open _root_.P2M8f8f5b7e renaming h32 → _p2mH32
open _root_.P2M8f8f5b7e renaming h33 → _p2mH33
open _root_.P2M8f8f5b7e renaming h34 → _p2mH34
open _root_.P2M8f8f5b7e renaming h35 → _p2mH35
open _root_.P2M8f8f5b7e renaming h36 → _p2mH36
open _root_.P2M8f8f5b7e renaming h395 → _p2mH395
end
open _root_.P2M8f8f5b7e renaming h31 → _p2mH31
open _root_.P2M8f8f5b7e renaming h32 → _p2mH32
open _root_.P2M8f8f5b7e renaming h33 → _p2mH33
open _root_.P2M8f8f5b7e renaming h34 → _p2mH34
open _root_.P2M8f8f5b7e renaming h35 → _p2mH35
open _root_.P2M8f8f5b7e renaming h36 → _p2mH36
section
namespace CurrentAFT.RootPolynomialTensor
open AFT FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootPolynomialTensor.classicalProdDecidableEq
variable {Index : Type*} [Fintype Index] [DecidableEq Index]
  {RootData Control : Index → Type*} [∀ index, Fintype (RootData index)] [∀ index, Fintype (Control index)]
  {Value : Type*} [CommRing Value] [Algebra ℝ Value]
set_option maxRecDepth 8192
omit [Fintype Index] [DecidableEq Index] [∀ index, Fintype (Control index)] in
theorem _root_.P2M8f8f5b7e.h334 (reference : ∀ index, _root_.AFT.FiniteDist (RootData index))
    (physical : ∀ index, RootData index → (Control index → ℝ) →ₗ[ℝ] Value)
    (index : Index) (point : RootData index × Control index) :
    _root_.CurrentAFT.RootPolynomialTensor.averagedChannel reference physical index (Pi.single point 1) =
      (reference index).weight point.1 • physical index point.1 (Pi.single point.2 1) := by
  classical
  rcases point with ⟨pointRoot, pointControl⟩
  simp only [_root_.CurrentAFT.RootPolynomialTensor.averagedChannel, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    _root_.CurrentAFT.RootPolynomialTensor.sliceLinear, LinearMap.coe_mk, AddHom.coe_mk]
  change (∑ root, (reference index).weight root • physical index root
    (fun control => (Pi.single (pointRoot, pointControl) (1 : ℝ) : RootData index × Control index → ℝ) (root, control))) = _
  rw [Finset.sum_eq_single pointRoot]
  · congr 1
    congr 1
    funext control
    simp [Pi.single_apply]
  · intro root _ hne
    have hzero : (fun control => (Pi.single (pointRoot, pointControl) (1 : ℝ) : RootData index × Control index → ℝ) (root, control)) = 0 := by
      funext control
      simp [hne]
    rw [hzero, map_zero, smul_zero]
  · simp
open _root_.P2M8f8f5b7e renaming h334 → _p2mH334
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h335
    (reference : ∀ index, _root_.AFT.FiniteDist (RootData index))
    (physical : ∀ index, RootData index → (Control index → ℝ) →ₗ[ℝ] Value)
    (input : ((index : Index) → RootData index × Control index) → ℝ) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.RootPolynomialTensor.averagedChannel reference physical) input =
      ∑ roots : (index : Index) → RootData index, (∏ index, (reference index).weight (roots index)) •
        _root_.CurrentAFT.FinitePolynomialTensor.synthesis (fun index => physical index (roots index)) (fun controls => input (fun index => (roots index, controls index))) := by
  unfold _root_.CurrentAFT.FinitePolynomialTensor.synthesis
  simp only [_p2mH334, Finset.prod_smul, smul_smul, Finset.smul_sum]
  rw [← Fintype.sum_prod_type (f := fun pair : ((index : Index) → RootData index) × ((index : Index) → Control index) =>
    ((∏ index, (reference index).weight (pair.1 index)) * input (fun index => (pair.1 index, pair.2 index))) •
      ∏ index, physical index (pair.1 index) (Pi.single (pair.2 index) 1))]
  rw [← (_root_.CurrentAFT.RootPolynomialTensor.sourceEquiv (RootData := RootData) (Control := Control)).sum_comp]
  apply Finset.sum_congr rfl
  intro source _
  simp only [_root_.CurrentAFT.RootPolynomialTensor.sourceEquiv, Equiv.coe_fn_mk]
  rw [mul_comm]
open _root_.P2M8f8f5b7e renaming h335 → _p2mH335
end
open _root_.P2M8f8f5b7e renaming h334 → _p2mH334
open _root_.P2M8f8f5b7e renaming h335 → _p2mH335
end CurrentAFT.RootPolynomialTensor
open _root_.P2M8f8f5b7e renaming h334 → _p2mH334
open _root_.P2M8f8f5b7e renaming h335 → _p2mH335
end
open _root_.P2M8f8f5b7e renaming h334 → _p2mH334
open _root_.P2M8f8f5b7e renaming h335 → _p2mH335
namespace CurrentAFT.RootPolynomialTensor
end CurrentAFT.RootPolynomialTensor
namespace CurrentAFT.RootPolynomialTensor.averagedChannel
end CurrentAFT.RootPolynomialTensor.averagedChannel
namespace CurrentAFT.RootPolynomialTensor.sliceLinear
end CurrentAFT.RootPolynomialTensor.sliceLinear
namespace CurrentAFT.RootPolynomialTensor.sourceEquiv
end CurrentAFT.RootPolynomialTensor.sourceEquiv
section
namespace CurrentAFT.RootPhysicalAverages
open AFT AFT.RepresentedPolynomial DiffuseProfiles ProposalPrimary ActualControls FirstHistogram
  LocalReferenceEnergy PairedReferenceEnergy FixedPairedFirst PhysicalSynthesis
  RootTaggedSelected RootSelectedPhysicalLinear RootSelectedPhysicalColumns
  CycleRootExpansion TaggedPhysicalFock OrdinaryPhysicalFock
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootPhysicalAverages.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootPhysicalAverages.safeDecidableEq
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base ProposalPrimary.primaryLaw rootReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h330 (security : ℕ) :
    _root_.CurrentAFT.RootSelectedPhysicalLinear.primaryRaw security = _root_.CurrentAFT.RootPolynomialTensor.averagedChannel
      (Index := Unit) (fun _ => _root_.AFT.FiniteDist.independent (fun _ : Fin 2 => _root_.CurrentAFT.CycleRootExpansion.rootReference security))
      (fun _ => _root_.CurrentAFT.RootPhysicalAverages.primaryAt security) () := by
  apply LinearMap.ext
  intro score
  change _root_.CurrentAFT.RootSelectedPhysicalColumns.primaryNumerator security
    (_root_.CurrentAFT.RootTaggedSelectedChannel.curryLinear security (_root_.CurrentAFT.RootPrimaryGroupedChannel.pairLinear security score)) = _
  rw [← _root_.CurrentAFT.RootSelectedPhysicalColumns.primaryNumerator_eq]
  have hmass : _root_.CurrentAFT.RootTaggedSelected.mass security (_root_.CurrentAFT.RootTaggedSelectedChannel.curryLinear security (_root_.CurrentAFT.RootPrimaryGroupedChannel.pairLinear security score)) =
      ∑ sample : _root_.CurrentAFT.RootTaggedSelected.Sample security, (_root_.CurrentAFT.RootTaggedSelected.sourceLaw security).weight sample •
        _root_.CurrentAFT.PairedReferenceEnergy.pairedMassAt security (sample.1.1.val : ℤ) (sample.1.2.val : ℤ) sample.2
          (fun color => score ((_root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv security).symm sample.1, color)) := by
    funext word
    simp only [_root_.CurrentAFT.RootTaggedSelected.mass_eq_joint, _root_.CurrentAFT.PairedReferenceEnergy.jointPairedMass, _root_.CurrentAFT.RootTaggedSelectedChannel.curryLinear,
      _root_.CurrentAFT.RootPrimaryGroupedChannel.pairLinear, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmass, map_sum]
  simp only [map_smul, _root_.CurrentAFT.RootPolynomialTensor.averagedChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, _root_.CurrentAFT.RootPolynomialTensor.sliceLinear, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.CurrentAFT.RootPhysicalAverages.primaryAt, _p2mH381, map_sum, map_smul]
  conv_rhs => rw [← (_root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv security).symm.sum_comp]
  simp only [_root_.CurrentAFT.RootTaggedSelected.sourceLaw, _root_.CurrentAFT.RootTaggedSelected.rootsLaw, Fintype.sum_prod_type, _root_.AFT.FiniteDist.prod_weight, _root_.AFT.FiniteDist.independent,
    Fin.prod_univ_two, _root_.CurrentAFT.RootPrimaryGroupedChannel.pairEquiv, finTwoArrowEquiv,
    Equiv.coe_fn_symm_mk, Matrix.cons_val_zero, Matrix.cons_val_one,
    Finset.smul_sum, smul_smul]
open _root_.P2M8f8f5b7e renaming h330 → _p2mH330
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h327 {Color : Type*} [Fintype Color] (reference profile : Color → ℝ) :
    _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear reference (fun word : Fin 1 → Color => profile (word 0)) = _root_.AFT.RepresentedPolynomial.singleGenerating reference profile := by
  unfold _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Fin.prod_univ_one]
  rw [← (Equiv.funUnique (Fin 1) Color).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply, uniqueElim_const, MvPolynomial.smul_eq_C_mul, _root_.AFT.RepresentedPolynomial.singleGenerating]
open _root_.P2M8f8f5b7e renaming h327 → _p2mH327
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h331 (security : ℕ) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.BodyChannelEvaluation.safeMass security score = _root_.CurrentAFT.OrdinaryPhysicalFock.profile security score := by
  have h := _p2mH68 security (_root_.CurrentAFT.OrdinaryPhysicalFock.extendDensity security score)
  unfold _root_.CurrentAFT.OrdinaryPhysicalFock.profile
  simpa only [_p2mH180] using h
open _root_.P2M8f8f5b7e renaming h331 → _p2mH331
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h328 (security : ℕ) (roots : Fin 1 → _root_.CurrentAFT.CycleRootExpansion.Root security) (score : _root_.CurrentAFT.ActualControls.SafePalette security → ℝ) :
    _root_.CurrentAFT.RootPhysicalAverages.ordinaryAt security roots score = _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
      (_root_.CurrentAFT.SelectedOrdinaryRoot.pushLinear (_root_.CurrentAFT.ActualControls.bodyReference security) (_root_.CurrentAFT.SelectedOrdinaryRoot.rootEmbedding security (roots 0)) score) := by
  change _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
    (fun word : Fin 1 → _root_.CurrentAFT.RootPhysicalAverages.Palette security => _root_.CurrentAFT.OrdinaryPhysicalFock.translatedProfile security ((roots 0).val : ℤ) score (word 0)) = _
  rw [_p2mH327]
  congr 1
  funext color
  rw [_p2mH373, _p2mH331]
  rfl
open _root_.P2M8f8f5b7e renaming h328 → _p2mH328
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h329 (security : ℕ) :
    _root_.CurrentAFT.RootSelectedPhysicalLinear.ordinaryRaw security = _root_.CurrentAFT.RootPolynomialTensor.averagedChannel
      (Index := Unit) (fun _ => _root_.AFT.FiniteDist.independent (fun _ : Fin 1 => _root_.CurrentAFT.CycleRootExpansion.rootReference security))
      (fun _ => _root_.CurrentAFT.RootPhysicalAverages.ordinaryAt security) () := by
  apply LinearMap.ext
  intro score
  change _root_.CurrentAFT.RootSelectedPhysicalColumns.ordinaryNumerator security (_root_.CurrentAFT.RootOrdinaryGroupedChannel.toRaw security score) = _
  simp only [_root_.CurrentAFT.RootPolynomialTensor.averagedChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, _root_.CurrentAFT.RootPolynomialTensor.sliceLinear, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [_p2mH328, _p2mH343]
  rw [← (Equiv.funUnique (Fin 1) (_root_.CurrentAFT.CycleRootExpansion.Root security)).symm.sum_comp]
  simp only [_root_.AFT.FiniteDist.independent, Fin.prod_univ_one, Equiv.funUnique_symm_apply, uniqueElim_const]
  rfl
open _root_.P2M8f8f5b7e renaming h329 → _p2mH329
end
open _root_.P2M8f8f5b7e renaming h327 → _p2mH327
open _root_.P2M8f8f5b7e renaming h328 → _p2mH328
open _root_.P2M8f8f5b7e renaming h329 → _p2mH329
open _root_.P2M8f8f5b7e renaming h330 → _p2mH330
open _root_.P2M8f8f5b7e renaming h331 → _p2mH331
end CurrentAFT.RootPhysicalAverages
open _root_.P2M8f8f5b7e renaming h327 → _p2mH327
open _root_.P2M8f8f5b7e renaming h328 → _p2mH328
open _root_.P2M8f8f5b7e renaming h329 → _p2mH329
open _root_.P2M8f8f5b7e renaming h330 → _p2mH330
open _root_.P2M8f8f5b7e renaming h331 → _p2mH331
end
open _root_.P2M8f8f5b7e renaming h327 → _p2mH327
open _root_.P2M8f8f5b7e renaming h328 → _p2mH328
open _root_.P2M8f8f5b7e renaming h329 → _p2mH329
open _root_.P2M8f8f5b7e renaming h330 → _p2mH330
open _root_.P2M8f8f5b7e renaming h331 → _p2mH331
section
namespace CurrentAFT.RootPolynomialPlacement
open AFT CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootPolynomialPlacement.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootPolynomialPlacement.classicalSubtypeDecidableEq
variable {Selected Pool Color Value : Type*} [Fintype Selected] [Fintype Pool] [Fintype Color]
  [CommRing Value] [Algebra ℝ Value]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h332 (law : Pool → _root_.AFT.FiniteDist Color) (physical : Pool → Color → Value) :
    _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent law) (fun word => ∏ index, physical index (word index)) =
      ∏ index, _root_.CurrentAFT.CycleRootExpansion.expectationLinear (law index) (physical index) := by
  simp only [_root_.CurrentAFT.CycleRootExpansion.expectationLinear, LinearMap.coe_mk, AddHom.coe_mk, _root_.AFT.FiniteDist.independent]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro word _
  rw [Finset.prod_smul]
open _root_.P2M8f8f5b7e renaming h332 → _p2mH332
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h333 (embedding : Selected ↪ Pool) (law : Pool → _root_.AFT.FiniteDist Color)
    (score : (Selected → Color) → Value) (physical : Pool → Color → Value) :
    _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent law)
      (fun word => score (word ∘ embedding) * ∏ index, physical index (word index)) =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent (fun index => law (embedding index)))
        (fun word => score word * ∏ index, physical (embedding index) (word index)) *
      ∏ index : {index : Pool // index ∉ Finset.univ.map embedding},
        _root_.CurrentAFT.CycleRootExpansion.expectationLinear (law index.val) (physical index.val) := by
  let partition := _root_.AFT.FiniteDist.placementPartition embedding
  let wordEquiv : ((Selected → Color) × ({index : Pool // index ∉ Finset.univ.map embedding} → Color)) ≃
      (Pool → Color) :=
    (Equiv.sumArrowEquivProdArrow Selected {index : Pool // index ∉ Finset.univ.map embedding} Color).symm.trans
      (Equiv.piCongrLeft (fun _ : Pool => Color) partition)
  have heval (word : (Selected → Color) × ({index : Pool // index ∉ Finset.univ.map embedding} → Color))
      (index : Selected ⊕ {index : Pool // index ∉ Finset.univ.map embedding}) :
      wordEquiv word (partition index) = Sum.elim word.1 word.2 index := by
    exact Equiv.piCongrLeft_apply_apply (fun _ : Pool => Color) partition _ index
  have hselected (word : (Selected → Color) × ({index : Pool // index ∉ Finset.univ.map embedding} → Color)) :
      wordEquiv word ∘ embedding = word.1 := by
    funext index
    exact heval word (.inl index)
  rw [← _p2mH332 (fun index : {index : Pool // index ∉ Finset.univ.map embedding} => law index.val)
    (fun index => physical index.val)]
  simp only [_root_.CurrentAFT.CycleRootExpansion.expectationLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← wordEquiv.sum_comp, Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro selected _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro rest _
  rw [hselected]
  change ((∏ index, (law index).weight (wordEquiv (selected, rest) index)) •
    (score selected * ∏ index, physical index (wordEquiv (selected, rest) index))) = _
  rw [← partition.prod_comp (fun index => (law index).weight (wordEquiv (selected, rest) index)),
    ← partition.prod_comp (fun index => physical index (wordEquiv (selected, rest) index))]
  simp only [heval, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, _root_.AFT.FiniteDist.independent]
  simp only [partition, _root_.AFT.FiniteDist.placementPartition_inl, _root_.AFT.FiniteDist.placementPartition_inr]
  simp only [Algebra.smul_def, map_mul]
  ring
open _root_.P2M8f8f5b7e renaming h333 → _p2mH333
end
open _root_.P2M8f8f5b7e renaming h332 → _p2mH332
open _root_.P2M8f8f5b7e renaming h333 → _p2mH333
end CurrentAFT.RootPolynomialPlacement
open _root_.P2M8f8f5b7e renaming h332 → _p2mH332
open _root_.P2M8f8f5b7e renaming h333 → _p2mH333
end
open _root_.P2M8f8f5b7e renaming h332 → _p2mH332
open _root_.P2M8f8f5b7e renaming h333 → _p2mH333
section
namespace CurrentAFT.RootBackgroundDenominatorProduct
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedOutputPlacement
  RootLocalDenominators RootUnselectedBlockChannel BackgroundPolynomialEvaluation
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h246 (security : ℕ) (queue : ℤ) :
    _root_.CurrentAFT.RootTaggedLocal.meanLaw security .queue queue = _root_.CurrentAFT.BackgroundPolynomialEvaluation.queueLaw security queue := by
  unfold _root_.CurrentAFT.RootTaggedLocal.meanLaw _root_.CurrentAFT.RootTaggedLocal.shiftedLaw _root_.CurrentAFT.UniformBodyProfiles.preRootLaw _root_.CurrentAFT.BackgroundPolynomialEvaluation.queueLaw
  exact _p2mH276 security _
open _root_.P2M8f8f5b7e renaming h246 → _p2mH246
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h244 (security : ℕ) (queue : ℤ) :
    (∏ block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security, _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue block) = _root_.CurrentAFT.BackgroundPolynomialEvaluation.fixedQueueGenerating security queue := by
  simp only [_root_.CurrentAFT.ActualBlockFock.BlockIndex, Fintype.prod_sum_type, _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial, _p2mH317, _p2mH246,
    _root_.CurrentAFT.RootLocalDenominators.uniformReference_eq, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold _root_.CurrentAFT.BackgroundPolynomialEvaluation.fixedQueueGenerating
  change _root_.CurrentAFT.LegPolynomialEvaluation.legGenerating security ^ _root_.CurrentAFT.Parameters.legCount security *
    (_root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.FringeCertificate.uniformProfile security)
      (_root_.CurrentAFT.BackgroundCertificates.convolvedCenterLaw security).weight ^ _root_.CurrentAFT.BackgroundPopulationBounds.freeCount security * _) = _
  ring
open _root_.P2M8f8f5b7e renaming h244 → _p2mH244
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h247 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) :
    (∏ _index : Fin r, _root_.CurrentAFT.RootLocalDenominators.primaryPolynomial security) * (∏ _index : Fin s, _root_.CurrentAFT.RootLocalDenominators.ordinaryPolynomial security) *
      (∏ index : selection.kept, _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue index.val) =
      ∏ block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security, _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue block := by
  have hsplit := Equiv.prod_comp (_root_.CurrentAFT.PairedOutputPlacement.blockEquiv selection) (_root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue)
  rw [← hsplit]
  simp only [Fintype.prod_sum_type, _root_.CurrentAFT.PairedOutputPlacement.blockEquiv_removed, _root_.CurrentAFT.PairedOutputPlacement.blockEquiv_kept,
    _root_.CurrentAFT.TaggedSelection.RemovedLabel, _root_.CurrentAFT.TaggedSelection.Selection.removedEmbedding, Function.Embedding.coeFn_mk]
  have hcenter (index : Fin (_root_.CurrentAFT.ActualBlockFock.centerCount security)) :
      _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue (.inr (.inl index)) = _root_.CurrentAFT.RootLocalDenominators.ordinaryPolynomial security :=
    (_p2mH319 security queue index).symm
  simp_rw [hcenter]
  simp only [_root_.CurrentAFT.RootLocalDenominators.primaryPolynomial, _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial, Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
  ac_rfl
open _root_.P2M8f8f5b7e renaming h247 → _p2mH247
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h245 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) :
    (∏ group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection tagged, _root_.CurrentAFT.RootBackgroundDenominatorProduct.denominator queue selection tagged group) *
      (∏ index : _root_.CurrentAFT.RootBackgroundDenominatorProduct.InactiveKept selection tagged, _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue index.val.val) =
      _root_.CurrentAFT.BackgroundPolynomialEvaluation.fixedQueueGenerating security queue := by
  have hkept := Fintype.prod_subtype_mul_prod_subtype (fun index : selection.kept => index.val ∈ tagged)
    (fun index : selection.kept => _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue index.val)
  change (∏ index : _root_.CurrentAFT.PairedRootPlacement.HitKept selection tagged, _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue index.val.val) *
    (∏ index : _root_.CurrentAFT.RootBackgroundDenominatorProduct.InactiveKept selection tagged, _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue index.val.val) =
      ∏ index : selection.kept, _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue index.val at hkept
  simp only [Fintype.prod_sum_type, _root_.CurrentAFT.RootBackgroundDenominatorProduct.denominator]
  rw [mul_assoc, hkept, _p2mH247, _p2mH244]
open _root_.P2M8f8f5b7e renaming h245 → _p2mH245
end
open _root_.P2M8f8f5b7e renaming h244 → _p2mH244
open _root_.P2M8f8f5b7e renaming h245 → _p2mH245
open _root_.P2M8f8f5b7e renaming h246 → _p2mH246
open _root_.P2M8f8f5b7e renaming h247 → _p2mH247
end CurrentAFT.RootBackgroundDenominatorProduct
open _root_.P2M8f8f5b7e renaming h244 → _p2mH244
open _root_.P2M8f8f5b7e renaming h245 → _p2mH245
open _root_.P2M8f8f5b7e renaming h246 → _p2mH246
open _root_.P2M8f8f5b7e renaming h247 → _p2mH247
end
open _root_.P2M8f8f5b7e renaming h244 → _p2mH244
open _root_.P2M8f8f5b7e renaming h245 → _p2mH245
open _root_.P2M8f8f5b7e renaming h246 → _p2mH246
open _root_.P2M8f8f5b7e renaming h247 → _p2mH247
section
namespace CurrentAFT.RootBlockReindex
open AFT ActualBlockFock TaggedSelection PairedRootPlacement PairedRootInput
  PairedRootCentering CycleRootExpansion
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootBlockReindex.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootBlockReindex.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootBlockReindex.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h250 {Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (test : (_root_.CurrentAFT.ActualBlockFock.BlockIndex security → _root_.CurrentAFT.CycleRootExpansion.Root security) → Value) :
    _root_.CurrentAFT.CycleRootExpansion.actualComponent security (tagged.map layout.toEmbedding) (fun roots => test (roots ∘ layout)) =
      ∑ roots, ((_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.ActualBlockFock.BlockIndex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security)).weight roots *
        _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout (roots ∘ _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged)) • test roots := by
  rw [_p2mH199]
  rw [← (Equiv.piCongrLeft (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security => _root_.CurrentAFT.CycleRootExpansion.Root security) layout).sum_comp]
  apply Finset.sum_congr rfl
  intro roots _
  have hreindex : (Equiv.piCongrLeft (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security => _root_.CurrentAFT.CycleRootExpansion.Root security) layout roots) ∘ layout = roots := by
    funext block
    exact Equiv.piCongrLeft_apply_apply (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security => _root_.CurrentAFT.CycleRootExpansion.Root security) layout roots block
  have hweight : (_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security)).weight
      (Equiv.piCongrLeft (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security => _root_.CurrentAFT.CycleRootExpansion.Root security) layout roots) =
      (_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.ActualBlockFock.BlockIndex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security)).weight roots := by
    simp only [_root_.AFT.FiniteDist.independent]
    rw [← Equiv.prod_comp layout]
    simp only [Equiv.piCongrLeft_apply_apply]
  rw [hweight, hreindex]
  congr 2
  unfold _root_.CurrentAFT.PairedRootCentering.rootDensity
  congr 1
  funext index
  simp only [Function.comp_apply, _p2mH200 selection tagged layout, Equiv.piCongrLeft_apply_apply]
open _root_.P2M8f8f5b7e renaming h250 → _p2mH250
end
open _root_.P2M8f8f5b7e renaming h250 → _p2mH250
end CurrentAFT.RootBlockReindex
open _root_.P2M8f8f5b7e renaming h250 → _p2mH250
end
open _root_.P2M8f8f5b7e renaming h250 → _p2mH250
namespace CurrentAFT.ActualRootPhysicalResponse
end CurrentAFT.ActualRootPhysicalResponse
namespace CurrentAFT.ActualRootPhysicalResponse.localDenominator
end CurrentAFT.ActualRootPhysicalResponse.localDenominator
namespace CurrentAFT.ActualRootPhysicalResponse.localDenominator.match_1
end CurrentAFT.ActualRootPhysicalResponse.localDenominator.match_1
namespace CurrentAFT.ActualRootPhysicalResponse.projectedPhysical
end CurrentAFT.ActualRootPhysicalResponse.projectedPhysical
namespace CurrentAFT.ActualRootPhysicalResponse.rawPhysical
end CurrentAFT.ActualRootPhysicalResponse.rawPhysical
namespace CurrentAFT.RootBlockReindex
end CurrentAFT.RootBlockReindex
namespace CurrentAFT.RootInactivePlacement
end CurrentAFT.RootInactivePlacement
namespace CurrentAFT.RootOrdinaryGroupedChannel.channel
end CurrentAFT.RootOrdinaryGroupedChannel.channel
namespace CurrentAFT.RootPhysicalAverages
end CurrentAFT.RootPhysicalAverages
namespace CurrentAFT.RootPhysicalAverages.primaryAt
end CurrentAFT.RootPhysicalAverages.primaryAt
namespace CurrentAFT.RootPolynomialPlacement
end CurrentAFT.RootPolynomialPlacement
namespace CurrentAFT.RootSelectedControlCenter.projector.match_1
end CurrentAFT.RootSelectedControlCenter.projector.match_1
namespace CurrentAFT.RootUnselectedGrouped.channel
end CurrentAFT.RootUnselectedGrouped.channel
section
namespace CurrentAFT.RootTaggedPhysicalFactorization
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection PairedRootPlacement
  PairedRootInput PairedRootCentering CycleRootExpansion ControlCoordinates
  RaisingPatternBudget FinitePolynomialTensor ActualRootPhysicalResponse
  LocalReferenceEnergy
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootTaggedPhysicalFactorization.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootTaggedPhysicalFactorization.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootTaggedPhysicalFactorization.classicalProdDecidableEq
attribute [local instance] _root_.CurrentAFT.RootTaggedPhysicalFactorization.classicalSubtypeDecidableEq
attribute [local instance] _root_.CurrentAFT.RootTaggedPhysicalFactorization.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount ProposalPrimary.primaryLaw
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h356 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) :
    _root_.CurrentAFT.ActualRootPhysicalResponse.rawPhysical queue selection tagged = _root_.CurrentAFT.RootPolynomialTensor.averagedChannel
      (_root_.CurrentAFT.RootTaggedPhysicalFactorization.rootReferenceByGroup selection tagged) (_root_.CurrentAFT.RootTaggedPhysicalFactorization.fixedPhysical queue selection tagged) := by
  funext group
  rcases group with (primary | ordinary) | kept
  · exact _p2mH330 security
  · exact _p2mH329 security
  · apply LinearMap.ext
    intro score
    simp only [_root_.CurrentAFT.ActualRootPhysicalResponse.rawPhysical, _root_.CurrentAFT.RootUnselectedPhysicalLinear.raw, _root_.CurrentAFT.RootUnselectedPhysicalLinear.rawRoot,
      _root_.CurrentAFT.RootUnselectedGrouped.extractLinear, _root_.CurrentAFT.RootUnselectedGrouped.inputEquiv,
      _root_.CurrentAFT.RootPolynomialTensor.averagedChannel, _root_.CurrentAFT.RootTaggedPhysicalFactorization.rootReferenceByGroup, _root_.CurrentAFT.RootTaggedPhysicalFactorization.fixedPhysical, _root_.CurrentAFT.RootTaggedPhysicalFactorization.unitPolynomial,
      LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, _root_.CurrentAFT.RootPolynomialTensor.sliceLinear,
      LinearMap.coe_mk, AddHom.coe_mk, Equiv.coe_fn_symm_mk]
    change (∑ root : _root_.CurrentAFT.CycleRootExpansion.Root security, ((_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root * score ((fun _ => root), ())) •
      _root_.CurrentAFT.RootUnselectedPhysicalLinear.positiveAt security queue kept.val.val root) =
      ∑ roots : Fin 1 → _root_.CurrentAFT.CycleRootExpansion.Root security,
        (_root_.AFT.FiniteDist.independent (fun _ : Fin 1 => _root_.CurrentAFT.CycleRootExpansion.rootReference security)).weight roots •
          score (roots, ()) • _root_.CurrentAFT.RootUnselectedPhysicalLinear.positiveAt security queue kept.val.val (roots 0)
    conv_rhs => rw [← (Equiv.funUnique (Fin 1) (_root_.CurrentAFT.CycleRootExpansion.Root security)).symm.sum_comp
      (fun roots : Fin 1 → _root_.CurrentAFT.CycleRootExpansion.Root security =>
        (_root_.AFT.FiniteDist.independent (fun _ : Fin 1 => _root_.CurrentAFT.CycleRootExpansion.rootReference security)).weight roots •
          score (roots, ()) • _root_.CurrentAFT.RootUnselectedPhysicalLinear.positiveAt security queue kept.val.val (roots 0))]
    simp only [_root_.AFT.FiniteDist.independent, Fin.prod_univ_one, Equiv.funUnique_symm_apply,
      uniqueElim_const, smul_smul]
    apply Finset.sum_congr rfl
    intro root _
    have hconstant : (uniqueElim root : Fin 1 → _root_.CurrentAFT.CycleRootExpansion.Root security) = fun _ => root :=
      funext (uniqueElim_const root)
    rw [hconstant]
    rfl
open _root_.P2M8f8f5b7e renaming h356 → _p2mH356
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h355 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (roots : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) → _root_.CurrentAFT.CycleRootExpansion.Root security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis (fun group => _root_.CurrentAFT.RootTaggedPhysicalFactorization.fixedPhysical queue selection tagged group (fun slot => roots ⟨group, slot⟩))
      (_root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel) =
      _root_.CurrentAFT.RootTaggedPhysicalFactorization.selectedPolynomial queue selection tagged roots kernel * _root_.CurrentAFT.RootTaggedPhysicalFactorization.hitPolynomial queue selection tagged roots := by
  unfold _root_.CurrentAFT.RootTaggedPhysicalFactorization.selectedPolynomial _root_.CurrentAFT.RootTaggedPhysicalFactorization.hitPolynomial _root_.CurrentAFT.FinitePolynomialTensor.synthesis _root_.CurrentAFT.PairedRootInput.controlKernel
  rw [← (Equiv.prodPiEquivSumPi (_root_.CurrentAFT.RaisingPatternBudget.RoleInput security r s)
    (fun _ : _root_.CurrentAFT.PairedRootPlacement.HitKept selection tagged => Unit)).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_sum_type, _root_.CurrentAFT.PairedRootInput.ControlInput,
    Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Sum.elim_inr, _root_.CurrentAFT.RootTaggedPhysicalFactorization.fixedPhysical, _root_.CurrentAFT.RootTaggedPhysicalFactorization.unitPolynomial,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.single_eq_same, one_smul, Fintype.sum_unique]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro controls _
  rw [smul_mul_assoc]
open _root_.P2M8f8f5b7e renaming h355 → _p2mH355
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h357 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.ActualRootPhysicalResponse.rawPhysical queue selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear
        (_root_.AFT.FiniteDist.independent (fun _ : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) => _root_.CurrentAFT.CycleRootExpansion.rootReference security))
        (fun roots => _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout roots •
          (_root_.CurrentAFT.RootTaggedPhysicalFactorization.selectedPolynomial queue selection tagged roots kernel * _root_.CurrentAFT.RootTaggedPhysicalFactorization.hitPolynomial queue selection tagged roots)) := by
  rw [_p2mH356, _p2mH335]
  rw [← (Equiv.piCurry (fun group (_ : _root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged group) => _root_.CurrentAFT.CycleRootExpansion.Root security)).sum_comp]
  change (∑ roots : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) → _root_.CurrentAFT.CycleRootExpansion.Root security,
    (∏ group, (_root_.CurrentAFT.RootTaggedPhysicalFactorization.rootReferenceByGroup selection tagged group).weight (fun slot => roots ⟨group, slot⟩)) •
      _root_.CurrentAFT.FinitePolynomialTensor.synthesis (fun group => _root_.CurrentAFT.RootTaggedPhysicalFactorization.fixedPhysical queue selection tagged group (fun slot => roots ⟨group, slot⟩))
        (fun controls => _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel (fun group => ((fun slot => roots ⟨group, slot⟩), controls group)))) = _
  have hinput (roots : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) → _root_.CurrentAFT.CycleRootExpansion.Root security) :
      (fun controls => _root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel (fun group => ((fun slot => roots ⟨group, slot⟩), controls group))) =
        _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout roots • _root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel := rfl
  simp_rw [hinput]
  unfold _root_.CurrentAFT.CycleRootExpansion.expectationLinear
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  apply Finset.sum_congr rfl
  intro roots _
  have hscale := (_root_.CurrentAFT.FinitePolynomialTensor.synthesisLinear
    (fun group => _root_.CurrentAFT.RootTaggedPhysicalFactorization.fixedPhysical queue selection tagged group (fun slot => roots ⟨group, slot⟩))).map_smul
      (_root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout roots) (_root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel)
  change _root_.CurrentAFT.FinitePolynomialTensor.synthesis _ (_root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout roots • _root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel) =
    _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout roots • _root_.CurrentAFT.FinitePolynomialTensor.synthesis _ (_root_.CurrentAFT.PairedRootInput.controlKernel selection tagged kernel) at hscale
  rw [hscale, _p2mH355]
  congr 1
  simp only [_root_.CurrentAFT.RootTaggedPhysicalFactorization.rootReferenceByGroup, _root_.AFT.FiniteDist.independent, Fintype.prod_sigma]
open _root_.P2M8f8f5b7e renaming h357 → _p2mH357
end
open _root_.P2M8f8f5b7e renaming h355 → _p2mH355
open _root_.P2M8f8f5b7e renaming h356 → _p2mH356
open _root_.P2M8f8f5b7e renaming h357 → _p2mH357
end CurrentAFT.RootTaggedPhysicalFactorization
open _root_.P2M8f8f5b7e renaming h355 → _p2mH355
open _root_.P2M8f8f5b7e renaming h356 → _p2mH356
open _root_.P2M8f8f5b7e renaming h357 → _p2mH357
end
open _root_.P2M8f8f5b7e renaming h355 → _p2mH355
open _root_.P2M8f8f5b7e renaming h356 → _p2mH356
open _root_.P2M8f8f5b7e renaming h357 → _p2mH357
namespace CurrentAFT.RootTaggedPhysicalFactorization
end CurrentAFT.RootTaggedPhysicalFactorization
namespace CurrentAFT.RootTaggedPhysicalFactorization.fixedPhysical
end CurrentAFT.RootTaggedPhysicalFactorization.fixedPhysical
namespace CurrentAFT.RootTaggedPhysicalFactorization.fixedPhysical.match_1
end CurrentAFT.RootTaggedPhysicalFactorization.fixedPhysical.match_1
namespace CurrentAFT.RootTaggedPhysicalFactorization.rootReferenceByGroup
end CurrentAFT.RootTaggedPhysicalFactorization.rootReferenceByGroup
namespace CurrentAFT.RootTaggedPhysicalFactorization.unitPolynomial
end CurrentAFT.RootTaggedPhysicalFactorization.unitPolynomial
namespace CurrentAFT.RootUnselectedPhysicalLinear.raw
end CurrentAFT.RootUnselectedPhysicalLinear.raw
section
namespace CurrentAFT.RootConditionalComponent
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection PairedRootPlacement
  PairedRootInput PairedRootCentering CycleRootExpansion ControlCoordinates
  RootTaggedPhysicalFactorization RootUnselectedPhysicalLinear RootBackgroundDenominatorProduct
  RootLocalDenominators RootIndependentBackground LocalReferenceEnergy FinitePolynomialTensor
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootConditionalComponent.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootConditionalComponent.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootConditionalComponent.classicalProdDecidableEq
attribute [local instance] _root_.CurrentAFT.RootConditionalComponent.classicalSubtypeDecidableEq
attribute [local instance] _root_.CurrentAFT.RootConditionalComponent.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount ProposalPrimary.primaryLaw
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h404 {Index Value : Type*} [CommMonoid Value]
    (first second : Fintype Index) (value : Index → Value) :
    (@Finset.univ Index first).prod value = (@Finset.univ Index second).prod value := by
  cases Subsingleton.elim first second
  rfl
open _root_.P2M8f8f5b7e renaming h404 → _p2mH404
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h403 {Selected Pool Value : Type*} [CommMonoid Value]
    (first second : Fintype Selected) (embedding : Selected ↪ Pool)
    (firstRest : Fintype {point : Pool // point ∉ (@Finset.univ Selected first).map embedding})
    (secondRest : Fintype {point : Pool // point ∉ (@Finset.univ Selected second).map embedding})
    (value : Pool → Value) :
    (@Finset.univ _ firstRest).prod (fun point => value point.val) =
      (@Finset.univ _ secondRest).prod (fun point => value point.val) := by
  cases Subsingleton.elim first second
  exact _p2mH404 firstRest secondRest _
open _root_.P2M8f8f5b7e renaming h403 → _p2mH403
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h256 (security : ℕ) (queue : ℤ) (block : _root_.CurrentAFT.ActualBlockFock.BlockIndex security) :
    _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (_root_.CurrentAFT.RootUnselectedPhysicalLinear.positiveAt security queue block) =
      _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue block := by
  rcases block with leg | (center | point)
  · exact _p2mH274 security
  · change (∑ root, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root •
      _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.RootTaggedLocal.shiftedLaw security .free 0 root).weight) = _
    rw [← _p2mH277]
    rfl
  · change (∑ root, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight root •
      _root_.AFT.RepresentedPolynomial.singleGenerating (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight (_root_.CurrentAFT.RootTaggedLocal.shiftedLaw security .queue queue root).weight) = _
    rw [← _p2mH277]
    rfl
open _root_.P2M8f8f5b7e renaming h256 → _p2mH256
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h253 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (roots : _root_.CurrentAFT.ActualBlockFock.BlockIndex security → _root_.CurrentAFT.CycleRootExpansion.Root security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue (fun block => (roots block).val) kernel.val =
      _root_.CurrentAFT.RootTaggedPhysicalFactorization.selectedPolynomial queue selection tagged (roots ∘ _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged) kernel *
        ∏ index : selection.kept, _root_.CurrentAFT.RootUnselectedPhysicalLinear.positiveAt security queue index.val (roots index.val) := by
  rw [_p2mH390]
  unfold _root_.CurrentAFT.TypedTaggedPhysical.selectedMass
  rw [_p2mH385, _p2mH388]
  have hchannels : _root_.CurrentAFT.TypedRolePolynomial.raw security r s
      (fun i => ((roots (.inr (.inl (selection.compensator i)))).val : ℤ))
      (fun i => ((roots (.inl (selection.primary i))).val : ℤ))
      (fun i => ((roots (.inr (.inl (selection.body i)))).val : ℤ)) =
      fun role => _root_.CurrentAFT.RootTaggedPhysicalFactorization.fixedPhysical queue selection tagged (.inl role)
        (fun slot => (roots ∘ _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged) ⟨.inl role, slot⟩) := by
    funext role
    cases role <;> rfl
  rw [hchannels]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  rw [_p2mH367]
  congr 1
  rcases index.val with leg | (center | point) <;> rfl
open _root_.P2M8f8f5b7e renaming h253 → _p2mH253
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h255 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (roots : _root_.CurrentAFT.ActualBlockFock.BlockIndex security → _root_.CurrentAFT.CycleRootExpansion.Root security) :
    (∏ block, _root_.CurrentAFT.RootConditionalComponent.keptFactor queue selection block (roots block)) =
      ∏ index : selection.kept, _root_.CurrentAFT.RootUnselectedPhysicalLinear.positiveAt security queue index.val (roots index.val) := by
  unfold _root_.CurrentAFT.RootConditionalComponent.keptFactor
  rw [← Finset.prod_filter]
  have hfilter : (Finset.univ : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)).filter (fun block => block ∈ selection.kept) =
      selection.kept := by ext block; simp
  rw [hfilter]
  exact Finset.prod_subtype selection.kept (fun _ => Iff.rfl) _
open _root_.P2M8f8f5b7e renaming h255 → _p2mH255
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h251 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (roots : Sigma (_root_.CurrentAFT.PairedRootPlacement.groupRootSlots selection tagged) → _root_.CurrentAFT.CycleRootExpansion.Root security) :
    (∏ slot, _root_.CurrentAFT.RootConditionalComponent.keptFactor queue selection (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged slot) (roots slot)) =
      _root_.CurrentAFT.RootTaggedPhysicalFactorization.hitPolynomial queue selection tagged roots := by
  rw [← (_root_.CurrentAFT.PairedRootPlacement.activeSlotsEquiv selection tagged).symm.prod_comp]
  rw [Fintype.prod_sum_type]
  have hselected : (∏ slot : Sigma (_root_.CurrentAFT.PairedRootPlacement.selectedRootSlots r s), _root_.CurrentAFT.RootConditionalComponent.keptFactor queue selection
      (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ((_root_.CurrentAFT.PairedRootPlacement.activeSlotsEquiv selection tagged).symm (.inl slot)))
      (roots ((_root_.CurrentAFT.PairedRootPlacement.activeSlotsEquiv selection tagged).symm (.inl slot)))) = 1 := by
    apply Finset.prod_eq_one
    intro slot _
    have hroot : _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ((_root_.CurrentAFT.PairedRootPlacement.activeSlotsEquiv selection tagged).symm (.inl slot)) =
        selection.removedEmbedding (_root_.CurrentAFT.PairedRootPlacement.selectedRootEquiv r s slot) := by
      change _root_.CurrentAFT.PairedRootPlacement.activeRootEmbedding selection tagged
        ((_root_.CurrentAFT.PairedRootPlacement.activeSlotsEquiv selection tagged) ((_root_.CurrentAFT.PairedRootPlacement.activeSlotsEquiv selection tagged).symm (.inl slot))) = _
      rw [Equiv.apply_symm_apply]
      rfl
    have hnot : _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged ((_root_.CurrentAFT.PairedRootPlacement.activeSlotsEquiv selection tagged).symm (.inl slot)) ∉ selection.kept := by
      rw [hroot]
      intro hkept
      have hnotremoved : selection.removedEmbedding (_root_.CurrentAFT.PairedRootPlacement.selectedRootEquiv r s slot) ∉ selection.removed := by
        simpa only [_root_.CurrentAFT.TaggedSelection.Selection.kept, Finset.mem_sdiff, Finset.mem_univ, true_and] using hkept
      apply hnotremoved
      exact Finset.mem_map.mpr ⟨_root_.CurrentAFT.PairedRootPlacement.selectedRootEquiv r s slot, Finset.mem_univ _, rfl⟩
    exact if_neg hnot
  rw [hselected, one_mul]
  apply Finset.prod_congr rfl
  intro index _
  change _root_.CurrentAFT.RootConditionalComponent.keptFactor queue selection index.val.val (roots ⟨.inr index, (0 : Fin 1)⟩) = _
  exact if_pos index.val.property
open _root_.P2M8f8f5b7e renaming h251 → _p2mH251
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h254 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) :
    (∏ index : _root_.CurrentAFT.RootInactivePlacement.InactiveRoot selection tagged,
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (_root_.CurrentAFT.RootConditionalComponent.keptFactor queue selection index.val)) =
      ∏ index : _root_.CurrentAFT.RootBackgroundDenominatorProduct.InactiveKept selection tagged,
        _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue index.val.val := by
  rw [← (_root_.CurrentAFT.RootInactivePlacement.inactiveEquiv selection tagged).symm.prod_comp]
  apply Finset.prod_congr rfl
  intro index _
  have hfactor : _root_.CurrentAFT.RootConditionalComponent.keptFactor queue selection index.val.val = _root_.CurrentAFT.RootUnselectedPhysicalLinear.positiveAt security queue index.val.val := by
    funext root
    exact if_pos index.val.property
  change _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (_root_.CurrentAFT.RootConditionalComponent.keptFactor queue selection index.val.val) = _
  rw [hfactor, _p2mH256]
open _root_.P2M8f8f5b7e renaming h254 → _p2mH254
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h252 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.CycleRootExpansion.actualComponent security (tagged.map layout.toEmbedding)
      (fun roots => _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue
        (fun block => (roots (layout block)).val) kernel.val) =
      _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.ActualRootPhysicalResponse.rawPhysical queue selection tagged) (_root_.CurrentAFT.PairedRootInput.jointInput selection tagged layout kernel) *
        ∏ index : _root_.CurrentAFT.RootBackgroundDenominatorProduct.InactiveKept selection tagged,
          _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue index.val.val := by
  refine (_p2mH250 selection tagged layout
    (fun roots => _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue (fun block => (roots block).val) kernel.val)).trans ?_
  have hsum : (∑ roots, ((_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.ActualBlockFock.BlockIndex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security)).weight roots *
      _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout (roots ∘ _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged)) •
        _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue (fun block => (roots block).val) kernel.val) =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.ActualBlockFock.BlockIndex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security))
        (fun roots => (_root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout (roots ∘ _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged) •
          _root_.CurrentAFT.RootTaggedPhysicalFactorization.selectedPolynomial queue selection tagged (roots ∘ _root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged) kernel) *
            ∏ block, _root_.CurrentAFT.RootConditionalComponent.keptFactor queue selection block (roots block)) := by
    simp only [_root_.CurrentAFT.CycleRootExpansion.expectationLinear, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr rfl
    intro roots _
    rw [_p2mH253, _p2mH255, smul_mul_assoc, smul_smul]
  rw [hsum, _p2mH333 (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged)
    (fun _ : _root_.CurrentAFT.ActualBlockFock.BlockIndex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security)
    (fun roots => _root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout roots • _root_.CurrentAFT.RootTaggedPhysicalFactorization.selectedPolynomial queue selection tagged roots kernel)
    (_root_.CurrentAFT.RootConditionalComponent.keptFactor queue selection)]
  apply congrArg₂ (fun first second : MvPolynomial (_root_.CurrentAFT.ActualControls.Palette security) ℝ => first * second)
  · refine Eq.trans ?_ (_p2mH357 queue selection tagged layout kernel).symm
    simp only [_root_.CurrentAFT.CycleRootExpansion.expectationLinear, LinearMap.coe_mk, AddHom.coe_mk]
    apply Finset.sum_congr (by ext word; simp)
    intro roots _
    apply congrArg₂ (fun (weight : ℝ) (value : MvPolynomial (_root_.CurrentAFT.ActualControls.Palette security) ℝ) => weight • value)
    · change (∏ slot, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (roots slot)) =
        (∏ slot, (_root_.CurrentAFT.CycleRootExpansion.rootReference security).weight (roots slot))
      exact Finset.prod_congr (by ext slot; simp) (fun _ _ => rfl)
    · rw [← smul_mul_assoc]
      apply congrArg (fun factor => (_root_.CurrentAFT.PairedRootCentering.rootDensity selection tagged layout roots •
        _root_.CurrentAFT.RootTaggedPhysicalFactorization.selectedPolynomial queue selection tagged roots kernel) * factor)
      refine Eq.trans ?_ (_p2mH251 queue selection tagged roots)
      exact Finset.prod_congr (by ext slot; simp) (fun _ _ => rfl)
  · refine Eq.trans ?_ (_p2mH254 queue selection tagged)
    exact _p2mH403 _ _ (_root_.CurrentAFT.PairedRootPlacement.rootEmbedding selection tagged) _ _
      (fun block => _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.CurrentAFT.CycleRootExpansion.rootReference security) (_root_.CurrentAFT.RootConditionalComponent.keptFactor queue selection block))
open _root_.P2M8f8f5b7e renaming h252 → _p2mH252
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h257 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.ActualRootResponse.response order horder queue selection tagged layout kernel) *
        _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.BackgroundPolynomialEvaluation.fixedQueueGenerating security queue) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.CurrentAFT.CycleRootExpansion.actualComponent security (tagged.map layout.toEmbedding)
          (fun roots => _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue
            (fun block => (roots (layout block)).val) kernel.val)) := by
  have hden : (∏ group, _root_.CurrentAFT.ActualRootPhysicalResponse.localDenominator queue selection tagged group) *
      (∏ index : _root_.CurrentAFT.RootBackgroundDenominatorProduct.InactiveKept selection tagged,
        _root_.CurrentAFT.RootUnselectedBlockChannel.positivePolynomial security queue index.val.val) =
        _root_.CurrentAFT.BackgroundPolynomialEvaluation.fixedQueueGenerating security queue := by
    refine Eq.trans ?_ (_p2mH245 queue selection tagged)
    apply congrArg₂ (fun first second : MvPolynomial (_root_.CurrentAFT.ActualControls.Palette security) ℝ => first * second)
    · apply Finset.prod_congr (by ext group; simp)
      intro group _
      rcases group with (primary | ordinary) | kept <;> rfl
    · exact Finset.prod_congr (by ext index; simp) (fun _ _ => rfl)
  rw [_p2mH252, map_mul, ← _p2mH35
    order horder queue selection tagged layout kernel, mul_assoc, ← map_mul, hden]
open _root_.P2M8f8f5b7e renaming h257 → _p2mH257
end
open _root_.P2M8f8f5b7e renaming h251 → _p2mH251
open _root_.P2M8f8f5b7e renaming h252 → _p2mH252
open _root_.P2M8f8f5b7e renaming h253 → _p2mH253
open _root_.P2M8f8f5b7e renaming h254 → _p2mH254
open _root_.P2M8f8f5b7e renaming h255 → _p2mH255
open _root_.P2M8f8f5b7e renaming h256 → _p2mH256
open _root_.P2M8f8f5b7e renaming h257 → _p2mH257
open _root_.P2M8f8f5b7e renaming h403 → _p2mH403
open _root_.P2M8f8f5b7e renaming h404 → _p2mH404
end CurrentAFT.RootConditionalComponent
open _root_.P2M8f8f5b7e renaming h251 → _p2mH251
open _root_.P2M8f8f5b7e renaming h252 → _p2mH252
open _root_.P2M8f8f5b7e renaming h253 → _p2mH253
open _root_.P2M8f8f5b7e renaming h254 → _p2mH254
open _root_.P2M8f8f5b7e renaming h255 → _p2mH255
open _root_.P2M8f8f5b7e renaming h256 → _p2mH256
open _root_.P2M8f8f5b7e renaming h257 → _p2mH257
open _root_.P2M8f8f5b7e renaming h403 → _p2mH403
open _root_.P2M8f8f5b7e renaming h404 → _p2mH404
end
open _root_.P2M8f8f5b7e renaming h251 → _p2mH251
open _root_.P2M8f8f5b7e renaming h252 → _p2mH252
open _root_.P2M8f8f5b7e renaming h253 → _p2mH253
open _root_.P2M8f8f5b7e renaming h254 → _p2mH254
open _root_.P2M8f8f5b7e renaming h255 → _p2mH255
open _root_.P2M8f8f5b7e renaming h256 → _p2mH256
open _root_.P2M8f8f5b7e renaming h257 → _p2mH257
namespace CurrentAFT.ActualRootDefect
end CurrentAFT.ActualRootDefect
namespace CurrentAFT.ActualRootDefect.selectedDefect
end CurrentAFT.ActualRootDefect.selectedDefect
namespace CurrentAFT.ActualRootResponse.response
end CurrentAFT.ActualRootResponse.response
namespace CurrentAFT.RootConditionalComponent
end CurrentAFT.RootConditionalComponent
section
namespace CurrentAFT.ActualRootDefectPhysical
open AFT ActualBlockFock TaggedSelection CycleRootExpansion ControlCoordinates
  LocalCoefficientFamily ActualRootDefect RootConditionalComponent
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualRootDefectPhysical.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootDefectPhysical.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.ActualRootDefectPhysical.vertexDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h29 {Value : Type*} [AddCommGroup Value] [Module ℝ Value]
    {security : ℕ} (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (test : (_root_.CurrentAFT.CycleRootExpansion.Vertex security → _root_.CurrentAFT.CycleRootExpansion.Root security) → Value) :
    (∑ tagged ∈ (Finset.univ : Finset (Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security))).filter (fun tagged => 2 ≤ tagged.card),
      _root_.CurrentAFT.CycleRootExpansion.actualComponent security (tagged.map layout.toEmbedding) test) =
      ∑ tagged ∈ (Finset.univ : Finset (Finset (_root_.CurrentAFT.CycleRootExpansion.Vertex security))).filter (fun tagged => 2 ≤ tagged.card),
        _root_.CurrentAFT.CycleRootExpansion.actualComponent security tagged test := by
  simp only [Finset.sum_filter]
  rw [← layout.finsetCongr.sum_comp]
  simp only [Equiv.finsetCongr_apply, Finset.card_map]
open _root_.P2M8f8f5b7e renaming h29 → _p2mH29
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h30 {security r s : ℕ} (order : ℕ) (horder : 2 ≤ order)
    (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
      (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queue *
        _root_.CurrentAFT.ActualRootDefect.selectedDefect order (by omega) queue selection layout kernel) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order
        (_root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.CurrentAFT.CycleRootExpansion.rootLaw security) (_root_.CurrentAFT.ActualRootDefectPhysical.rootTest queue selection layout kernel) -
          _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security))
            (_root_.CurrentAFT.ActualRootDefectPhysical.rootTest queue selection layout kernel)) := by
  rw [map_mul, _p2mH55]
  simp only [_root_.CurrentAFT.ActualRootDefect.selectedDefect, LinearMap.sum_apply, map_sum, Finset.mul_sum]
  have hlocal (tagged : Finset (_root_.CurrentAFT.ActualBlockFock.BlockIndex security)) :
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.BackgroundPolynomialEvaluation.fixedQueueGenerating security queue) *
        _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
          (_root_.CurrentAFT.ActualRootResponse.response order (by omega) queue selection tagged layout kernel) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.CycleRootExpansion.actualComponent security (tagged.map layout.toEmbedding)
        (_root_.CurrentAFT.ActualRootDefectPhysical.rootTest queue selection layout kernel)) := by
    rw [mul_comm]
    exact _p2mH257 order (by omega) queue selection tagged layout kernel
  simp_rw [hlocal]
  rw [← map_sum, _p2mH29 layout (_root_.CurrentAFT.ActualRootDefectPhysical.rootTest queue selection layout kernel)]
  have hdef := congrArg (fun response => response (_root_.CurrentAFT.ActualRootDefectPhysical.rootTest queue selection layout kernel))
    (_p2mH89 (Value := MvPolynomial (_root_.CurrentAFT.ActualControls.Palette security) ℝ) security)
  simp only [LinearMap.sub_apply, LinearMap.sum_apply] at hdef
  congr 1
  refine Eq.trans ?_ hdef.symm
  apply Finset.sum_congr (by ext tagged; simp)
  intro tagged _
  rfl
open _root_.P2M8f8f5b7e renaming h30 → _p2mH30
end
open _root_.P2M8f8f5b7e renaming h29 → _p2mH29
open _root_.P2M8f8f5b7e renaming h30 → _p2mH30
end CurrentAFT.ActualRootDefectPhysical
open _root_.P2M8f8f5b7e renaming h29 → _p2mH29
open _root_.P2M8f8f5b7e renaming h30 → _p2mH30
end
open _root_.P2M8f8f5b7e renaming h29 → _p2mH29
open _root_.P2M8f8f5b7e renaming h30 → _p2mH30
namespace CurrentAFT.ActualLayouts
end CurrentAFT.ActualLayouts
section
namespace CurrentAFT.RootConditionalResidues
open AFT ActualBlockFock TaggedSelection JointTaggedPhysicalFock TaggedPhysicalFock
  OrdinaryPhysicalFock TypedTaggedPhysical RootBackgroundPolynomial ActualLayouts
  ActualBlockMean ActualCycleMeanMGF ConditionalHistogramMean CycleRootExpansion ControlCoordinates
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootConditionalResidues.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootConditionalResidues.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootConditionalResidues.classicalSigmaDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h258 (security : ℕ) (firstComp secondComp firstAttach secondAttach : ℤ)
    (hcomp : (firstComp : _root_.CurrentAFT.CycleRootExpansion.Root security) = (secondComp : _root_.CurrentAFT.CycleRootExpansion.Root security))
    (hattach : (firstAttach : _root_.CurrentAFT.CycleRootExpansion.Root security) = (secondAttach : _root_.CurrentAFT.CycleRootExpansion.Root security)) :
    _root_.CurrentAFT.TaggedPhysicalFock.averagedPairedChannel security firstComp firstAttach = _root_.CurrentAFT.TaggedPhysicalFock.averagedPairedChannel security secondComp secondAttach := by
  apply LinearMap.ext
  intro score
  simp only [_p2mH381,
    _root_.CurrentAFT.RootSelectedZeroTag.pairedMassAt_periodic security firstComp secondComp firstAttach secondAttach hcomp hattach]
open _root_.P2M8f8f5b7e renaming h258 → _p2mH258
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h260 (security : ℕ) (first second : ℤ)
    (hequal : (first : _root_.CurrentAFT.CycleRootExpansion.Root security) = (second : _root_.CurrentAFT.CycleRootExpansion.Root security)) :
    _root_.CurrentAFT.OrdinaryPhysicalFock.bodyChannel security first = _root_.CurrentAFT.OrdinaryPhysicalFock.bodyChannel security second := by
  ext score word
  simp only [_root_.CurrentAFT.OrdinaryPhysicalFock.bodyChannel, _root_.CurrentAFT.OrdinaryPhysicalFock.translatedProfile,
    _root_.CurrentAFT.RootBackgroundPolynomial.shiftEquiv_eq_of_cast security first second hequal]
open _root_.P2M8f8f5b7e renaming h260 → _p2mH260
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h265 (security r s : ℕ)
    (firstComp secondComp firstAttach secondAttach : Fin r → ℤ) (firstBody secondBody : Fin s → ℤ)
    (hcomp : ∀ index, (firstComp index : _root_.CurrentAFT.CycleRootExpansion.Root security) = (secondComp index : _root_.CurrentAFT.CycleRootExpansion.Root security))
    (hattach : ∀ index, (firstAttach index : _root_.CurrentAFT.CycleRootExpansion.Root security) = (secondAttach index : _root_.CurrentAFT.CycleRootExpansion.Root security))
    (hbody : ∀ index, (firstBody index : _root_.CurrentAFT.CycleRootExpansion.Root security) = (secondBody index : _root_.CurrentAFT.CycleRootExpansion.Root security))
    (index : Fin (r + s)) :
    _root_.CurrentAFT.JointTaggedPhysicalFock.physicalChannel security r s firstComp firstAttach firstBody index =
      _root_.CurrentAFT.JointTaggedPhysicalFock.physicalChannel security r s secondComp secondAttach secondBody index := by
  have hrole (role : Fin r ⊕ Fin s) :
      _root_.CurrentAFT.JointTaggedPhysicalFock.roleChannel security r s firstComp firstAttach firstBody role =
        _root_.CurrentAFT.JointTaggedPhysicalFock.roleChannel security r s secondComp secondAttach secondBody role := by
    cases role with
    | inl index =>
      simp only [_root_.CurrentAFT.JointTaggedPhysicalFock.roleChannel, _root_.CurrentAFT.JointTaggedPhysicalFock.primaryChannel,
        _p2mH258 security _ _ _ _ (hcomp index) (hattach index)]
    | inr index =>
      simp only [_root_.CurrentAFT.JointTaggedPhysicalFock.roleChannel, _root_.CurrentAFT.JointTaggedPhysicalFock.ordinaryChannel, _p2mH260 security _ _ (hbody index)]
  exact hrole (finSumFinEquiv.symm index)
open _root_.P2M8f8f5b7e renaming h265 → _p2mH265
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h259 (security : ℕ) (queue : ℤ) (first second : _root_.CurrentAFT.ActualBlockFock.BlockIndex security → ℤ)
    (hequal : ∀ index, (first index : _root_.CurrentAFT.CycleRootExpansion.Root security) = (second index : _root_.CurrentAFT.CycleRootExpansion.Root security))
    (index : _root_.CurrentAFT.ActualBlockFock.BlockIndex security) :
    _root_.CurrentAFT.TypedTaggedPhysical.blockLaw security queue first index = _root_.CurrentAFT.TypedTaggedPhysical.blockLaw security queue second index := by
  rcases index with leg | (center | point)
  · exact _p2mH248 security _ _ (hequal (.inl leg))
  · simp only [_root_.CurrentAFT.TypedTaggedPhysical.blockLaw, _root_.CurrentAFT.ActualBlockFock.blockLawAt,
      _root_.CurrentAFT.RootBackgroundPolynomial.shiftEquiv_eq_of_cast security _ _ (hequal (.inr (.inl center)))]
  · have hshift : ((first (.inr (.inr point)) + queue : ℤ) : _root_.CurrentAFT.CycleRootExpansion.Root security) =
        ((second (.inr (.inr point)) + queue : ℤ) : _root_.CurrentAFT.CycleRootExpansion.Root security) := by
      simp only [Int.cast_add, hequal]
    simp only [_root_.CurrentAFT.TypedTaggedPhysical.blockLaw, _root_.CurrentAFT.ActualBlockFock.blockLawAt, _root_.CurrentAFT.RootBackgroundPolynomial.shiftEquiv_eq_of_cast security _ _ hshift]
open _root_.P2M8f8f5b7e renaming h259 → _p2mH259
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h266 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (first second : _root_.CurrentAFT.ActualBlockFock.BlockIndex security → ℤ)
    (hequal : ∀ index, (first index : _root_.CurrentAFT.CycleRootExpansion.Root security) = (second index : _root_.CurrentAFT.CycleRootExpansion.Root security))
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.ActualControls.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.CurrentAFT.TypedTaggedPhysical.selectedMass selection first kernel = _root_.CurrentAFT.TypedTaggedPhysical.selectedMass selection second kernel := by
  unfold _root_.CurrentAFT.TypedTaggedPhysical.selectedMass _root_.CurrentAFT.JointTaggedPhysicalFock.jointMass
  congr 1
  funext index
  exact _p2mH265 security r s _ _ _ _ _ _ (fun _ => hequal _) (fun _ => hequal _) (fun _ => hequal _) index
open _root_.P2M8f8f5b7e renaming h266 → _p2mH266
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h261 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (queue : ℤ)
    (first second : _root_.CurrentAFT.ActualBlockFock.BlockIndex security → ℤ)
    (hequal : ∀ index, (first index : _root_.CurrentAFT.CycleRootExpansion.Root security) = (second index : _root_.CurrentAFT.CycleRootExpansion.Root security))
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.ActualControls.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.CurrentAFT.TypedTaggedPhysical.conditionalMass selection queue first kernel =
      _root_.CurrentAFT.TypedTaggedPhysical.conditionalMass selection queue second kernel := by
  unfold _root_.CurrentAFT.TypedTaggedPhysical.conditionalMass
  rw [_p2mH266 selection first second hequal]
  congr 1
  funext index
  exact _p2mH259 security queue first second hequal index.val
open _root_.P2M8f8f5b7e renaming h261 → _p2mH261
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h262 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (queue : ℤ)
    (first second : _root_.CurrentAFT.ActualBlockFock.BlockIndex security → ℤ)
    (hequal : ∀ index, (first index : _root_.CurrentAFT.CycleRootExpansion.Root security) = (second index : _root_.CurrentAFT.CycleRootExpansion.Root security))
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.ActualControls.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue first kernel = _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue second kernel := by
  unfold _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial
  rw [_p2mH261 selection queue first second hequal]
open _root_.P2M8f8f5b7e renaming h262 → _p2mH262
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h263 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (queue : ℤ)
    (roots : _root_.CurrentAFT.ActualBlockFock.BlockIndex security → ℤ)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.ActualControls.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue roots kernel =
      _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue (fun block => ((roots block : _root_.CurrentAFT.CycleRootExpansion.Root security).val : ℤ)) kernel := by
  apply _p2mH262
  intro index
  simp only [Int.cast_natCast, ZMod.natCast_zmod_val]
open _root_.P2M8f8f5b7e renaming h263 → _p2mH263
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h264 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (queue : ℤ)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security) (permutation : Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security))
    (latent : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security → _root_.CurrentAFT.ActualCycleMeanMGF.Edge security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.DensityKernel (Primary := _root_.CurrentAFT.ActualControls.Palette security) (Body := _root_.CurrentAFT.ActualControls.SafePalette security) r s) :
    _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue
      (fun block => _root_.CurrentAFT.ActualBlockMean.rootAt security permutation latent (_root_.CurrentAFT.ActualLayouts.blockLayout layout block)) kernel =
      _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
        (_root_.CurrentAFT.TaggedOutputFock.conditionalMass security r s selection layout queue permutation latent kernel) := rfl
open _root_.P2M8f8f5b7e renaming h264 → _p2mH264
end
open _root_.P2M8f8f5b7e renaming h258 → _p2mH258
open _root_.P2M8f8f5b7e renaming h259 → _p2mH259
open _root_.P2M8f8f5b7e renaming h260 → _p2mH260
open _root_.P2M8f8f5b7e renaming h261 → _p2mH261
open _root_.P2M8f8f5b7e renaming h262 → _p2mH262
open _root_.P2M8f8f5b7e renaming h263 → _p2mH263
open _root_.P2M8f8f5b7e renaming h264 → _p2mH264
open _root_.P2M8f8f5b7e renaming h265 → _p2mH265
open _root_.P2M8f8f5b7e renaming h266 → _p2mH266
end CurrentAFT.RootConditionalResidues
open _root_.P2M8f8f5b7e renaming h258 → _p2mH258
open _root_.P2M8f8f5b7e renaming h259 → _p2mH259
open _root_.P2M8f8f5b7e renaming h260 → _p2mH260
open _root_.P2M8f8f5b7e renaming h261 → _p2mH261
open _root_.P2M8f8f5b7e renaming h262 → _p2mH262
open _root_.P2M8f8f5b7e renaming h263 → _p2mH263
open _root_.P2M8f8f5b7e renaming h264 → _p2mH264
open _root_.P2M8f8f5b7e renaming h265 → _p2mH265
open _root_.P2M8f8f5b7e renaming h266 → _p2mH266
end
open _root_.P2M8f8f5b7e renaming h258 → _p2mH258
open _root_.P2M8f8f5b7e renaming h259 → _p2mH259
open _root_.P2M8f8f5b7e renaming h260 → _p2mH260
open _root_.P2M8f8f5b7e renaming h261 → _p2mH261
open _root_.P2M8f8f5b7e renaming h262 → _p2mH262
open _root_.P2M8f8f5b7e renaming h263 → _p2mH263
open _root_.P2M8f8f5b7e renaming h264 → _p2mH264
open _root_.P2M8f8f5b7e renaming h265 → _p2mH265
open _root_.P2M8f8f5b7e renaming h266 → _p2mH266
namespace CurrentAFT.ActualRootDefectPhysical
end CurrentAFT.ActualRootDefectPhysical
namespace CurrentAFT.JointTaggedPhysicalFock.ordinaryChannel
end CurrentAFT.JointTaggedPhysicalFock.ordinaryChannel
namespace CurrentAFT.JointTaggedPhysicalFock.primaryChannel
end CurrentAFT.JointTaggedPhysicalFock.primaryChannel
namespace CurrentAFT.JointTaggedPhysicalFock.roleChannel
end CurrentAFT.JointTaggedPhysicalFock.roleChannel
namespace CurrentAFT.JointTaggedPhysicalFock.roleSlots
end CurrentAFT.JointTaggedPhysicalFock.roleSlots
namespace CurrentAFT.JointTaggedPhysicalFock.roleSlots.match_1
end CurrentAFT.JointTaggedPhysicalFock.roleSlots.match_1
namespace CurrentAFT.OrdinaryPhysicalFock
end CurrentAFT.OrdinaryPhysicalFock
namespace CurrentAFT.OrdinaryPhysicalFock.bodyChannel
end CurrentAFT.OrdinaryPhysicalFock.bodyChannel
namespace CurrentAFT.RootConditionalResidues
end CurrentAFT.RootConditionalResidues
namespace CurrentAFT.TypedTaggedPhysical.blockLaw
end CurrentAFT.TypedTaggedPhysical.blockLaw
section
namespace CurrentAFT.RootActualOutputPolynomial
open AFT AFT.RepresentedPolynomial ActualBlockFock ActualBlockMean ActualFockBound
  TaggedSelection TaggedOutputFock CycleRootExpansion ActualLayouts ActualRootDefectPhysical
  LocalReferenceEnergy RootBackgroundPolynomial ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.RootActualOutputPolynomial.classicalFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootActualOutputPolynomial.classicalSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootActualOutputPolynomial.vertexDecidableEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.legCount
section Generic
variable {Source Target Value : Type*} [Fintype Source] [Fintype Target]
  [AddCommGroup Value] [Module ℝ Value]
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h240 (law : _root_.AFT.FiniteDist Source) (map : Source → Target) (test : Target → Value) :
    _root_.CurrentAFT.CycleRootExpansion.expectationLinear (law.map map) test = _root_.CurrentAFT.CycleRootExpansion.expectationLinear law (test ∘ map) := by
  simp only [_root_.CurrentAFT.CycleRootExpansion.expectationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.AFT.FiniteDist.map_weight, Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Function.comp_apply]
open _root_.P2M8f8f5b7e renaming h240 → _p2mH240
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h241 (law : _root_.AFT.FiniteDist Source) (channel : Source → _root_.AFT.FiniteDist Target)
    (test : Target → Value) :
    _root_.CurrentAFT.CycleRootExpansion.expectationLinear (law.mix channel) test =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear law (fun source => _root_.CurrentAFT.CycleRootExpansion.expectationLinear (channel source) test) := by
  simp only [_root_.CurrentAFT.CycleRootExpansion.expectationLinear, LinearMap.coe_mk, AddHom.coe_mk,
    _root_.AFT.FiniteDist.mix_weight, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
open _root_.P2M8f8f5b7e renaming h241 → _p2mH241
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h242 {Output : Type*} [Fintype Output]
    (channel : (Output → ℝ) →ₗ[ℝ] Value) (law : _root_.AFT.FiniteDist Source) (mass : Source → Output → ℝ) :
    channel (fun output => law.expectation (fun source => mass source output)) =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear law (fun source => channel (mass source)) := by
  have hmass : (fun output => law.expectation (fun source => mass source output)) =
      ∑ source, law.weight source • mass source := by
    funext output
    simp only [_root_.AFT.FiniteDist.expectation, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hmass, map_sum]
  simp only [map_smul, _root_.CurrentAFT.CycleRootExpansion.expectationLinear, LinearMap.coe_mk, AddHom.coe_mk]
open _root_.P2M8f8f5b7e renaming h242 → _p2mH242
end Generic
open _root_.P2M8f8f5b7e renaming h240 → _p2mH240
open _root_.P2M8f8f5b7e renaming h241 → _p2mH241
open _root_.P2M8f8f5b7e renaming h242 → _p2mH242
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h243 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (permutation : Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)) (latent : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security → _root_.CurrentAFT.ActualCycleMeanMGF.Edge security) :
    _root_.CurrentAFT.ActualRootDefectPhysical.rootTest queue selection (_root_.CurrentAFT.ActualLayouts.blockLayout layout) kernel (_root_.CurrentAFT.RootBackgroundPolynomial.rootedResidues security permutation latent) =
      _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
        (_root_.CurrentAFT.TaggedOutputFock.conditionalMass security r s selection layout queue permutation latent kernel.val) := by
  change _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue
    (fun block => (((_root_.CurrentAFT.ActualBlockMean.rootAt security permutation latent (_root_.CurrentAFT.ActualLayouts.blockLayout layout block) : ℤ) : _root_.CurrentAFT.CycleRootExpansion.Root security).val : ℤ)) kernel.val = _
  rw [← _p2mH263,
    _p2mH264]
open _root_.P2M8f8f5b7e renaming h243 → _p2mH243
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h239 {security r s : ℕ} (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.CurrentAFT.CycleRootExpansion.rootLaw security) (_root_.CurrentAFT.ActualRootDefectPhysical.rootTest queue selection (_root_.CurrentAFT.ActualLayouts.blockLayout layout) kernel) =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)))
        (fun permutation => _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
          (_root_.CurrentAFT.TaggedOutputFock.outputMass security r s selection layout queue permutation kernel.val)) := by
  rw [_p2mH249, _p2mH241]
  simp_rw [_p2mH240]
  apply congrArg (_root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security))))
  funext permutation
  change _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security => _root_.CurrentAFT.DiffuseProfiles.edgeLaw security))
    (fun latent => _root_.CurrentAFT.ActualRootDefectPhysical.rootTest queue selection (_root_.CurrentAFT.ActualLayouts.blockLayout layout) kernel (_root_.CurrentAFT.RootBackgroundPolynomial.rootedResidues security permutation latent)) = _
  simp_rw [_p2mH243]
  rw [← _p2mH242]
  apply congrArg (_root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight)
  funext output
  simp only [_root_.CurrentAFT.TaggedOutputFock.outputMass, _root_.CurrentAFT.ActualFockBound.latentLaw, _root_.AFT.FiniteDist.expectation, _root_.AFT.FiniteDist.independent]
  apply Finset.sum_congr (by ext latent; simp)
  intro latent _
  rfl
open _root_.P2M8f8f5b7e renaming h239 → _p2mH239
end
open _root_.P2M8f8f5b7e renaming h239 → _p2mH239
open _root_.P2M8f8f5b7e renaming h240 → _p2mH240
open _root_.P2M8f8f5b7e renaming h241 → _p2mH241
open _root_.P2M8f8f5b7e renaming h242 → _p2mH242
open _root_.P2M8f8f5b7e renaming h243 → _p2mH243
end CurrentAFT.RootActualOutputPolynomial
open _root_.P2M8f8f5b7e renaming h239 → _p2mH239
open _root_.P2M8f8f5b7e renaming h240 → _p2mH240
open _root_.P2M8f8f5b7e renaming h241 → _p2mH241
open _root_.P2M8f8f5b7e renaming h242 → _p2mH242
open _root_.P2M8f8f5b7e renaming h243 → _p2mH243
end
open _root_.P2M8f8f5b7e renaming h239 → _p2mH239
open _root_.P2M8f8f5b7e renaming h240 → _p2mH240
open _root_.P2M8f8f5b7e renaming h241 → _p2mH241
open _root_.P2M8f8f5b7e renaming h242 → _p2mH242
open _root_.P2M8f8f5b7e renaming h243 → _p2mH243
namespace CurrentAFT.CompleteRaisingEvaluation
end CurrentAFT.CompleteRaisingEvaluation
namespace CurrentAFT.CompleteRaisingEvaluation.normalizedJoint
end CurrentAFT.CompleteRaisingEvaluation.normalizedJoint
namespace CurrentAFT.CompleteRaisingEvaluation.normalizedSlot
end CurrentAFT.CompleteRaisingEvaluation.normalizedSlot
section
namespace CurrentAFT.RootIndependentSelectedPhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection PairedRootPlacement
  PairedRootInput CycleRootExpansion ControlCoordinates ControlProduct GradedControlAlgebra
  LocalCoefficientFamily RaisingPatternBudget FinitePolynomialTensor
  DiffuseProfiles ProposalPrimary ActualControls CompleteRaisingEvaluation
  RootConditionalComponent
open scoped BigOperators Classical
noncomputable section
attribute [local instance] _root_.CurrentAFT.RootIndependentSelectedPhysical.baselineFinDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentSelectedPhysical.baselineVertexDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentSelectedPhysical.baselineSumDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentSelectedPhysical.baselineProdDecidableEq
attribute [local instance] _root_.CurrentAFT.RootIndependentSelectedPhysical.baselineSubtypeDecidableEq
set_option maxHeartbeats 2400000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount primaryLaw bodyReference
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h282 (security order : ℕ) (horder : 1 ≤ order) (r s : ℕ)
    (role : _root_.CurrentAFT.RaisingPatternBudget.Role r s) (source : _root_.CurrentAFT.RaisingPatternBudget.RoleInput security r s role) :
    _root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s role (Pi.single source 1) =
      (_root_.CurrentAFT.RaisingPatternBudget.roleReference security r s role).weight source • _root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint security order horder r s role source := by
  cases role with
  | inl index =>
      change _root_.CurrentAFT.RaisingChannels.primaryLeading security order horder (Pi.single source 1) +
        _root_.CurrentAFT.RaisingChannels.primaryRaised security order horder (Pi.single source 1) = _
      rw [_root_.CurrentAFT.RaisingChannels.primaryLeading_single, _root_.CurrentAFT.RaisingChannels.primaryRaised_single, ← smul_add]
      congr 1
      unfold _root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint _root_.CurrentAFT.GlobalRaising.primaryPoint
      change _root_.CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear security order horder (_root_.CurrentAFT.GlobalRaising.primaryAtom security source) +
        (_root_.CurrentAFT.NormalizedLocalPolynomial.independentNormalized security order (_root_.CurrentAFT.GlobalRaising.primaryAtom security source).val -
          _root_.CurrentAFT.LocalRaisingLinear.primaryEmbeddingLinear security order horder (_root_.CurrentAFT.GlobalRaising.primaryAtom security source)) = _
      abel
  | inr index =>
      change _root_.CurrentAFT.RaisingChannels.bodyLeading security order horder (Pi.single source 1) +
        _root_.CurrentAFT.RaisingChannels.bodyRaised security order horder (Pi.single source 1) = _
      rw [_root_.CurrentAFT.RaisingChannels.bodyLeading_single, _root_.CurrentAFT.RaisingChannels.bodyRaised_single, ← smul_add]
      exact congrArg (fun value : _root_.CurrentAFT.LocalCoefficientFamily.Family security order => (_root_.CurrentAFT.ActualControls.bodyReference security).weight source • value)
        (_p2mH181 security order horder _ _).symm
open _root_.P2M8f8f5b7e renaming h282 → _p2mH282
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h283 (security order : ℕ) (horder : 1 ≤ order) {r s : ℕ}
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s) (_root_.CurrentAFT.RaisingPatternKernel.inputJoint security kernel) =
      _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order horder kernel := by
  unfold _root_.CurrentAFT.FinitePolynomialTensor.synthesis
  simp_rw [_p2mH282, Finset.prod_smul, smul_smul]
  rw [← (Equiv.prodPiEquivSumPi (fun _ : Fin r => _root_.CurrentAFT.RootIndependentSelectedPhysical.Palette security)
    (fun _ : Fin s => _root_.CurrentAFT.ActualControls.SafePalette security)).sum_comp, Fintype.sum_prod_type]
  unfold _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint
  apply Finset.sum_congr rfl
  intro colors _
  apply Finset.sum_congr rfl
  intro centers _
  simp only [Fintype.prod_sum_type, _root_.CurrentAFT.RaisingPatternBudget.roleReference, _root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint, _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedSlot,
    Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Sum.elim_inr, _root_.CurrentAFT.RaisingPatternBudget.RoleInput, _root_.CurrentAFT.RaisingPatternKernel.inputJoint]
  rw [mul_comm]
open _root_.P2M8f8f5b7e renaming h283 → _p2mH283
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h410 (security : ℕ)
    (labels : _root_.CurrentAFT.CycleSelections.Selection (_root_.CurrentAFT.Parameters.bodySize security) 0) (word : Fin 0 → _root_.CurrentAFT.CycleRootExpansion.Root security) :
    _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security 0 labels word = 1 := by
  unfold _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient _root_.CurrentAFT.CycleSelections.centeredRootDensity
  simp only [Fin.prod_univ_zero, _root_.AFT.FiniteDist.expectation_const]
open _root_.P2M8f8f5b7e renaming h410 → _p2mH410
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h281 {security r s : ℕ} (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s)
    (word : _root_.CurrentAFT.PairedRootInput.GroupInput selection ∅) :
    _root_.CurrentAFT.PairedRootInput.jointInput selection ∅ layout kernel word = _root_.CurrentAFT.PairedRootInput.controlKernel selection ∅ kernel (fun group => (word group).2) := by
  unfold _root_.CurrentAFT.PairedRootInput.jointInput
  have hzero (count : ℕ) (hcount : count = 0)
      (labels : _root_.CurrentAFT.CycleSelections.Selection (_root_.CurrentAFT.Parameters.bodySize security) count) (input : Fin count → _root_.CurrentAFT.CycleRootExpansion.Root security) :
      _root_.CurrentAFT.CycleRootExpansion.selectedCoefficient security count labels input = 1 := by
    subst count
    exact _p2mH410 security labels input
  rw [hzero _ Finset.card_empty, one_mul]
open _root_.P2M8f8f5b7e renaming h281 → _p2mH281
set_option maxRecDepth 8192
private def _root_.P2M8f8f5b7e.h407 {RootData Control : Type*} [Fintype RootData] (law : _root_.AFT.FiniteDist RootData) :
    ((RootData × Control) → ℝ) →ₗ[ℝ] (Control → ℝ) where
  toFun score control := law.expectation (fun root => score (root, control))
  map_add' first second := by funext control; exact _root_.AFT.FiniteDist.expectation_add _ _ _
  map_smul' scalar score := by funext control; exact _root_.AFT.FiniteDist.expectation_const_mul _ _ _
open _root_.P2M8f8f5b7e renaming h407 → CurrentAFT.RootIndependentSelectedPhysical.meanLinear
open _root_.P2M8f8f5b7e renaming h407 → _p2mH407
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h405 {RootData Control Value : Type*} [Fintype RootData] [CommRing Value] [Algebra ℝ Value]
    (law : _root_.AFT.FiniteDist RootData) (channel : (Control → ℝ) →ₗ[ℝ] Value) :
    _root_.CurrentAFT.RootPolynomialTensor.averagedChannel (Index := Unit) (fun _ => law) (fun _ _ => channel) () =
      channel.comp (_p2mH407 law) := by
  apply LinearMap.ext
  intro score
  have hmean : _p2mH407 law score = ∑ root, law.weight root • (fun control => score (root, control)) := by
    funext control
    simp only [_p2mH407, LinearMap.coe_mk, AddHom.coe_mk, _root_.AFT.FiniteDist.expectation,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simp only [_root_.CurrentAFT.RootPolynomialTensor.averagedChannel, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, _root_.CurrentAFT.RootPolynomialTensor.sliceLinear, LinearMap.coe_mk, AddHom.coe_mk]
  rw [hmean, map_sum]
  simp only [map_smul]
open _root_.P2M8f8f5b7e renaming h405 → _p2mH405
set_option maxRecDepth 8192
private def _root_.P2M8f8f5b7e.h408 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) :
    (group : _root_.CurrentAFT.PairedRootPlacement.ActiveGroup selection ∅) → (_root_.CurrentAFT.PairedRootInput.ControlInput selection ∅ group → ℝ) →ₗ[ℝ] _root_.CurrentAFT.LocalCoefficientFamily.Family security order
  | .inl role => _root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s role
  | .inr index => isEmptyElim index
open _root_.P2M8f8f5b7e renaming h408 → CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
open _root_.P2M8f8f5b7e renaming h408 → _p2mH408
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h406 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) :
    _root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection ∅ =
      _root_.CurrentAFT.RootPolynomialTensor.averagedChannel
        (_root_.CurrentAFT.RootTaggedPhysicalFactorization.rootReferenceByGroup selection ∅)
        (fun group _ => _p2mH408 order horder selection group) := by
  funext group
  rcases group with (primary | ordinary) | kept
  · apply LinearMap.ext
    intro score
    have hflag : _root_.CurrentAFT.ActualRootGroupedChannel.primaryFlags selection ∅ primary = fun _ => false := by
      funext slot
      simp only [_root_.CurrentAFT.ActualRootGroupedChannel.primaryFlags, Finset.notMem_empty, decide_false]
    change _root_.CurrentAFT.RootPrimaryGroupedChannel.channel security order (_root_.CurrentAFT.ActualRootGroupedChannel.primaryFlags selection ∅ primary) score = _
    rw [hflag, _root_.CurrentAFT.RootPrimaryGroupedChannel.channel_zero,
      _root_.CurrentAFT.RootSelectedZeroTag.zeroChannel_eq_leading_add_raised security order horder]
    exact congrArg (fun map => map score)
      (_p2mH405 (_root_.AFT.FiniteDist.independent (fun _ : Fin 2 => _root_.CurrentAFT.CycleRootExpansion.rootReference security))
        (_root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s (.inl primary))).symm
  · apply LinearMap.ext
    intro score
    have hflag : _root_.CurrentAFT.ActualRootGroupedChannel.ordinaryFlag selection ∅ ordinary = false := by
      simp only [_root_.CurrentAFT.ActualRootGroupedChannel.ordinaryFlag, Finset.notMem_empty, decide_false]
    change _root_.CurrentAFT.RootOrdinaryGroupedChannel.channel security order horder (_root_.CurrentAFT.ActualRootGroupedChannel.ordinaryFlag selection ∅ ordinary) score = _
    rw [hflag, _root_.CurrentAFT.RootOrdinaryGroupedChannel.channel_false,
      _p2mH370]
    have hmean : _root_.CurrentAFT.SelectedOrdinaryMean.rootMean security (_root_.CurrentAFT.RootOrdinaryGroupedChannel.toRaw security score) =
        _p2mH407 (_root_.AFT.FiniteDist.independent (fun _ : Fin 1 => _root_.CurrentAFT.CycleRootExpansion.rootReference security)) score := by
      funext center
      exact (_root_.CurrentAFT.RootOrdinaryGroupedChannel.oneRoot_expectation security (fun roots => score (roots, center))).symm
    rw [hmean]
    exact congrArg (fun map => map score)
      (_p2mH405 (_root_.AFT.FiniteDist.independent (fun _ : Fin 1 => _root_.CurrentAFT.CycleRootExpansion.rootReference security))
        (_root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s (.inr ordinary))).symm
  · exact isEmptyElim kept
open _root_.P2M8f8f5b7e renaming h406 → CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
open _root_.P2M8f8f5b7e renaming h406 → _p2mH406
set_option maxRecDepth 8192
private theorem _root_.P2M8f8f5b7e.h409 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_p2mH408 order horder selection) (_root_.CurrentAFT.PairedRootInput.controlKernel selection ∅ kernel) =
      _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.RootIndependentSelectedPhysical.normalizedRole security order horder r s) (_root_.CurrentAFT.RaisingPatternKernel.inputJoint security kernel) := by
  unfold _root_.CurrentAFT.FinitePolynomialTensor.synthesis _root_.CurrentAFT.PairedRootInput.controlKernel
  rw [← (Equiv.prodPiEquivSumPi (_root_.CurrentAFT.RaisingPatternBudget.RoleInput security r s) (fun _ : _root_.CurrentAFT.PairedRootPlacement.HitKept selection ∅ => Unit)).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.prod_sum_type, _root_.CurrentAFT.PairedRootInput.ControlInput,
    Equiv.prodPiEquivSumPi, Equiv.sumPiEquivProdPi, Equiv.coe_fn_symm_mk,
    Sum.elim_inl, Sum.elim_inr, _p2mH408, Fintype.prod_empty, mul_one,
    Fintype.sum_unique]
open _root_.P2M8f8f5b7e renaming h409 → _p2mH409
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h284 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order) (queue : ℤ)
    (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.ActualRootResponse.response order horder queue selection ∅ layout kernel = _root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order horder kernel := by
  rw [_p2mH37, _root_.CurrentAFT.GroupedFamilyIdentity.response_eq]
  change _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_root_.CurrentAFT.ActualRootGroupedChannel.channel order horder queue selection ∅)
    (_root_.CurrentAFT.PairedRootInput.jointInput selection ∅ layout kernel) = _
  rw [_p2mH406, _p2mH335]
  simp_rw [_p2mH281]
  rw [← Finset.sum_smul]
  change (∑ roots, (_root_.AFT.FiniteDist.dependentIndependent
    (_root_.CurrentAFT.RootTaggedPhysicalFactorization.rootReferenceByGroup selection ∅)).weight roots) •
      _root_.CurrentAFT.FinitePolynomialTensor.synthesis (_p2mH408 order horder selection) (_root_.CurrentAFT.PairedRootInput.controlKernel selection ∅ kernel) = _
  rw [_root_.AFT.FiniteDist.sum_one, one_smul, _p2mH409, _p2mH283]
open _root_.P2M8f8f5b7e renaming h284 → _p2mH284
set_option maxRecDepth 8192
theorem _root_.P2M8f8f5b7e.h280 {security r s : ℕ} (order : ℕ) (horder : 1 ≤ order)
    (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s) (layout : _root_.CurrentAFT.ActualBlockFock.BlockIndex security ≃ _root_.CurrentAFT.CycleRootExpansion.Vertex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.TruncatedOutput.quotientMap order
      (_root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security))
        (fun roots => _root_.CurrentAFT.TypedTaggedPhysical.conditionalPolynomial selection queue
          (fun block => (roots (layout block)).val) kernel.val)) =
      _root_.CurrentAFT.TruncatedOutput.quotientMap order (_root_.CurrentAFT.BackgroundPolynomialEvaluation.fixedQueueGenerating security queue) *
        _root_.CurrentAFT.BackgroundEvaluation.evaluation security order (_root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order horder kernel) := by
  have h := _p2mH257 order horder queue selection ∅ layout kernel
  rw [_p2mH284, Finset.map_empty] at h
  have hempty : _root_.CurrentAFT.CycleRootExpansion.actualComponent (Value := MvPolynomial (_root_.CurrentAFT.RootIndependentSelectedPhysical.Palette security) ℝ) security ∅ =
      _root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security)) := by
    unfold _root_.CurrentAFT.CycleRootExpansion.actualComponent
    exact _p2mH90 (Value := MvPolynomial (_root_.CurrentAFT.RootIndependentSelectedPhysical.Palette security) ℝ)
      (_root_.CurrentAFT.CycleRootExpansion.rootLaw security) (fun _ => _root_.CurrentAFT.CycleRootExpansion.rootReference security)
  rw [hempty] at h
  exact h.symm.trans (mul_comm _ _)
open _root_.P2M8f8f5b7e renaming h280 → _p2mH280
end
open _root_.P2M8f8f5b7e renaming h280 → _p2mH280
open _root_.P2M8f8f5b7e renaming h281 → _p2mH281
open _root_.P2M8f8f5b7e renaming h282 → _p2mH282
open _root_.P2M8f8f5b7e renaming h283 → _p2mH283
open _root_.P2M8f8f5b7e renaming h284 → _p2mH284
open _root_.P2M8f8f5b7e renaming h405 → _p2mH405
open _root_.P2M8f8f5b7e renaming h406 → CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
open _root_.P2M8f8f5b7e renaming h406 → _p2mH406
open _root_.P2M8f8f5b7e renaming h407 → CurrentAFT.RootIndependentSelectedPhysical.meanLinear
open _root_.P2M8f8f5b7e renaming h407 → _p2mH407
open _root_.P2M8f8f5b7e renaming h408 → CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
open _root_.P2M8f8f5b7e renaming h408 → _p2mH408
open _root_.P2M8f8f5b7e renaming h409 → _p2mH409
open _root_.P2M8f8f5b7e renaming h410 → _p2mH410
end CurrentAFT.RootIndependentSelectedPhysical
open _root_.P2M8f8f5b7e renaming h280 → _p2mH280
open _root_.P2M8f8f5b7e renaming h281 → _p2mH281
open _root_.P2M8f8f5b7e renaming h282 → _p2mH282
open _root_.P2M8f8f5b7e renaming h283 → _p2mH283
open _root_.P2M8f8f5b7e renaming h284 → _p2mH284
open _root_.P2M8f8f5b7e renaming h405 → _p2mH405
open _root_.P2M8f8f5b7e renaming h406 → CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
open _root_.P2M8f8f5b7e renaming h406 → _p2mH406
open _root_.P2M8f8f5b7e renaming h407 → CurrentAFT.RootIndependentSelectedPhysical.meanLinear
open _root_.P2M8f8f5b7e renaming h407 → _p2mH407
open _root_.P2M8f8f5b7e renaming h408 → CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
open _root_.P2M8f8f5b7e renaming h408 → _p2mH408
open _root_.P2M8f8f5b7e renaming h409 → _p2mH409
open _root_.P2M8f8f5b7e renaming h410 → _p2mH410
end
open _root_.P2M8f8f5b7e renaming h280 → _p2mH280
open _root_.P2M8f8f5b7e renaming h281 → _p2mH281
open _root_.P2M8f8f5b7e renaming h282 → _p2mH282
open _root_.P2M8f8f5b7e renaming h283 → _p2mH283
open _root_.P2M8f8f5b7e renaming h284 → _p2mH284
namespace CurrentAFT.ActualCompleteStability
end CurrentAFT.ActualCompleteStability
namespace CurrentAFT.ActualCompleteStability.rootCorrection
end CurrentAFT.ActualCompleteStability.rootCorrection
namespace CurrentAFT.ActualFockBound
end CurrentAFT.ActualFockBound
namespace CurrentAFT.ActualFockBound.latentLaw
end CurrentAFT.ActualFockBound.latentLaw
namespace CurrentAFT.ActualRootFamily
end CurrentAFT.ActualRootFamily
namespace CurrentAFT.ActualRootFamily.rootLinear
end CurrentAFT.ActualRootFamily.rootLinear
namespace CurrentAFT.OrdinaryRaising
end CurrentAFT.OrdinaryRaising
namespace CurrentAFT.OrdinaryRaising.normalizedFamily
end CurrentAFT.OrdinaryRaising.normalizedFamily
namespace CurrentAFT.PhysicalPolynomialAverages
end CurrentAFT.PhysicalPolynomialAverages
namespace CurrentAFT.PhysicalPolynomialAverages.arityOptionMap
end CurrentAFT.PhysicalPolynomialAverages.arityOptionMap
namespace CurrentAFT.RootActualOutputPolynomial
end CurrentAFT.RootActualOutputPolynomial
namespace CurrentAFT.RootIndependentSelectedPhysical
end CurrentAFT.RootIndependentSelectedPhysical
namespace CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
end CurrentAFT.RootIndependentSelectedPhysical.empty_channel_average
namespace CurrentAFT.RootIndependentSelectedPhysical.meanLinear
end CurrentAFT.RootIndependentSelectedPhysical.meanLinear
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
end CurrentAFT.RootIndependentSelectedPhysical.normalizedActive
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedActive.match_1
end CurrentAFT.RootIndependentSelectedPhysical.normalizedActive.match_1
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint
end CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint.match_1
end CurrentAFT.RootIndependentSelectedPhysical.normalizedPoint.match_1
namespace CurrentAFT.RootIndependentSelectedPhysical.normalizedRole
end CurrentAFT.RootIndependentSelectedPhysical.normalizedRole
namespace CurrentAFT.TaggedOutputFock
end CurrentAFT.TaggedOutputFock
namespace CurrentAFT.TaggedOutputFock.outputMass
end CurrentAFT.TaggedOutputFock.outputMass
section
namespace CurrentAFT.ActualCompletePhysical
open AFT AFT.RepresentedPolynomial ActualBlockFock TaggedSelection ControlCoordinates
  LocalCoefficientFamily GradedControlAlgebra CycleRootExpansion ActualLayouts
  ActualRootDefectPhysical RootActualOutputPolynomial RootIndependentSelectedPhysical
  PhysicalPolynomialAverages LocalReferenceEnergy ActualFockBound ActualRootFamily
  ConditionalHistogramMean UniformTaggedOutput CompleteRaisingEvaluation ActualCycleMeanMGF
open scoped BigOperators Classical
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] _root_.CurrentAFT.ActualCompletePhysical.finDecEq
attribute [local instance] _root_.CurrentAFT.ActualCompletePhysical.sumDecEq
attribute [local instance] _root_.CurrentAFT.ActualCompletePhysical.vertexDecEq
attribute [local irreducible] Parameters.base Parameters.bodySize Parameters.dimension Parameters.legCount
set_option maxRecDepth 8192
theorem _root_.CurrentAFT.ActualCompletePhysical.__p2m_proof_4014a4a3ca35a499f5b5 {security r s : ℕ} (order : ℕ) (horder : 2 ≤ order) (hpositive : 1 ≤ order)
    (queue : ℤ) (selection : _root_.CurrentAFT.TaggedSelection.Selection security r s)
    (layout : _root_.CurrentAFT.ConditionalHistogramMean.RoleIndex security ≃ _root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)
    (kernel : _root_.CurrentAFT.ControlCoordinates.canonicalKernels (_root_.CurrentAFT.ProposalPrimary.primaryLaw security) (_root_.CurrentAFT.ActualControls.bodyReference security) r s) :
    _root_.CurrentAFT.TruncatedOutput.quotientMap order
      (_root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.uniform (Equiv.Perm (_root_.CurrentAFT.ActualCycleMeanMGF.BodyIndex security)))
        (fun permutation => _root_.AFT.RepresentedPolynomial.centeredGeneratingLinear (_root_.CurrentAFT.LocalReferenceEnergy.uniformReference security).weight
          (_root_.CurrentAFT.TaggedOutputFock.outputMass security r s selection layout queue permutation kernel.val))) =
      _root_.CurrentAFT.BackgroundEvaluation.evaluation security order
        (_root_.CurrentAFT.ActualBackground.fixedQueueBackground security order horder queue *
          (_root_.CurrentAFT.CompleteRaisingEvaluation.normalizedJoint security order hpositive kernel +
            _root_.CurrentAFT.ActualRootDefect.selectedDefect order hpositive queue selection (_root_.CurrentAFT.ActualLayouts.blockLayout layout) kernel)) := by
  rw [← _p2mH239]
  have hdef := _p2mH30 order horder queue selection (_root_.CurrentAFT.ActualLayouts.blockLayout layout) kernel
  have hind := _p2mH280 order (by omega) queue selection (_root_.CurrentAFT.ActualLayouts.blockLayout layout) kernel
  rw [mul_add, map_add, hdef, map_mul,
    _p2mH55, ← hind, map_sub]
  change _ = _root_.CurrentAFT.TruncatedOutput.quotientMap order
    (_root_.CurrentAFT.CycleRootExpansion.expectationLinear (_root_.AFT.FiniteDist.independent (fun _ : _root_.CurrentAFT.CycleRootExpansion.Vertex security => _root_.CurrentAFT.CycleRootExpansion.rootReference security))
      (_root_.CurrentAFT.ActualRootDefectPhysical.rootTest queue selection (_root_.CurrentAFT.ActualLayouts.blockLayout layout) kernel)) + _
  abel
end
end CurrentAFT.ActualCompletePhysical
end
set_option maxRecDepth 65536
theorem solution : (type_of% @_root_.CurrentAFT.ActualCompletePhysical.__p2m_proof_4014a4a3ca35a499f5b5) := @_root_.CurrentAFT.ActualCompletePhysical.__p2m_proof_4014a4a3ca35a499f5b5
