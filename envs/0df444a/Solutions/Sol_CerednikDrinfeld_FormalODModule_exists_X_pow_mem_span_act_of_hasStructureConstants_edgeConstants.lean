-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/a6ad82e0-cd15-5231-83f5-d900d1fcae68

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings
import Definitions.Def_CerednikDrinfeld_EdgeFamilyConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants
p2m_attr_erase "instance" "CerednikDrinfeld.GradedCartierModuleData.module CerednikDrinfeld.GradedCartierModuleData.addCommGroup CerednikDrinfeld.GradedCartierModuleData.instModuleWittVectorSigma CerednikDrinfeld.GradedCartierModuleData.instAddCommGroupSigma MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "CerednikDrinfeld.FormalODModule.mem_toGradedCartierModuleData_piece_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_homothety_apply CerednikDrinfeld.FormalODModule.mem_gradedSubmodule_iff CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_frobenius_apply CerednikDrinfeld.FormalODModule.varpiLinear_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_varpi_apply CerednikDrinfeld.FormalODModule.toGradedCartierModuleData_verschiebung_apply CerednikDrinfeld.FormalODModule.gradedSubmodule_toAddSubgroup MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal MvFormalGroup MvFormalGroup.CartierModule

open scoped PadicInt Padic

universe u

namespace NilpEdgeReduce

p2m_open "CerednikDrinfeld.FormalODModule"

variable {p : ℕ} [hp : Fact p.Prime]

theorem frobenius_teichmuller (c : GaloisField p 2) :
    WittVector.frobenius (WittVector.teichmuller p c) = WittVector.teichmuller p (c ^ p) := by
  ext n
  rw [WittVector.coeff_frobenius_charP]
  cases n with
  | zero => rw [WittVector.teichmuller_coeff_zero, WittVector.teichmuller_coeff_zero]
  | succ n =>
    rw [WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n),
      WittVector.teichmuller_coeff_pos p _ _ (Nat.succ_pos n), zero_pow hp.out.ne_zero]

theorem mem_gradedPiece_comp_frobenius_iff {B : Type u} [CommRing B] (X : FormalODModule p B)
    (j : Zp2 p →+* B) (n : ℕ) (f : CartierModule p X.F) :
    f ∈ X.gradedPiece (j.comp (WittVector.frobenius (p := p) (R := GaloisField p 2))) n ↔
      f ∈ X.gradedPiece j (n + 1) := by
  simp only [mem_gradedPiece_iff, RingHom.comp_apply, frobenius_teichmuller, map_pow, ← pow_mul]
  constructor <;> intro h c <;> rw [h c] <;> congr 2 <;> ring

theorem rev_piIndex (m : ℕ) (i : Fin 2) : (piIndex m i).rev = piIndex m i.rev := by
  ext
  simp only [Fin.val_rev, piIndex_val]
  have hi := i.isLt
  omega

theorem edgeConstants_swap {R : Type u} [CommRing R] (ξ η : R) (m : ℕ) (i : Fin 2) :
    EdgeFamily.edgeConstants p η ξ m i = EdgeFamily.edgeConstants p ξ η m i.rev := by
  fin_cases i <;> simp [EdgeFamily.edgeConstants]

theorem isHomogeneousVBasis_rev {B : Type u} [CommRing B] (X : FormalODModule p B)
    (j : Zp2 p →+* B) (γ : Fin 2 → CartierModule p X.F) (h : X.IsHomogeneousVBasis j γ) :
    X.IsHomogeneousVBasis (j.comp (WittVector.frobenius (p := p) (R := GaloisField p 2)))
      (fun i => γ i.rev) := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [mem_gradedPiece_comp_frobenius_iff]
    fin_cases i
    · exact h.1 1
    · show γ 0 ∈ X.gradedPiece j (0 + 2)
      rw [gradedPiece_add_two]
      exact h.1 0
  · have hdet : (Matrix.of fun i k => tangent (γ (Fin.rev i)) k).det =
        -(Matrix.of fun i k => tangent (γ i) k).det := by
      rw [Matrix.det_fin_two, Matrix.det_fin_two]
      simp only [Matrix.of_apply]
      show tangent (γ (Fin.rev 0)) 0 * tangent (γ (Fin.rev 1)) 1 -
          tangent (γ (Fin.rev 0)) 1 * tangent (γ (Fin.rev 1)) 0 = _
      have h0 : (Fin.rev 0 : Fin 2) = 1 := rfl
      have h1 : (Fin.rev 1 : Fin 2) = 0 := rfl
      rw [h0, h1]
      ring
    rw [hdet]
    exact h.2.neg

theorem hasStructureConstants_rev {B : Type u} [CommRing B] (X : FormalODModule p B)
    (γ : Fin 2 → CartierModule p X.F) (ξ η : B)
    (h : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ η)) :
    X.HasStructureConstants (fun i => γ i.rev) (EdgeFamily.edgeConstants p η ξ) := by
  intro i N
  obtain ⟨r, hr⟩ := h i.rev N
  refine ⟨r, ?_⟩
  rw [hr]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [rev_piIndex, edgeConstants_swap ξ η (m : ℕ) i]

theorem branch {R : Type} [CommRing R] [IsNoetherianRing R] [CharP R p] (j : Zp2 p →+* R)
    (ξ η : R) (hη : η = 0) (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis j γ) (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ η)) :
    ∃ N : ℕ, ∀ i : Fin 2,
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N ∈ Ideal.span (Set.range (X.act (p : Zp2 p))) := by
  subst hη
  exact CerednikDrinfeld.FormalODModule.exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants_zero
    p j ξ X γ hγ ha

theorem branch_swap {R : Type} [CommRing R] [IsNoetherianRing R] [CharP R p] (j : Zp2 p →+* R)
    (ξ η : R) (hξ : ξ = 0) (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis j γ) (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ η)) :
    ∃ N : ℕ, ∀ i : Fin 2,
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N ∈ Ideal.span (Set.range (X.act (p : Zp2 p))) :=
  branch _ η ξ hξ X (fun i => γ i.rev) (isHomogeneousVBasis_rev X j γ hγ)
    (hasStructureConstants_rev X γ ξ η ha)

theorem charP_quotient_of_not_isUnit {R : Type} [CommRing R] [CharP R p] (η : R) (hη : ¬ IsUnit η) :
    CharP (R ⧸ Ideal.span ({η} : Set R)) p := by
  refine CharP.quotient' p _ fun x hx => ?_
  by_cases hdvd : p ∣ x
  · exact (CharP.cast_eq_zero_iff R p x).mpr hdvd
  · exfalso
    apply hη
    have hu : IsUnit (x : R) := by
      have hz : IsUnit ((x : ZMod p)) := by
        rw [isUnit_iff_ne_zero, Ne, ZMod.natCast_eq_zero_iff]
        exact hdvd
      have := hz.map (ZMod.castHom (dvd_refl p) R)
      rwa [map_natCast] at this
    have htop : Ideal.span ({η} : Set R) = ⊤ :=
      Ideal.eq_top_of_isUnit_mem _ hx hu
    exact Ideal.span_singleton_eq_top.mp htop

theorem exists_eq_smul_of_map_eq_zero {R : Type} [CommRing R] (η : R)
    (f : MvPowerSeries (Fin 2) R)
    (hf : MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span ({η} : Set R))) f = 0) :
    ∃ g : MvPowerSeries (Fin 2) R, f = η • g := by
  have hc : ∀ n : Fin 2 →₀ ℕ, ∃ c : R, c * η = MvPowerSeries.coeff n f := by
    intro n
    have h := congrArg (MvPowerSeries.coeff n) hf
    rw [MvPowerSeries.coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem] at h
    exact Ideal.mem_span_singleton'.mp h
  choose c hc' using hc
  refine ⟨fun n => c n, MvPowerSeries.ext fun n => ?_⟩
  show MvPowerSeries.coeff n f = η * c n
  rw [mul_comm]
  exact (hc' n).symm

theorem exists_mem_add_smul_of_map_mem {R : Type} [CommRing R] (η : R) (φ : Series R)
    (F : MvPowerSeries (Fin 2) R)
    (h : MvPowerSeries.map (Ideal.Quotient.mk (Ideal.span ({η} : Set R))) F ∈
      Ideal.span (Set.range (φ.map (Ideal.Quotient.mk (Ideal.span ({η} : Set R)))))) :
    ∃ a ∈ Ideal.span (Set.range φ), ∃ g : MvPowerSeries (Fin 2) R, F = a + η • g := by
  classical
  set mk := Ideal.Quotient.mk (Ideal.span ({η} : Set R)) with hmk
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h

  have hlift : ∀ i : Fin 2, ∃ c' : MvPowerSeries (Fin 2) R, MvPowerSeries.map mk c' = c i := by
    intro i
    have hs : ∀ n : Fin 2 →₀ ℕ, ∃ r : R, mk r = MvPowerSeries.coeff n (c i) :=
      fun n => Ideal.Quotient.mk_surjective _
    choose r hr using hs
    refine ⟨fun n => r n, ?_⟩
    ext n
    rw [MvPowerSeries.coeff_map]
    exact hr n
  choose c' hc' using hlift
  have hzero : MvPowerSeries.map mk (F - ∑ i, c' i * φ i) = 0 := by
    rw [map_sub, map_sum, sub_eq_zero, ← hc]
    refine (Finset.sum_congr rfl fun i _ => ?_).symm
    rw [map_mul, hc' i]
    rfl
  obtain ⟨g, hg⟩ := exists_eq_smul_of_map_eq_zero η _ hzero
  refine ⟨∑ i, c' i * φ i, ?_, g, ?_⟩
  · exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · rw [← hg]; ring

theorem exists_mem_add_smul {R : Type} [CommRing R] [IsNoetherianRing R] [CharP R p]
    (j : Zp2 p →+* R) (ξ η : R) (hηu : ¬ IsUnit η)
    (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F)
    (hγ : X.IsHomogeneousVBasis j γ) (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ η)) :
    ∃ N : ℕ, ∀ i : Fin 2, ∃ a ∈ Ideal.span (Set.range (X.act (p : Zp2 p))), ∃ g : MvPowerSeries (Fin 2) R,
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N = a + η • g := by
  haveI : CharP (R ⧸ Ideal.span ({η} : Set R)) p := charP_quotient_of_not_isUnit η hηu
  set f := Ideal.Quotient.mk (Ideal.span ({η} : Set R)) with hf
  have hfη : f η = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self η)
  have hγ' := hγ.map f
  have ha' : (X.map f).HasStructureConstants (fun i => baseChange f (γ i))
      (EdgeFamily.edgeConstants p (f ξ) (f η)) := by
    have h := ha.map f
    have heq : (fun m i => f (EdgeFamily.edgeConstants p ξ η m i)) =
        EdgeFamily.edgeConstants p (f ξ) (f η) := by
      funext m i
      exact EdgeFamily.edgeConstants_map f ξ η m i
    rwa [heq] at h
  obtain ⟨N, hN⟩ := branch (f.comp j) (f ξ) (f η) hfη (X.map f) _ hγ' ha'
  refine ⟨N, fun i => ?_⟩
  have hmem : MvPowerSeries.map f ((MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N) ∈
      Ideal.span (Set.range ((X.act (p : Zp2 p)).map f)) := by
    rw [map_pow, MvPowerSeries.map_X]
    exact hN i
  exact exists_mem_add_smul_of_map_mem η (X.act (p : Zp2 p)) _ hmem

end NilpEdgeReduce

open NilpEdgeReduce in
theorem solution
    (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] [IsNoetherianRing R] [CharP R p] (j : Zp2 p →+* R)
    (ξ η : R) (hξη : ξ * η = 0)
    (X : FormalODModule p R) (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (ha : X.HasStructureConstants γ (EdgeFamily.edgeConstants p ξ η)) :
    ∃ N : ℕ, ∀ i : Fin 2,
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) ^ N ∈ Ideal.span (Set.range (X.act (p : Zp2 p))) := by
  by_cases hηu : IsUnit η
  ·
    have hξ : ξ = 0 := by
      obtain ⟨u, rfl⟩ := hηu
      have := congrArg (· * (↑u⁻¹ : R)) hξη
      simpa using this
    exact branch_swap j ξ η hξ X γ hγ ha
  by_cases hξu : IsUnit ξ
  · have hη : η = 0 := by
      obtain ⟨u, rfl⟩ := hξu
      have := congrArg ((↑u⁻¹ : R) * ·) hξη
      simpa using this
    exact branch j ξ η hη X γ hγ ha

  obtain ⟨N, hN⟩ := exists_mem_add_smul j ξ η hηu X γ hγ ha
  obtain ⟨M, hM⟩ := exists_mem_add_smul (j.comp (WittVector.frobenius (p := p) (R := GaloisField p 2)))
    η ξ hξu X (fun i => γ i.rev) (isHomogeneousVBasis_rev X j γ hγ) (hasStructureConstants_rev X γ ξ η ha)
  refine ⟨N + M, fun i => ?_⟩
  obtain ⟨a, haI, g, hg⟩ := hN i
  obtain ⟨b, hbI, h, hh⟩ := hM i
  rw [pow_add, hg, hh]
  have key : (a + η • g) * (b + ξ • h) = a * (b + ξ • h) + b * (η • g) + (ξ * η) • (g * h) := by
    simp only [Algebra.smul_def, map_mul]
    ring
  rw [key, hξη, zero_smul, add_zero]
  exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ haI) (Ideal.mul_mem_right _ _ hbI)

end S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_X_pow_mem_span_act_of_hasStructureConstants_edgeConstants (solution)
