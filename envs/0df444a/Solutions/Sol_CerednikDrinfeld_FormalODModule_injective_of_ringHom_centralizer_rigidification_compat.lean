-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.injective_of_ringHom_centralizer_rigidification_compat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c3b8a5d4-7d3d-58a7-a416-610060ba4107

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_CerednikDrinfeld_PeriodMap
import Definitions.Def_CerednikDrinfeld_CritChartEndMatrix
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed
import Theorems.Thm_CerednikDrinfeld_FormalODModule_eq_zero_of_endAct_varpiEnd_eq_zero_of_isSpecial_of_hasHeight
import Theorems.Thm_MvFormalGroup_CartierModule_eq_of_forall_map_eq_of_algebra_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_injective_of_ringHom_centralizer_rigidification_compat
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

p2m_open "MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.FormalODModule~NMod"

namespace ReduceE2a

theorem map_coe_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (fun A : Matrix (Fin 2) (Fin 2) ℤ_[p] => A.map ((↑) : ℤ_[p] → ℚ_[p])) :=
  fun A B h => Matrix.ext fun i j => PadicInt.ext (by simpa using congrFun (congrFun h i) j)

end ReduceE2a

theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _))
    (E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p])
    (hNe : ∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))))
    (hE : ∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p],
        (p : ℚ_[p]) • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) ∧
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p • Ne (rΦ w) = rΦ (A.mulVec w)) :
    Function.Injective E := by
  classical
  intro e e' hEe
  let D := (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ)

  have hPi : ∀ m : CartierModule p Φ.F, endAct Φ.varpiEnd m = 0 → m = 0 :=
    fun m hm => CerednikDrinfeld.FormalODModule.eq_zero_of_endAct_varpiEnd_eq_zero_of_isSpecial_of_hasHeight p k ι Φ hΦ hΦ4 m hm
  have hp1 : ∀ m : CartierModule p Φ.F, p • m = 0 → m = 0 := fun m hm => by
    apply hPi; apply hPi
    rw [endAct_varpiEnd_endAct_varpiEnd]; exact hm
  have hpn : ∀ (n : ℕ) (m : CartierModule p Φ.F), p ^ n • m = 0 → m = 0 := by
    intro n; induction n with
    | zero => intro m hm; simpa using hm
    | succ n ih => intro m hm; rw [pow_succ, mul_smul] at hm; exact hp1 m (ih _ hm)

  have hker : ∀ y : CartierModule p Φ.F, D.nMk (y, 0) = 0 → y = 0 := by
    intro y hy
    rw [GradedCartierModuleData.nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy
    obtain ⟨t, ht⟩ := hy
    have h1 : D.verschiebung (D.ofSigma t) = y := congrArg Prod.fst ht
    have h2 : D.toSigma (-D.varpi (D.ofSigma t)) = D.toSigma 0 := congrArg Prod.snd ht
    have h3 : D.varpi (D.ofSigma t) = 0 := by
      have := congrArg D.ofSigma h2
      simp only [GradedCartierModuleData.ofSigma_toSigma, neg_eq_zero] at this
      exact this
    have h4 : D.ofSigma t = 0 := hPi _ (by
      rw [← varpiLinear_apply]; exact h3)
    rw [← h1, h4]; exact map_zero _

  obtain ⟨A, hA, hcomp⟩ := hE e
  obtain ⟨A', hA', hcomp'⟩ := hE e'
  have hAA : A = A' := ReduceE2a.map_coe_injective (by show A.map _ = A'.map _; rw [← hA, ← hA', hEe])
  obtain ⟨Ne, hNe1⟩ := hNe e
  obtain ⟨Ne', hNe1'⟩ := hNe e'
  have key : ∀ w, p • Ne (rΦ w) = p • Ne' (rΦ w) := fun w => by
    rw [hcomp Ne hNe1 w, hcomp' Ne' hNe1' w, hAA]

  have hgmem : ((e : MvFormalGroup.End Φ.F) - (e' : MvFormalGroup.End Φ.F)) ∈ Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) :=
    Subring.sub_mem _ e.2 e'.2
  set g : MvFormalGroup.End Φ.F := (e : MvFormalGroup.End Φ.F) - (e' : MvFormalGroup.End Φ.F) with hgdef
  have hVg : ∀ x : D.M, (endAct g : D.M →+ D.M) (D.verschiebung x) = D.verschiebung ((endAct g : D.M →+ D.M) x) :=
    fun x => endAct_verschiebungInt _ x
  have hPg : ∀ x : D.M, (endAct g : D.M →+ D.M) (D.varpi x) = D.varpi ((endAct g : D.M →+ D.M) x) := fun x => by
    show endAct g (Φ.varpiLinear x) = Φ.varpiLinear (endAct g x)
    rw [varpiLinear_apply, varpiLinear_apply]
    exact endAct_varpiEnd_comm hgmem x
  let Ng : D.NMod →+ D.NMod := D.nMap D (endAct g) hVg hPg
  have pinG : ∀ x : CartierModule p Φ.F × D.Sigma, Ng (D.nMk x) = Ne (D.nMk x) - Ne' (D.nMk x) := fun x => by
    rw [hNe1 x, hNe1' x, ← map_sub]
    show D.nMk (endAct g x.1, D.toSigma (endAct g (D.ofSigma x.2))) = _
    rw [hgdef, map_sub]
    rfl
  have hNg : ∀ z, Ng z = Ne z - Ne' z := fun z => by
    obtain ⟨x, rfl⟩ := D.nMk_surjective z; exact pinG x
  have hNg0 : ∀ w, p • Ng (rΦ w) = 0 := fun w => by rw [hNg, nsmul_sub, key, sub_self]

  have Ng_smul : ∀ (c : WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) (z : D.NMod), Ng (c • z) = c • Ng z := by
    intro c z
    obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
    rw [GradedCartierModuleData.smul_nMk]
    show D.nMk (endAct g (c • m), endAct g (WittVector.frobenius c • m')) = c • D.nMk (endAct g m, endAct g m')
    rw [GradedCartierModuleData.smul_nMk]
    exact congrArg D.nMk (Prod.ext (endAct_smul_witt g c m) (endAct_smul_witt g _ m'))
  have Ng_varpi : ∀ z : D.NMod, Ng (D.nVarpi z) = D.nVarpi (Ng z) := by
    intro z
    obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
    show D.nMk (endAct g (D.varpi m), endAct g (D.varpi m')) = D.nMk (D.varpi (endAct g m), D.varpi (endAct g m'))
    rw [show endAct g (D.varpi m) = D.varpi (endAct g m) from hPg m,
      show endAct g (D.varpi m') = D.varpi (endAct g m') from hPg m']

  obtain ⟨a, hK⟩ := CerednikDrinfeld.FormalODModule.exists_pow_smul_eq_sum_smul_add_sum_smul_nVarpi_of_bijOn_etaPiece_zero_of_isAlgClosed p k ι Φ hΦ hΦ4 hcΦ rΦ hrΦ
  have hkill : ∀ z : D.NMod, p ^ (a + 1) • Ng z = 0 := by
    intro z
    obtain ⟨c, d, hz⟩ := hK z
    have hz' : Ng (p ^ a • z) = (∑ i, c i • Ng (rΦ (Pi.single i 1))) + ∑ i, d i • D.nVarpi (Ng (rΦ (Pi.single i 1))) := by
      rw [hz, map_add, map_sum, map_sum]
      congr 1
      · exact Finset.sum_congr rfl fun i _ => Ng_smul _ _
      · exact Finset.sum_congr rfl fun i _ => (Ng_smul _ _).trans (congrArg (d i • ·) (Ng_varpi _))
    have h1 : ∀ i, (p : WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) • Ng (rΦ (Pi.single i 1)) = 0 :=
      fun i => by rw [Nat.cast_smul_eq_nsmul]; exact hNg0 _
    have h1' : ∀ i, (p : WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) • (c i • Ng (rΦ (Pi.single i 1))) = 0 :=
      fun i => by rw [smul_comm, h1, smul_zero]
    have h2' : ∀ i, (p : WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))) • (d i • D.nVarpi (Ng (rΦ (Pi.single i 1)))) = 0 :=
      fun i => by rw [smul_comm, ← LinearMap.map_smul, h1, map_zero, smul_zero]
    rw [pow_succ', mul_smul, ← map_nsmul, hz',
      ← Nat.cast_smul_eq_nsmul (WittVector p (WittVector p k ⧸ pIdeal p (WittVector p k))), smul_add,
      Finset.smul_sum, Finset.smul_sum]
    simp only [h1', h2', Finset.sum_const_zero, add_zero]

  have hprod : ∀ (n : ℕ) (x : CartierModule p Φ.F), n • ((x, 0) : CartierModule p Φ.F × D.Sigma) = (n • x, 0) :=
    fun n x => by refine Prod.ext ?_ ?_ <;> simp
  have hg0 : ∀ m : CartierModule p Φ.F, endAct g m = 0 := by
    intro m
    have h := hkill (D.nMk ((m, 0) : CartierModule p Φ.F × D.Sigma))
    have e1 : Ng (D.nMk ((m, 0) : CartierModule p Φ.F × D.Sigma)) = D.nMk ((endAct g m, 0) : CartierModule p Φ.F × D.Sigma) := by
      show D.nMk (endAct g m, D.toSigma (endAct g (D.ofSigma 0))) = D.nMk ((endAct g m, 0) : CartierModule p Φ.F × D.Sigma)
      exact congrArg D.nMk (Prod.ext rfl (by
        show D.toSigma (endAct g (0 : CartierModule p Φ.F)) = (0 : CartierModule p Φ.F)
        rw [map_zero (endAct g)]; rfl))
    rw [e1] at h
    have h2 : D.nMk ((p ^ (a + 1) • endAct g m, 0) : CartierModule p Φ.F × D.Sigma) = 0 := by
      have := (map_nsmul D.nMk (p ^ (a + 1)) ((endAct g m, 0) : CartierModule p Φ.F × D.Sigma)).trans h
      simp at this
      exact this
    exact hpn _ _ (hker _ h2)

  letI : Algebra ℤ_[p] (WittVector p k ⧸ pIdeal p (WittVector p k)) :=
    ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp
      ((WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom)).toAlgebra
  have hg : g = 0 := MvFormalGroup.CartierModule.eq_of_forall_map_eq_of_algebra_padicInt p Φ.F Φ.F g 0 (fun f => by
    rw [map_zero_hom]; exact hg0 f)
  apply Subtype.ext
  exact sub_eq_zero.mp hg

#print axioms solution

end S_CerednikDrinfeld_FormalODModule_injective_of_ringHom_centralizer_rigidification_compat
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_injective_of_ringHom_centralizer_rigidification_compat (solution)
