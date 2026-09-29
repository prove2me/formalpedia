-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5498fe14-8fd9-516a-8d88-9ffaf53b0f2c

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
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_nsmul_nMap_mem_eta_of_mem_eta_of_cast_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec MvFormalGroup.WittLaw.coe_frobIntPt"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld.FormalODModule

namespace ReduceE1

theorem map_smul_of_addMonoidHom {p : ℕ} [Fact p.Prime] {ι κ : Type} [Fintype ι] [Fintype κ]
    (T : (ι → ℤ_[p]) →+ (κ → ℤ_[p])) (c : ℤ_[p]) (v : ι → ℤ_[p]) : T (c • v) = c • T v := by
  funext i
  apply (PadicInt.ext_of_toZModPow).mp
  intro n
  obtain ⟨a, d, hd⟩ : ∃ (a : ℕ) (d : ℤ_[p]), c = (a : ℤ_[p]) + (p : ℤ_[p]) ^ n * d := by
    have h := PadicInt.appr_spec n c
    rw [Ideal.mem_span_singleton] at h
    obtain ⟨d, hd⟩ := h
    exact ⟨c.appr n, d, by linear_combination hd⟩
  have hT : ∀ (m : ℕ) (w : ι → ℤ_[p]), T ((m : ℤ_[p]) • w) = (m : ℤ_[p]) • T w := fun m w => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, map_nsmul]
  have key : T (c • v) i - (c • T v) i = (p : ℤ_[p]) ^ n * (T (d • v) i - d * T v i) := by
    have e1 : c • v = (a : ℤ_[p]) • v + ((p ^ n : ℕ) : ℤ_[p]) • (d • v) := by
      rw [hd, add_smul, smul_smul]; push_cast; rfl
    rw [e1, map_add, hT, hT, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, hd]
    push_cast
    simp only [smul_eq_mul]
    ring
  rw [← sub_eq_zero, ← RingHom.map_sub, key, ← RingHom.mem_ker, PadicInt.ker_toZModPow]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

noncomputable def toLinear {p : ℕ} [Fact p.Prime] {ι κ : Type} [Fintype ι] [Fintype κ]
    (T : (ι → ℤ_[p]) →+ (κ → ℤ_[p])) : (ι → ℤ_[p]) →ₗ[ℤ_[p]] (κ → ℤ_[p]) :=
  { toFun := T, map_add' := T.map_add, map_smul' := fun c v => map_smul_of_addMonoidHom T c v }

@[scoped simp] theorem toLinear_apply {p : ℕ} [Fact p.Prime] {ι κ : Type} [Fintype ι] [Fintype κ]
    (T : (ι → ℤ_[p]) →+ (κ → ℤ_[p])) (v : ι → ℤ_[p]) : toLinear T v = T v := rfl

theorem exists_ringHom_of_matrix {p : ℕ} [Fact p.Prime] {R : Type} [Ring R] {S : Subring R}
    (A : S → Matrix (Fin 2) (Fin 2) ℤ_[p])
    (A_one : A 1 = (p : ℤ_[p]) • 1)
    (A_mul : ∀ e e' : S, A e * A e' = (p : ℤ_[p]) • A (e * e'))
    (A_zero : A 0 = 0)
    (A_add : ∀ e e' : S, A (e + e') = A e + A e') :
    ∃ E : S →+* Matrix (Fin 2) (Fin 2) ℚ_[p],
      ∀ e, (p : ℚ_[p]) • E e = (A e).map ((↑) : ℤ_[p] → ℚ_[p]) := by
  have cQ_mul : ∀ M N : Matrix (Fin 2) (Fin 2) ℤ_[p],
      (M * N).map ((↑) : ℤ_[p] → ℚ_[p]) = M.map ((↑) : ℤ_[p] → ℚ_[p]) * N.map ((↑) : ℤ_[p] → ℚ_[p]) :=
    fun M N => by ext i j; simp [Matrix.mul_apply]
  have cQ_add : ∀ M N : Matrix (Fin 2) (Fin 2) ℤ_[p],
      (M + N).map ((↑) : ℤ_[p] → ℚ_[p]) = M.map ((↑) : ℤ_[p] → ℚ_[p]) + N.map ((↑) : ℤ_[p] → ℚ_[p]) :=
    fun M N => by ext i j; simp
  have cQ_smul : ∀ (c : ℤ_[p]) (M : Matrix (Fin 2) (Fin 2) ℤ_[p]),
      (c • M).map ((↑) : ℤ_[p] → ℚ_[p]) = (c : ℚ_[p]) • M.map ((↑) : ℤ_[p] → ℚ_[p]) :=
    fun c M => by ext i j; simp
  have cQ_one : (1 : Matrix (Fin 2) (Fin 2) ℤ_[p]).map ((↑) : ℤ_[p] → ℚ_[p]) = 1 := by simp
  have cQ_zero : (0 : Matrix (Fin 2) (Fin 2) ℤ_[p]).map ((↑) : ℤ_[p] → ℚ_[p]) = 0 := by simp
  have hp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hpp : ((p : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) := by norm_cast
  refine ⟨{ toFun := fun e => (p : ℚ_[p])⁻¹ • (A e).map ((↑) : ℤ_[p] → ℚ_[p])
            map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, fun e => ?_⟩
  · simp only [A_one, cQ_smul, cQ_one, smul_smul, hpp, inv_mul_cancel₀ hp, one_smul]
  · intro e e'
    simp only [Matrix.smul_mul, Matrix.mul_smul, ← cQ_mul, A_mul, cQ_smul, smul_smul, hpp,
      inv_mul_cancel₀ hp, mul_one]
  · simp only [A_zero, cQ_zero, smul_zero]
  · intro e e'
    simp only [A_add, cQ_add, smul_add]
  · show (p : ℚ_[p]) • ((p : ℚ_[p])⁻¹ • (A e).map ((↑) : ℤ_[p] → ℚ_[p])) = _
    rw [smul_smul, mul_inv_cancel₀ hp, one_smul]

theorem map_coe_injective {p : ℕ} [Fact p.Prime] :
    Function.Injective (fun A : Matrix (Fin 2) (Fin 2) ℤ_[p] => A.map ((↑) : ℤ_[p] → ℚ_[p])) :=
  fun A B h => Matrix.ext fun i j => PadicInt.ext (by simpa using congrFun (congrFun h i) j)

end ReduceE1
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq.ReduceE1"

set_option maxHeartbeats 3200000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
    (ι : Zp2 p →+* WittVector p k)
    (Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
    (hΦ : Φ.IsSpecial ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι)) (hΦ4 : Φ.HasHeight 4)
    (hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
    (hrΦ : ∀ (L : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).M →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
      (hL : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).IsCanonicalLMap L),
      Set.BijOn rΦ Set.univ ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).etaPiece L hL.isCartierLMap.map_verschiebung 0 : Set _)) :
    ∃ E : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) ℚ_[p],
      (∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod,
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2))))) ∧
      (∀ e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), ∃ A : Matrix (Fin 2) (Fin 2) ℤ_[p],
        (p : ℚ_[p]) • E e = A.map ((↑) : ℤ_[p] → ℚ_[p]) ∧
        ∀ (Ne : (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod),
          (∀ x : MvFormalGroup.CartierModule p Φ.F × (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).Sigma,
            Ne ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk x) =
              (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).nMk
                (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F) x.1,
                 (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).toSigma
                   (MvFormalGroup.CartierModule.endAct (e : MvFormalGroup.End Φ.F)
                     ((Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).ofSigma x.2)))) →
          ∀ w : Fin 2 → ℤ_[p], p • Ne (rΦ w) = rΦ (A.mulVec w)) := by
  classical

  let D := (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ)
  obtain ⟨L₀, hL₀⟩ := CerednikDrinfeld.FormalODModule.exists_isCanonicalLMap_toGradedCartierModuleData_of_isSpecial_of_isAlgClosed p k ι Φ hΦ hcΦ
  have hr : Set.BijOn rΦ Set.univ (D.etaPiece L₀ hL₀.isCartierLMap.map_verschiebung 0 : Set _) := hrΦ L₀ hL₀
  have rinj : Function.Injective rΦ := fun a b h => hr.injOn (Set.mem_univ a) (Set.mem_univ b) h
  have hp0 : (p : WittVector p k ⧸ pIdeal p (WittVector p k)) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (pIdeal p (WittVector p k))), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)

  have hVe : ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (x : D.M),
      (endAct (e : MvFormalGroup.End Φ.F) : D.M →+ D.M) (D.verschiebung x) = D.verschiebung ((endAct (e : MvFormalGroup.End Φ.F) : D.M →+ D.M) x) :=
    fun e x => endAct_verschiebungInt _ x
  have hPe : ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (x : D.M),
      (endAct (e : MvFormalGroup.End Φ.F) : D.M →+ D.M) (D.varpi x) = D.varpi ((endAct (e : MvFormalGroup.End Φ.F) : D.M →+ D.M) x) :=
    fun e x => by
      show endAct (e : MvFormalGroup.End Φ.F) (Φ.varpiLinear x) = Φ.varpiLinear (endAct (e : MvFormalGroup.End Φ.F) x)
      rw [varpiLinear_apply, varpiLinear_apply]
      exact endAct_varpiEnd_comm e.2 x
  have hFe : ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (x : D.M),
      (endAct (e : MvFormalGroup.End Φ.F) : D.M →+ D.M) (D.frobenius x) = D.frobenius ((endAct (e : MvFormalGroup.End Φ.F) : D.M →+ D.M) x) :=
    fun e x => endAct_frobenius _ x
  let Ne₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) → (D.NMod →+ D.NMod) := fun e => D.nMap D (endAct (e : MvFormalGroup.End Φ.F)) (hVe e) (hPe e)
  have pin : ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (x : MvFormalGroup.CartierModule p Φ.F × D.Sigma),
      Ne₀ e (D.nMk x) = D.nMk (endAct (e : MvFormalGroup.End Φ.F) x.1, D.toSigma (endAct (e : MvFormalGroup.End Φ.F) (D.ofSigma x.2))) :=
    fun e x => rfl
  have uniq : ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (Ne : D.NMod →+ D.NMod),
      (∀ x : MvFormalGroup.CartierModule p Φ.F × D.Sigma,
        Ne (D.nMk x) = D.nMk (endAct (e : MvFormalGroup.End Φ.F) x.1, D.toSigma (endAct (e : MvFormalGroup.End Φ.F) (D.ofSigma x.2)))) →
      Ne = Ne₀ e := fun e Ne h => by
    apply AddMonoidHom.ext
    intro z
    obtain ⟨x, rfl⟩ := D.nMk_surjective z
    exact (h x).trans (pin e x).symm

  have Ne_mul : ∀ e e' : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), Ne₀ (e * e') = (Ne₀ e).comp (Ne₀ e') := fun e e' => by
    apply AddMonoidHom.ext
    intro z
    obtain ⟨x, rfl⟩ := D.nMk_surjective z
    show Ne₀ (e * e') (D.nMk x) = Ne₀ e (Ne₀ e' (D.nMk x))
    rw [pin, pin, pin, Subring.coe_mul, map_mul]
    rfl
  have Ne_one : Ne₀ 1 = AddMonoidHom.id _ := by
    apply AddMonoidHom.ext
    intro z
    obtain ⟨x, rfl⟩ := D.nMk_surjective z
    rw [pin, OneMemClass.coe_one, map_one]
    rfl
  have Ne_add : ∀ e e' : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), Ne₀ (e + e') = Ne₀ e + Ne₀ e' := fun e e' => by
    apply AddMonoidHom.ext
    intro z
    obtain ⟨x, rfl⟩ := D.nMk_surjective z
    show Ne₀ (e + e') (D.nMk x) = Ne₀ e (D.nMk x) + Ne₀ e' (D.nMk x)
    rw [pin, pin, pin, ← map_add, Prod.mk_add_mk, Subring.coe_add, map_add]
    rfl

  let S : AddSubgroup D.NMod := D.etaPiece L₀ hL₀.isCartierLMap.map_verschiebung 0

  have stab : ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (z : D.NMod), z ∈ S → p • Ne₀ e z ∈ S := fun e z hz => by
    have hz' : z ∈ D.eta L₀ hL₀.isCartierLMap.map_verschiebung ⊓ D.nPiece 0 := hz
    refine (AddSubgroup.mem_inf.mpr ⟨?_, ?_⟩ : p • Ne₀ e z ∈ D.eta L₀ hL₀.isCartierLMap.map_verschiebung ⊓ D.nPiece 0)
    · exact CerednikDrinfeld.GradedCartierModuleData.nsmul_nMap_mem_eta_of_mem_eta_of_cast_eq_zero p hp0 D D (endAct (e : MvFormalGroup.End Φ.F)) (hFe e) (hVe e) (hPe e)
        L₀ hL₀.isCartierLMap L₀ hL₀.isCartierLMap z (AddSubgroup.mem_inf.mp hz').1
    · refine AddSubgroup.nsmul_mem _ ?_ p
      obtain ⟨⟨m, m'⟩, hmm, rfl⟩ := (AddSubgroup.mem_inf.mp hz').2
      refine ⟨(endAct (e : MvFormalGroup.End Φ.F) m, endAct (e : MvFormalGroup.End Φ.F) m'), ?_, rfl⟩
      obtain ⟨hm, hm'⟩ := hmm
      exact ⟨(Φ.mem_toGradedCartierModuleData_piece_iff _ hcΦ _ _).mpr
          (endAct_mem_gradedPiece _ e.2 _ ((Φ.mem_toGradedCartierModuleData_piece_iff _ hcΦ _ _).mp hm)),
        (Φ.mem_toGradedCartierModuleData_piece_iff _ hcΦ _ _).mpr
          (endAct_mem_gradedPiece _ e.2 _ ((Φ.mem_toGradedCartierModuleData_piece_iff _ hcΦ _ _).mp hm'))⟩

  let rinv : D.NMod → (Fin 2 → ℤ_[p]) := Function.invFunOn rΦ Set.univ
  have hrinv : ∀ z, z ∈ S → rΦ (rinv z) = z := fun z hz => hr.invOn_invFunOn.2 hz
  have hrmem : ∀ w, rΦ w ∈ S := fun w => hr.mapsTo (Set.mem_univ w)

  have Tadd : ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (w w' : Fin 2 → ℤ_[p]),
      rinv (p • Ne₀ e (rΦ (w + w'))) = rinv (p • Ne₀ e (rΦ w)) + rinv (p • Ne₀ e (rΦ w')) := fun e w w' => by
    apply rinj
    rw [hrinv (p • Ne₀ e (rΦ (w + w'))) (stab e _ (hrmem _)), map_add rΦ (rinv _) (rinv _),
      hrinv (p • Ne₀ e (rΦ w)) (stab e _ (hrmem _)), hrinv (p • Ne₀ e (rΦ w')) (stab e _ (hrmem _)),
      map_add, map_add, nsmul_add]
  let T : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) → ((Fin 2 → ℤ_[p]) →+ (Fin 2 → ℤ_[p])) := fun e =>
    { toFun := fun w => rinv (p • Ne₀ e (rΦ w))
      map_zero' := by
        apply rinj
        rw [hrinv _ (stab e _ (hrmem _)), map_zero, map_zero, nsmul_zero]
      map_add' := Tadd e }
  have hT : ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (w : Fin 2 → ℤ_[p]), rΦ (T e w) = p • Ne₀ e (rΦ w) :=
    fun e w => hrinv _ (stab e _ (hrmem _))

  let A : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) → Matrix (Fin 2) (Fin 2) ℤ_[p] := fun e => LinearMap.toMatrix' (ReduceE1.toLinear (T e))
  have hA : ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (w : Fin 2 → ℤ_[p]), (A e).mulVec w = T e w := fun e w => by
    show (LinearMap.toMatrix' (ReduceE1.toLinear (T e))).mulVec w = T e w
    rw [LinearMap.toMatrix'_mulVec]; rfl
  have hAT : ∀ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (w : Fin 2 → ℤ_[p]), rΦ ((A e).mulVec w) = p • Ne₀ e (rΦ w) :=
    fun e w => by rw [hA, hT]

  have A_mul : ∀ e e' : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), A e * A e' = (p : ℤ_[p]) • A (e * e') := fun e e' => by
    apply Matrix.toLin'.injective
    apply LinearMap.ext; intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec]
    apply rinj
    rw [hAT, hAT, map_nsmul (Ne₀ e), Nat.cast_smul_eq_nsmul, map_nsmul rΦ, hAT, Ne_mul]
    rfl
  have A_one : A 1 = (p : ℤ_[p]) • 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext; intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.smul_mulVec, Matrix.one_mulVec]
    apply rinj
    rw [hAT, Ne_one, AddMonoidHom.id_apply, Nat.cast_smul_eq_nsmul, map_nsmul rΦ]
  have A_add : ∀ e e' : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}), A (e + e') = A e + A e' := fun e e' => by
    apply Matrix.toLin'.injective
    apply LinearMap.ext; intro w
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.add_mulVec]
    apply rinj
    rw [hAT, map_add rΦ, hAT, hAT, Ne_add, AddMonoidHom.add_apply, nsmul_add]
  have A_zero : A 0 = 0 := by
    have h := A_add 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  clear_value A
  obtain ⟨E, hE⟩ := ReduceE1.exists_ringHom_of_matrix A A_one A_mul A_zero A_add
  refine ⟨E, fun e => ⟨Ne₀ e, pin e⟩, fun e => ⟨A e, ?_, fun Ne hNe' w => ?_⟩⟩
  · exact hE e
  · rw [uniq e Ne hNe', ← hAT]

#print axioms solution

end S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_ringHom_centralizer_matrix_smul_eq_map_and_nsmul_apply_rigidification_eq (solution)
