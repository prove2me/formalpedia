-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/fd2ba752-02da-51e0-865d-1e2b3f5485b5

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Theorems.Thm_CerednikDrinfeld_FormalODModule_exists_digits_tangent_eq_and_fst_snd_eq_of_varpiEnd_eq_verschiebungInt_of_hasStructureConstants_dualNumber
import Theorems.Thm_CerednikDrinfeld_FormalODModule_mem_etaPiece_iff_exists_varpiEnd_eq_verschiebungInt_of_charP
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvPowerSeries.blockPermEmbed_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

namespace C2PLineReads

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]

theorem smul_row_injective {n : Type} [Fintype n] [DecidableEq n]
    (T : Matrix n n B) (hT : IsUnit T.det)
    (i : n) (x y : B) (h : x • T i = y • T i) : x = y := by
  have hTu : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).mpr hT
  obtain ⟨u, hu⟩ := hTu
  have key : ∀ v : n → B, Matrix.vecMul (Matrix.vecMul v T) (↑u⁻¹ : Matrix n n B) = v := by
    intro v
    rw [Matrix.vecMul_vecMul, ← hu, Units.mul_inv, Matrix.vecMul_one]
  have hrow : ∀ w : B, Matrix.vecMul (Pi.single i w) T = w • T i := by
    intro w
    rw [Matrix.single_vecMul]
    rfl
  have h1 : Matrix.vecMul (Pi.single i x) T = Matrix.vecMul (Pi.single i y) T := by
    rw [hrow, hrow, h]
  have h2 : (Pi.single i x : n → B) = Pi.single i y := by
    rw [← key (Pi.single i x), h1, key]
  have h3 := congrFun h2 i
  rwa [Pi.single_eq_same, Pi.single_eq_same] at h3

theorem tangent_sum_homothety {d : ℕ} {Φ : MvFormalGroup d B} [Φ.IsComm]
    {ι : Type} [Fintype ι] (c : ι → B) (e : ι → CartierModule p Φ) :
    tangent (∑ i, homothety (c i) (e i)) = Matrix.vecMul c (Matrix.of fun i k => tangent (e i) k) := by
  rw [map_sum]
  funext k
  simp only [Finset.sum_apply, tangent_homothety, Pi.smul_apply, smul_eq_mul, Matrix.vecMul,
    Matrix.of_apply]
  rfl

theorem exists_verschiebungInt_eq_varpi (j : Zp2 p →+* B)
    (X : FormalODModule p B) (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hker : ∀ f : CartierModule p X.F, tangent f = 0 ↔ ∃ g : CartierModule p X.F, verschiebungInt g = f)
    (i₀ : Fin 2) (h : CartierModule p X.F) (hPi : endAct X.varpiEnd (γ i₀) = verschiebungInt h)
    (m : CartierModule p X.F) (hm : m ∈ X.gradedPiece j (i₀ : ℕ)) :
    ∃ g : CartierModule p X.F, verschiebungInt g = endAct X.varpiEnd m := by
  classical

  have h10 : i₀ + 1 + 1 = i₀ := by fin_cases i₀ <;> rfl
  have hhom : ∀ (a : B) (n : ℕ) (f : CartierModule p X.F), f ∈ X.gradedPiece j n →
      homothety a f ∈ X.gradedPiece j n := fun a n f hf => by
    rw [← teichmuller_smul]; exact FormalODModule.smul_mem_gradedPiece X j n _ f hf
  have hV1 : ∀ (i : Fin 2) (f : CartierModule p X.F), f ∈ X.gradedPiece j (i : ℕ) →
      verschiebungInt f ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ) :=
    fun i f hf => (X.toGradedCartierModuleData j hc).verschiebung_mem i f hf
  have hP1 : ∀ (i : Fin 2) (f : CartierModule p X.F), f ∈ X.gradedPiece j (i : ℕ) →
      endAct X.varpiEnd f ∈ X.gradedPiece j ((i + 1 : Fin 2) : ℕ) :=
    fun i f hf => (X.toGradedCartierModuleData j hc).varpi_mem i f hf
  have hdisj : ∀ q : CartierModule p X.F, q ∈ X.gradedPiece j (i₀ : ℕ) →
      q ∈ X.gradedPiece j ((i₀ + 1 : Fin 2) : ℕ) → q = 0 := by
    intro q h1 h2
    have hq : q ∈ X.gradedPiece j 0 ⊓ X.gradedPiece j 1 := by
      fin_cases i₀
      · exact AddSubgroup.mem_inf.2 ⟨h1, h2⟩
      · exact AddSubgroup.mem_inf.2 ⟨h2, h1⟩
    rwa [hc.inf_eq_bot, AddSubgroup.mem_bot] at hq
  have hsum : ∀ f : Fin 2 → CartierModule p X.F, ∑ i, f i = f i₀ + f (i₀ + 1) := by
    intro f
    fin_cases i₀
    · simp [Fin.sum_univ_two]
    · simp [Fin.sum_univ_two, add_comm]

  set T : Matrix (Fin 2) (Fin 2) B := Matrix.of fun i k => tangent (γ i) k with hT
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det T).mpr hγ.2
  set c : Fin 2 → B := Matrix.vecMul (tangent m) (↑u⁻¹ : Matrix (Fin 2) (Fin 2) B) with hcdef
  have hcT : Matrix.vecMul c T = tangent m := by
    rw [hcdef, Matrix.vecMul_vecMul, ← hu, Units.inv_mul, Matrix.vecMul_one]
  have h0 : tangent (m - ∑ i, homothety (c i) (γ i)) = 0 := by
    rw [map_sub, tangent_sum_homothety, hcT, sub_self]
  obtain ⟨y, hy⟩ := (hker _).1 h0

  obtain ⟨ya, hya, yb, hyb, hyab⟩ : ∃ ya ∈ X.gradedPiece j (i₀ : ℕ),
      ∃ yb ∈ X.gradedPiece j ((i₀ + 1 : Fin 2) : ℕ), ya + yb = y := by
    have hy' : y ∈ X.gradedPiece j 0 ⊔ X.gradedPiece j 1 := by
      rw [hc.sup_eq_top]; exact AddSubgroup.mem_top y
    obtain ⟨y0, hy0, y1, hy1, rfl⟩ := AddSubgroup.mem_sup.1 hy'
    fin_cases i₀
    · exact ⟨y0, hy0, y1, hy1, rfl⟩
    · exact ⟨y1, hy1, y0, hy0, add_comm _ _⟩

  set r : CartierModule p X.F := homothety (c i₀) (γ i₀) + verschiebungInt yb with hr
  set q : CartierModule p X.F := homothety (c (i₀ + 1)) (γ (i₀ + 1)) + verschiebungInt ya with hq
  have hmrq : m = r + q := by
    have : m = (∑ i, homothety (c i) (γ i)) + verschiebungInt y := by
      rw [hy]; abel
    rw [this, hsum, ← hyab, map_add, hr, hq]
    abel
  have hr_mem : r ∈ X.gradedPiece j (i₀ : ℕ) := by
    refine (X.gradedPiece j (i₀ : ℕ)).add_mem (hhom _ _ _ (hγ.1 i₀)) ?_
    have := hV1 (i₀ + 1) yb hyb
    rwa [h10] at this
  have hq_mem : q ∈ X.gradedPiece j ((i₀ + 1 : Fin 2) : ℕ) :=
    (X.gradedPiece j _).add_mem (hhom _ _ _ (hγ.1 (i₀ + 1))) (hV1 i₀ ya hya)
  have hq0 : q = 0 := by
    refine hdisj q ?_ hq_mem
    have : q = m - r := by rw [hmrq]; abel
    rw [this]
    exact (X.gradedPiece j _).sub_mem hm hr_mem
  have hmr : m = r := by rw [hmrq, hq0, add_zero]
  refine ⟨homothety (c i₀ ^ p) h + endAct X.varpiEnd yb, ?_⟩
  rw [hmr, hr, map_add, map_add, endAct_homothety, hPi, homothety_verschiebungInt,
    endAct_verschiebungInt]

end C2PLineReads

theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p]
    (j : Zp2 p →+* DualNumber κ) (X : FormalODModule p (DualNumber κ))
    (γ : Fin 2 → CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (a ν : ℕ → Fin 2 → κ) (c : κ)
    (hA : X.HasStructureConstants γ (fun m i => algebraMap κ (DualNumber κ) (a m i) + (c * ν m i) • DualNumber.eps))
    (hν0 : ∀ i, ν 0 i = 0) (i₀ : Fin 2) (ha0 : a 0 i₀ = 0)
    (L : (X.toGradedCartierModuleData j hc).M →+
      (X.toGradedCartierModuleData j hc).NMod)
    (hL : (X.toGradedCartierModuleData j hc).IsCanonicalLMap L)
    (z : (X.toGradedCartierModuleData j hc).NMod)
    (hz : z ∈ (X.toGradedCartierModuleData j hc).etaPiece L
      hL.isCartierLMap.map_verschiebung i₀)
    (m : CartierModule p X.F)
    (hm : (X.toGradedCartierModuleData j hc).vRange.mkQ m =
      (X.toGradedCartierModuleData j hc).u L
        hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz).1⟩) :
    (∃ x : DualNumber κ, tangent m = x • tangent (γ i₀)) ∧
    ∀ x : DualNumber κ, tangent m = x • tangent (γ i₀) →
      a 0 (FormalODModule.piIndex 0 i₀) ^ p * TrivSqZeroExt.fst x =
        (a 0 (FormalODModule.piIndex 0 i₀) ^ p * a 1 i₀ + a 0 (FormalODModule.piIndex 0 i₀) * a 1 (FormalODModule.piIndex 0 i₀)) *
            TrivSqZeroExt.fst x ^ p +
        (a 0 (FormalODModule.piIndex 0 i₀) ^ (p + 1) * a 2 i₀ -
            a 0 (FormalODModule.piIndex 0 i₀) * a 1 i₀ ^ p * a 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst x ^ (p ^ 2) ∧
      a 0 (FormalODModule.piIndex 0 i₀) ^ p * TrivSqZeroExt.snd x =
        c * ((a 0 (FormalODModule.piIndex 0 i₀) ^ (p + 1) * ν 2 i₀ -
              a 0 (FormalODModule.piIndex 0 i₀) * a 1 i₀ ^ p * ν 1 (FormalODModule.piIndex 0 i₀)) * TrivSqZeroExt.fst x ^ (p ^ 2) +
            (a 0 (FormalODModule.piIndex 0 i₀) ^ p * ν 1 i₀ + a 0 (FormalODModule.piIndex 0 i₀) * ν 1 (FormalODModule.piIndex 0 i₀)) *
              TrivSqZeroExt.fst x ^ p) := by
  classical
  haveI : CharP (DualNumber κ) p := (Algebra.charP_iff κ (DualNumber κ) p).1 inferInstance
  have hom0 : ∀ f : CartierModule p X.F, homothety (0 : DualNumber κ) f = 0 := fun f => by
    rw [← teichmuller_smul, WittVector.teichmuller_zero]
    exact zero_smul (WittVector p (DualNumber κ)) f
  letI : Algebra ℤ_[p] (DualNumber κ) :=
    ((algebraMap κ (DualNumber κ)).comp ((ZMod.castHom (dvd_refl p) κ).comp (PadicInt.toZMod (p := p)))).toAlgebra
  obtain ⟨hV, -, hker, -⟩ :=
    MvFormalGroup.CartierModule.verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
      p X.F

  obtain ⟨h, hh⟩ := hA i₀ 1
  have hPi : endAct X.varpiEnd (γ i₀) = verschiebungInt h := by
    rw [hh]
    simp [ha0, hν0, hom0]
  have hi : ∀ m' ∈ X.gradedPiece j (i₀ : ℕ), ∃ g : CartierModule p X.F,
      verschiebungInt g = endAct X.varpiEnd m' :=
    fun m' hm' => C2PLineReads.exists_verschiebungInt_eq_varpi j X hc γ hγ hker i₀ h hPi m' hm'

  obtain ⟨m₁, hm₁, hinv, rfl⟩ :=
    (CerednikDrinfeld.FormalODModule.mem_etaPiece_iff_exists_varpiEnd_eq_verschiebungInt_of_charP
      p j X hc hV L hL i₀ hi z).1 hz
  have hq : (X.toGradedCartierModuleData j hc).vRange.mkQ m₁ =
      (X.toGradedCartierModuleData j hc).u L hL.isCartierLMap.map_verschiebung
        ⟨(X.toGradedCartierModuleData j hc).nMk (m₁, 0), (AddSubgroup.mem_inf.mp hz).1⟩ := rfl

  obtain ⟨δ₀, δ₁, t, -, htan, -, -, hD0, hD1⟩ :=
    CerednikDrinfeld.FormalODModule.exists_digits_tangent_eq_and_fst_snd_eq_of_varpiEnd_eq_verschiebungInt_of_hasStructureConstants_dualNumber
      p κ j X γ hγ a (fun m i => c * ν m i) hA (fun i => by show c * ν 0 i = 0; rw [hν0, mul_zero]) i₀ ha0
      m₁ hm₁ hinv

  have htm : tangent m = tangent m₁ := by
    have h2 := hm.trans hq.symm
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h2
    obtain ⟨y, hy⟩ := h2
    have hy' : verschiebungInt y = m - m₁ := hy
    have : tangent (m - m₁) = 0 := by
      rw [← hy']
      exact tangent_verschiebungInt y
    rwa [map_sub, sub_eq_zero] at this
  have hx0 : tangent m = δ₀ • tangent (γ i₀) := by
    rw [htm, htan]; rfl
  refine ⟨⟨δ₀, hx0⟩, fun x hx => ?_⟩
  have hxe : x = δ₀ := by
    have h2 := hx0.symm.trans hx
    exact (C2PLineReads.smul_row_injective (Matrix.of fun i k => tangent (γ i) k) hγ.2 i₀ δ₀ x h2).symm
  subst hxe
  refine ⟨hD0, ?_⟩
  rw [hD1]
  ring

end S_CerednikDrinfeld_FormalODModule_exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_tangent_eq_smul_and_forall_fst_snd_eq_of_mem_etaPiece_of_hasStructureConstants_dualNumber (solution)
