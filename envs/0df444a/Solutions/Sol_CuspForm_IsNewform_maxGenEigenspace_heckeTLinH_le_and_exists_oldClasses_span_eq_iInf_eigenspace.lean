-- Prove2me | solution 1 for CuspForm.IsNewform.maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9134f640-a5c4-56ee-b6f6-c404ec7ab7e9

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Definitions.Def_CuspForm_PrimitiveFormGamma1
import Theorems.Thm_CuspForm_IsNewform_exists_gamma1_coe_eq_and_isPrimitiveForm_one
import Theorems.Thm_CuspForm_exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus
import Theorems.Thm_CuspForm_exists_gammaH_coe_eq_of_hasNebentypus
import Theorems.Thm_CuspForm_exists_gamma1_coe_eq_of_gammaH
import Theorems.Thm_CuspForm_coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus
import Theorems.Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul
import Theorems.Thm_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_IsPrimitiveForm_level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat CuspForm.Gamma1Hecke.redMatrix_apply_one_one CuspForm.Gamma1Hecke.redMatrix_apply_one_zero CuspForm.Gamma1Hecke.lift_infty CuspForm.Gamma1Hecke.heckeRep_infty CuspForm.Gamma1Hecke.heckeRep_coe CuspForm.Gamma1Hecke.wt_infty CuspForm.Gamma1Hecke.redMatrix_apply_zero_one CuspForm.coe_slashLinOfMemGamma0_apply CuspForm.Gamma1Hecke.wt_coe CuspForm.Gamma1Hecke.lift_coe CuspForm.Gamma1Hecke.redMatrix_apply_zero_zero CuspForm.coe_heckeTOne CuspForm.coe_heckeTLinOne_apply CuspForm.coe_slashOfMemGamma0 CuspForm.PeterssonCoset.mapGL_apply"

set_option autoImplicit false

namespace CuspForm
p2m_export "CuspForm" "IsGLPos.coe_smul coe_zero coe_sub coe_smul coe_add IsNewform heckeULinH heckeTLinH HasNebentypus IsPrimitiveForm IsNewform.exists_gamma1_coe_eq_and_isPrimitiveForm_one exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus exists_gammaH_coe_eq_of_hasNebentypus exists_gamma1_coe_eq_of_gammaH coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq"
namespace CCAAux
p2m_open "CuspForm"

open scoped MatrixGroups ModularForm
open CongruenceSubgroup

theorem maxGenEigenspace_le_eigenspace_of_forall_mem_span {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (T : Module.End K V) {ι : Type*} (v : ι → V) (a : ι → K)
    (hv : ∀ i, T (v i) = a i • v i) (hspan : ∀ x : V, x ∈ Submodule.span K (Set.range v)) (ν : K) :
    T.maxGenEigenspace ν ≤ T.eigenspace ν := by
  intro x hx
  have htop : ∀ y : V, y ∈ ⨆ μ, T.eigenspace μ := by
    intro y
    refine Submodule.span_le.2 ?_ (hspan y)
    rintro _ ⟨i, rfl⟩
    exact Submodule.mem_iSup_of_mem (a i) (Module.End.mem_eigenspace_iff.2 (hv i))
  have hx' : x ∈ T.eigenspace ν ⊔ ⨆ μ, ⨆ (_ : μ ≠ ν), T.eigenspace μ := by
    rw [← iSup_split_single]
    exact htop x
  obtain ⟨e, he, r, hr, rfl⟩ := Submodule.mem_sup.1 hx'
  have hr' : r ∈ ⨆ μ, ⨆ (_ : μ ≠ ν), T.maxGenEigenspace μ :=
    (iSup₂_mono fun μ _ => (Module.End.eigenspace_le_maxGenEigenspace : T.eigenspace μ ≤ _)) hr
  have hrν : r ∈ T.maxGenEigenspace ν := by
    have := Submodule.sub_mem _ hx (Module.End.eigenspace_le_maxGenEigenspace he)
    rwa [add_sub_cancel_left] at this
  have hdis : Disjoint (T.maxGenEigenspace ν) (⨆ μ, ⨆ (_ : μ ≠ ν), T.maxGenEigenspace μ) :=
    Module.End.independent_maxGenEigenspace T ν
  have h0 : r = 0 := (Submodule.disjoint_def.1 hdis) r hrν hr'
  rw [h0, add_zero]
  exact he

theorem apply_units_eq_one_of_changeLevel_eq_one {L N : ℕ} [NeZero N] (hL : L ∣ N)
    (ε : DirichletCharacter ℂ L) (h : DirichletCharacter.changeLevel hL ε = 1) (u : (ZMod L)ˣ) :
    ε u = 1 := by
  obtain ⟨w, rfl⟩ := ZMod.unitsMap_surjective hL u
  have hw := DirichletCharacter.changeLevel_eq_cast_of_dvd ε hL w
  rw [h, MulChar.one_apply_coe] at hw
  rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply]
  exact hw.symm

theorem apply_natCast_eq_one_of_changeLevel_eq_one {L N : ℕ} [NeZero N] (hL : L ∣ N)
    (ε : DirichletCharacter ℂ L) (h : DirichletCharacter.changeLevel hL ε = 1) {p : ℕ}
    (hp : Nat.Coprime p L) : ε (p : ZMod L) = 1 := by
  have := apply_units_eq_one_of_changeLevel_eq_one hL ε h (ZMod.unitOfCoprime p hp)
  rwa [ZMod.coe_unitOfCoprime] at this

theorem hasNebentypus_one_of_coe_eq {N : ℕ} [NeZero N] {k : ℤ}
    (F : CuspForm (CohCarrier.GammaH N ⊤) k) (f₁ : CuspForm (CongruenceSubgroup.Gamma1 N) k)
    (h : (⇑f₁ : UpperHalfPlane → ℂ) = ⇑F) :
    CuspForm.HasNebentypus (1 : DirichletCharacter ℂ N) f₁ := by
  intro γ hγ τ
  have hγ' : (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) ∈
      (CohCarrier.GammaH N ⊤ : Subgroup (GL (Fin 2) ℝ)) :=
    Subgroup.mem_map_of_mem _ (by rw [CohCarrier.GammaH_top]; exact hγ)
  have hs : ((⇑F) ∣[k] γ) τ = F τ := by
    rw [ModularForm.SL_slash]
    exact congrFun (SlashInvariantForm.slash_action_eqn F _ hγ') τ
  rw [ModularForm.slash_action_eq'_iff] at hs
  have hunit : IsUnit (((γ 1 1 : ℤ) : ZMod N)) :=
    ⟨CohCarrier.gamma0Units N ⟨γ, hγ⟩, by rw [CohCarrier.val_gamma0Units]; rfl⟩
  rw [MulChar.one_apply hunit, one_mul, h]
  exact hs

theorem coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*} (s : Finset ι)
    (f : ι → CuspForm Γ k) : (⇑(∑ i ∈ s, f i) : UpperHalfPlane → ℂ) = ∑ i ∈ s, ⇑(f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, CuspForm.coe_add, ih]

theorem coe_sum_smul {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne] {k : ℤ} {ι : Type*} [Fintype ι]
    (c : ι → ℂ) (f : ι → CuspForm Γ k) :
    (⇑(∑ i, c i • f i) : UpperHalfPlane → ℂ) = ∑ i, c i • ⇑(f i) := by
  rw [coe_finset_sum]
  exact Finset.sum_congr rfl fun i _ => CuspForm.IsGLPos.coe_smul _ _

end CuspForm.CCAAux

theorem solution
    (N : ℕ) [NeZero N] (S : Finset ℕ) (hNS : ∀ q : ℕ, q.Prime → q ∣ N → q ∈ S)
    (Mg : ℕ) [NeZero Mg] (hMgN : Mg ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 Mg) 2) (hg : g.IsNewform) :

    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (ν : ℂ),
      Module.End.maxGenEigenspace
          (CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ hℓN) ν ≤
        Module.End.eigenspace (CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ hℓN) ν) ∧

    ∃ v : ℕ → CuspForm (CohCarrier.GammaH N ⊤) 2,
      (∀ d : ℕ, d ∣ N / Mg → ∀ τ : UpperHalfPlane, v d τ = g (ModularForm.heckeDiagMatrix d • τ)) ∧
      LinearIndependent ℂ (fun d : ↥(Nat.divisors (N / Mg)) => v (d : ℕ)) ∧
      Submodule.span ℂ (Set.range fun d : ↥(Nat.divisors (N / Mg)) => v (d : ℕ)) =
        ⨅ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓS : ℓ ∉ S), Module.End.eigenspace
          (CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ (fun h => hℓS (hNS ℓ hℓ h)))
          (ModularFormClass.qCoeff g ℓ) ∧
      (∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (d : ℕ), d ∣ N / Mg →
        (q ∣ d → CuspForm.heckeULinH 2 q (v d) = v (d / q)) ∧
        (¬ q ∣ d → q ∣ Mg → CuspForm.heckeULinH 2 q (v d) = ModularFormClass.qCoeff g q • v d) ∧
        (¬ q ∣ d → ¬ q ∣ Mg → CuspForm.heckeULinH 2 q (v d) =
          ModularFormClass.qCoeff g q • v d - (q : ℂ) • v (d * q))) := by
  classical
  have hN0 : N ≠ 0 := NeZero.ne N

  obtain ⟨g₁, hg₁g, hprim⟩ := hg.exists_gamma1_coe_eq_and_isPrimitiveForm_one

  obtain ⟨n, L, hL, εL, gi, G, hP, hD, hC, hCOMP, hG, hLI, hSP⟩ :=
    CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus N 2
      (1 : DirichletCharacter ℂ N)
  haveI hLne : ∀ i, NeZero (L i) := fun i =>
    ⟨fun h => hN0 (Nat.eq_zero_of_zero_dvd (h ▸ hL i))⟩

  obtain ⟨i₀, hLi₀, hqi₀⟩ := hCOMP Mg hMgN 1 g₁ hprim (DirichletCharacter.changeLevel_one hMgN)
  subst hLi₀
  have hgi₀ : (⇑(gi i₀) : UpperHalfPlane → ℂ) = ⇑g := by
    have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 (L i₀) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
      rw [CongruenceSubgroup.strictPeriods_Gamma1]
      exact AddSubgroup.mem_zmultiples 1
    have : gi i₀ = g₁ := ModularFormClass.eq_of_forall_qCoeff_eq h1 hqi₀
    rw [this, hg₁g]
  have hqc : ∀ m, ModularFormClass.qCoeff (gi i₀) m = ModularFormClass.qCoeff g m := fun m => by
    rw [hgi₀]

  have hεu : ∀ (i : Fin n) (u : (ZMod (L i))ˣ), εL i u = 1 := fun i u =>
    CuspForm.CCAAux.apply_units_eq_one_of_changeLevel_eq_one (hL i) (εL i) (hC i) u
  have hεp : ∀ (i : Fin n) (p : ℕ), p.Prime → ¬ p ∣ L i → εL i (p : ZMod (L i)) = 1 := fun i p hp hpL =>
    CuspForm.CCAAux.apply_natCast_eq_one_of_changeLevel_eq_one (hL i) (εL i) (hC i)
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpL)

  have hone : ∀ d : (ZMod N)ˣ, d ∈ (⊤ : Subgroup (ZMod N)ˣ) → (1 : DirichletCharacter ℂ N) (d : ZMod N) = 1 :=
    fun d _ => MulChar.one_apply_coe d
  have hex : ∀ (i : Fin n) (d : ℕ), d ∣ N / L i →
      ∃ F : CuspForm (CohCarrier.GammaH N ⊤) 2, (⇑F : UpperHalfPlane → ℂ) = ⇑(G i d) :=
    fun i d hd => CuspForm.exists_gammaH_coe_eq_of_hasNebentypus N ⊤ 2 1 hone (G i d) (hG i d hd).2
  choose Gt₀ hGt₀ using hex
  let Gt : Fin n → ℕ → CuspForm (CohCarrier.GammaH N ⊤) 2 := fun i d =>
    if hd : d ∣ N / L i then Gt₀ i d hd else 0
  have hGtc : ∀ (i : Fin n) (d : ℕ), d ∣ N / L i → (⇑(Gt i d) : UpperHalfPlane → ℂ) = ⇑(G i d) := by
    intro i d hd
    simp only [Gt, dif_pos hd]
    exact hGt₀ i d hd

  have hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (i : Fin n) (d : ℕ), d ∣ N / L i →
      CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ hℓN (Gt i d) =
        ModularFormClass.qCoeff (gi i) ℓ • Gt i d := by
    intro ℓ hℓ hℓN i d hd
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    apply DFunLike.coe_injective
    try dsimp only
    rw [CuspForm.IsGLPos.coe_smul]
    obtain ⟨-, hTcoe, -⟩ :=
      CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus N ⊤ 2 1
        (Gt i d) (G i d) (hGtc i d hd) (hG i d hd).2
    have hℓL : ¬ ℓ ∣ L i := fun h => hℓN (h.trans (hL i))
    have h1 : (1 : DirichletCharacter ℂ N) (ℓ : ZMod N) = εL i (ℓ : ZMod (L i)) := by
      rw [hεp i ℓ hℓ hℓL, MulChar.one_apply (ZMod.isUnit_prime_of_not_dvd hℓ hℓN)]
    change ⇑(CuspForm.heckeTLinH 2 hℓ hℓN (Gt i d)) = _
    rw [hTcoe ℓ hℓ hℓN, hGtc i d hd, h1]
    exact (hP i).isEigenformWith.heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul N 2
      (hL i) (G i) (fun d hd => (hG i d hd).1) hℓ hℓN hd
  have hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (i : Fin n) (d : ℕ), d ∣ N / L i →
      (q ∣ d → CuspForm.heckeULinH 2 q (Gt i d) = Gt i (d / q)) ∧
      (¬ q ∣ d → q ∣ L i → CuspForm.heckeULinH 2 q (Gt i d) = ModularFormClass.qCoeff (gi i) q • Gt i d) ∧
      (¬ q ∣ d → ¬ q ∣ L i → CuspForm.heckeULinH 2 q (Gt i d) =
        ModularFormClass.qCoeff (gi i) q • Gt i d -
          (εL i (q : ZMod (L i)) * (q : ℂ) ^ ((2 : ℤ) - 1)) • Gt i (d * q)) := by
    intro q hq hqN i d hd
    haveI : NeZero q := ⟨hq.ne_zero⟩
    obtain ⟨-, -, hUcoe⟩ :=
      CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus N ⊤ 2 1
        (Gt i d) (G i d) (hGtc i d hd) (hG i d hd).2
    obtain ⟨hU1, hU2, hU3⟩ := (hP i).isEigenformWith.heckeU_degeneracy_of_dvd_level N 2 (hL i) (G i)
      (fun d hd => (hG i d hd).1) hq hqN hd
    refine ⟨fun hqd => ?_, fun hqd hqL => ?_, fun hqd hqL => ?_⟩
    · apply DFunLike.coe_injective
      try dsimp only
      rw [hUcoe q hq hqN, hU1 hqd, hGtc i (d / q) ((Nat.div_dvd_of_dvd hqd).trans hd)]
    · apply DFunLike.coe_injective
      try dsimp only
      rw [hUcoe q hq hqN, hU2 hqd hqL, CuspForm.IsGLPos.coe_smul, hGtc i d hd]
    · have hqNL : q ∣ N / L i := by
        have := (Nat.Prime.dvd_mul hq).1 ((Nat.div_mul_cancel (hL i)).symm ▸ hqN : q ∣ N / L i * L i)
        exact this.resolve_right hqL
      have hdq : d * q ∣ N / L i :=
        Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.Prime.coprime_iff_not_dvd hq).2 hqd).symm hd hqNL
      apply DFunLike.coe_injective
      try dsimp only
      rw [hUcoe q hq hqN, hU3 hqd hqL, CuspForm.coe_sub, CuspForm.IsGLPos.coe_smul,
        CuspForm.IsGLPos.coe_smul, hGtc i d hd, hGtc i (d * q) hdq]

  let Gs : (Σ i : Fin n, ↥(Nat.divisors (N / L i))) → CuspForm (CongruenceSubgroup.Gamma1 N) 2 :=
    fun x => G x.1 (x.2 : ℕ)
  let Gts : (Σ i : Fin n, ↥(Nat.divisors (N / L i))) → CuspForm (CohCarrier.GammaH N ⊤) 2 :=
    fun x => Gt x.1 (x.2 : ℕ)
  have hxd : ∀ x : (Σ i : Fin n, ↥(Nat.divisors (N / L i))), (x.2 : ℕ) ∣ N / L x.1 := fun x =>
    Nat.dvd_of_mem_divisors x.2.2
  have hGsc : ∀ x, (⇑(Gts x) : UpperHalfPlane → ℂ) = ⇑(Gs x) := fun x => hGtc x.1 x.2 (hxd x)

  have hspan : ∀ f : CuspForm (CohCarrier.GammaH N ⊤) 2, f ∈ Submodule.span ℂ (Set.range Gts) := by
    intro f
    obtain ⟨f₁, hf₁⟩ := CuspForm.exists_gamma1_coe_eq_of_gammaH N ⊤ 2 f
    have hmem := hSP f₁ (CuspForm.CCAAux.hasNebentypus_one_of_coe_eq f f₁ hf₁)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
    refine (Submodule.mem_span_range_iff_exists_fun ℂ).2 ⟨c, DFunLike.coe_injective ?_⟩
    try dsimp only
    rw [CuspForm.CCAAux.coe_sum_smul, ← hf₁, ← hc, CuspForm.CCAAux.coe_sum_smul]
    exact Finset.sum_congr rfl fun x _ => by rw [hGsc]

  have hLIt : LinearIndependent ℂ Gts := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have hc' : ∑ x, c x • Gs x = 0 := by
      apply DFunLike.coe_injective
      try dsimp only
      rw [CuspForm.CCAAux.coe_sum_smul, CuspForm.coe_zero]
      have := congrArg (fun F : CuspForm (CohCarrier.GammaH N ⊤) 2 => (⇑F : UpperHalfPlane → ℂ)) hc
      simp only [CuspForm.CCAAux.coe_sum_smul, CuspForm.coe_zero, hGsc] at this
      exact this
    exact (Fintype.linearIndependent_iff.1 hLI) c hc'

  have hsep : ∀ i : Fin n, i ≠ i₀ → ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ S ∧ ¬ ℓ ∣ N ∧
      ModularFormClass.qCoeff (gi i) ℓ ≠ ModularFormClass.qCoeff (gi i₀) ℓ := by
    intro i hi
    by_contra hcon
    push Not at hcon
    have hSMO := CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
      (hP i) (hP i₀) (S ∪ N.primeFactors)
      (fun p hp hpS => by
        rw [Finset.mem_union, not_or, Nat.mem_primeFactors_of_ne_zero hN0] at hpS
        exact hcon p hp hpS.1 (fun h => hpS.2 ⟨hp, h⟩))
      (fun p hp hpS => by
        rw [Finset.mem_union, not_or, Nat.mem_primeFactors_of_ne_zero hN0] at hpS
        have hpN : ¬ p ∣ N := fun h => hpS.2 ⟨hp, h⟩
        rw [hεp i p hp (fun h => hpN (h.trans (hL i))), hεp i₀ p hp (fun h => hpN (h.trans (hL i₀)))])
    rcases hD i i₀ hi with hL' | ⟨m, hm⟩
    · exact hL' hSMO.1
    · exact hm (hSMO.2 m)

  refine ⟨fun ℓ hℓ hℓN ν => ?_, ⟨Gt i₀, fun d hd τ => ?_, ?_, ?_, fun q hq hqN d hd => ?_⟩⟩
  ·
    exact CuspForm.CCAAux.maxGenEigenspace_le_eigenspace_of_forall_mem_span _ Gts
      (fun x => ModularFormClass.qCoeff (gi x.1) ℓ) (fun x => hT ℓ hℓ hℓN x.1 x.2 (hxd x)) hspan ν
  ·
    rw [show (Gt i₀ d) τ = (G i₀ d) τ from congrFun (hGtc i₀ d hd) τ, (hG i₀ d hd).1 τ,
      show (gi i₀) (ModularForm.heckeDiagMatrix d • τ) = g (ModularForm.heckeDiagMatrix d • τ) from
        congrFun hgi₀ _]
  ·
    exact hLIt.comp (fun d : ↥(Nat.divisors (N / L i₀)) => (⟨i₀, d⟩ : Σ i : Fin n, ↥(Nat.divisors (N / L i))))
      (fun d d' h => by cases h; rfl)
  ·
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨d, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
      intro ℓ hℓ hℓS
      rw [← hqc]
      exact hT ℓ hℓ (fun h => hℓS (hNS ℓ hℓ h)) i₀ d (Nat.dvd_of_mem_divisors d.2)
    · intro x hx
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan x)

      have hc0 : ∀ y : (Σ i : Fin n, ↥(Nat.divisors (N / L i))), y.1 ≠ i₀ → c y = 0 := by
        intro y hy
        obtain ⟨ℓ, hℓ, hℓS, hℓN, hne⟩ := hsep y.1 hy
        have hxℓ : CuspForm.heckeTLinH (H := (⊤ : Subgroup (ZMod N)ˣ)) 2 hℓ (fun h => hℓS (hNS ℓ hℓ h))
            (∑ z, c z • Gts z) = ModularFormClass.qCoeff g ℓ • ∑ z, c z • Gts z := by
          have := (Submodule.mem_iInf _).1 hx ℓ
          have := (Submodule.mem_iInf _).1 this hℓ
          have := (Submodule.mem_iInf _).1 this hℓS
          exact Module.End.mem_eigenspace_iff.1 this
        have hrel : ∑ z, (c z * (ModularFormClass.qCoeff (gi z.1) ℓ - ModularFormClass.qCoeff g ℓ)) • Gts z = 0 := by
          simp only [mul_sub, sub_smul, Finset.sum_sub_distrib, mul_smul]
          rw [map_sum] at hxℓ
          simp only [map_smul, Finset.smul_sum] at hxℓ
          rw [sub_eq_zero]
          convert hxℓ using 2 with z _ z _
          · rw [hT ℓ hℓ (fun h => hℓS (hNS ℓ hℓ h)) z.1 z.2 (hxd z), smul_comm]
          · rw [smul_comm]
        have hz := (Fintype.linearIndependent_iff.1 hLIt) _ hrel y
        rw [hqc] at hne
        exact (mul_eq_zero.1 hz).resolve_right (sub_ne_zero.2 hne)

      rw [show (∑ z, c z • Gts z) = ∑ z ∈ Finset.univ.filter (fun z => z.1 = i₀), c z • Gts z from by
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun z _ => by
          by_cases hz : z.1 = i₀
          · rw [if_pos hz]
          · rw [if_neg hz, hc0 z hz, zero_smul]]
      refine Submodule.sum_mem _ fun z hz => Submodule.smul_mem _ _ ?_
      rw [Finset.mem_filter] at hz
      obtain ⟨⟨i, d⟩, rfl⟩ : ∃ z' : (Σ i : Fin n, ↥(Nat.divisors (N / L i))), z' = z := ⟨z, rfl⟩
      rcases hz with ⟨-, hzi⟩
      change i = i₀ at hzi
      subst hzi
      exact Submodule.subset_span ⟨d, rfl⟩
  ·
    obtain ⟨h1, h2, h3⟩ := hU q hq hqN i₀ d hd
    refine ⟨h1, fun hqd hqM => ?_, fun hqd hqM => ?_⟩
    · rw [h2 hqd hqM, hqc]
    · rw [h3 hqd hqM, hqc, hεp i₀ q hq hqM, one_mul]
      norm_num

end S_CuspForm_IsNewform_maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace
end P2MW
export P2MW.S_CuspForm_IsNewform_maxGenEigenspace_heckeTLinH_le_and_exists_oldClasses_span_eq_iInf_eigenspace (solution)
