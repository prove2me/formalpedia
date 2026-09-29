-- Prove2me | solution 1 for CuspForm.IsNewform.finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/1c601cba-f664-5416-913f-66fca836e9de

import Mathlib
import Definitions.Def_CuspForm_Newforms
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Theorems.Thm_CuspForm_heckeTLin_comm
import Theorems.Thm_CuspForm_span_rescaleLin_isNewform_eq_top
import Theorems.Thm_CuspForm_heckeTLin_rescaleLin
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_CuspForm_IsNewform_level_eq_and_qCoeff_eq_of_forall_qCoeff_eq
import Theorems.Thm_CuspForm_IsNormalizedEigenform_eq_of_forall_prime_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open ModularFormClass

namespace NewformDualLine

variable {M : ℕ} [NeZero M] (S : Finset ℕ)

abbrev I (M : ℕ) (S : Finset ℕ) : Type := {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S}

def T (ℓ : I M S) : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
  CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1

theorem T_comm (ℓ ℓ' : I M S) : Commute (T S ℓ) (T S ℓ') :=
  CuspForm.heckeTLin_comm 2 ℓ.2.1 ℓ.2.2.1 ℓ'.2.1 ℓ'.2.2.1

def Esp (μ : I M S → ℂ) : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
  ⨅ ℓ, Module.End.eigenspace (T S ℓ) (μ ℓ)

theorem mem_Esp {μ : I M S → ℂ} {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} :
    f ∈ Esp S μ ↔ ∀ ℓ, T S ℓ f = μ ℓ • f := by
  simp [Esp, Submodule.mem_iInf]

theorem iSupIndep_Esp : iSupIndep (fun μ : I M S → ℂ => Esp S μ) := by
  have h := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (T (M := M) S)
    (fun i j φ => Module.End.mapsTo_maxGenEigenspace_of_comm (T_comm S j i) φ)
  refine h.mono fun μ => ?_
  exact iInf_mono fun ℓ => Module.End.eigenspace_le_maxGenEigenspace

def 𝓑 : Set (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
  {F | ∃ (R d : ℕ) (hdRM : d * R ∣ M) (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2),
    CuspForm.IsNewform g' ∧ F = FreyPackage.ModMCarrier.rescaleLin hdRM 2 g'}

theorem span_𝓑 : Submodule.span ℂ (𝓑 (M := M)) = ⊤ :=
  CuspForm.span_rescaleLin_isNewform_eq_top M

theorem neZero_of_mul_dvd {R d : ℕ} (hdRM : d * R ∣ M) : NeZero R :=
  ⟨by rintro rfl; exact NeZero.ne M (Nat.eq_zero_of_zero_dvd (by simpa using hdRM))⟩

theorem rescale_mem_Esp {R d : ℕ} (hdRM : d * R ∣ M)
    (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (hg' : CuspForm.IsNewform g') :
    FreyPackage.ModMCarrier.rescaleLin hdRM 2 g' ∈ Esp S (fun ℓ => qCoeff g' ℓ) := by
  haveI : NeZero R := neZero_of_mul_dvd hdRM
  rw [mem_Esp]
  intro ℓ
  have hℓR : ¬ (ℓ : ℕ) ∣ R := fun h => ℓ.2.2.1 (h.trans ((Dvd.intro_left d rfl).trans hdRM))
  have heig := ((CuspForm.isNormalizedEigenform_iff_heckeTLin g').1 hg'.1).2 ℓ ℓ.2.1
  rw [T, CuspForm.heckeTLin_rescaleLin hdRM ℓ.2.1 ℓ.2.2.1 hℓR g', (heig.1 hℓR), map_smul]

theorem heckeDiagMatrix_one : ModularForm.heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  rw [ModularForm.val_heckeDiagMatrix one_ne_zero, Units.val_one, Matrix.one_fin_two]
  simp

theorem rescaleLin_one (h : 1 * M ∣ M) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    FreyPackage.ModMCarrier.rescaleLin h 2 f = f := by
  apply DFunLike.coe_injective
  show ⇑(FreyPackage.ModMCarrier.rescaleLin h 2 f) = ⇑f
  rw [FreyPackage.ModMCarrier.coe_rescaleLin_apply, heckeDiagMatrix_one]
  exact SlashAction.slash_one 2 ⇑f

variable {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)

def cg (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) : I M S → ℂ := fun ℓ => qCoeff g ℓ

include hg in
theorem g_mem_Esp : g ∈ Esp S (cg S g) := by
  rw [mem_Esp]
  intro ℓ
  exact (((CuspForm.isNormalizedEigenform_iff_heckeTLin g).1 hg.1).2 ℓ ℓ.2.1).1 ℓ.2.2.1

include hg in

theorem rescale_eq_of_packet_eq {R d : ℕ} (hdRM : d * R ∣ M)
    (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (hg' : CuspForm.IsNewform g')
    (hpk : (fun ℓ : I M S => qCoeff g' ℓ) = cg S g) :
    FreyPackage.ModMCarrier.rescaleLin hdRM 2 g' = g := by

  let P : ℕ := ∏ q ∈ S, max q 1
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun q _ => by
    exact Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le Nat.zero_lt_one (le_max_right q 1))
  haveI : NeZero (M * P) := ⟨mul_ne_zero (NeZero.ne M) hP⟩
  have hR : R ∣ M * P := ((Dvd.intro_left d rfl).trans hdRM).trans (Dvd.intro _ rfl)
  have hM : M ∣ M * P := Dvd.intro _ rfl
  have h : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M * P → qCoeff g' ℓ = qCoeff g ℓ := by
    intro ℓ hℓ hℓMP
    have hℓM : ¬ ℓ ∣ M := fun h => hℓMP (h.mul_right P)
    have hℓS : ℓ ∉ S := by
      intro hS
      apply hℓMP
      have h1 : max ℓ 1 ∣ P := Finset.dvd_prod_of_mem (fun q => max q 1) hS
      rw [max_eq_left hℓ.one_lt.le] at h1
      exact h1.mul_left M
    exact congrFun hpk ⟨ℓ, hℓ, hℓM, hℓS⟩
  obtain ⟨hRM, hq⟩ := CuspForm.IsNewform.level_eq_and_qCoeff_eq_of_forall_qCoeff_eq hg' hg hR hM h
  subst hRM
  have hgg : g' = g :=
    CuspForm.IsNormalizedEigenform.eq_of_forall_prime_qCoeff_eq hg'.1 hg.1 fun p _ => hq p
  subst hgg

  have hd : d = 1 := by
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact NeZero.ne R (Nat.eq_zero_of_zero_dvd (by simpa using hdRM))
    have hle : d * R ≤ 1 * R := by
      rw [one_mul]; exact Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne R)) hdRM
    have : d ≤ 1 := Nat.le_of_mul_le_mul_right hle (Nat.pos_of_ne_zero (NeZero.ne R))
    omega
  subst hd
  exact rescaleLin_one hdRM g'

def 𝓑' (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    Set (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
  {F | ∃ (R d : ℕ) (hdRM : d * R ∣ M) (g' : CuspForm (CongruenceSubgroup.Gamma0 R) 2),
    CuspForm.IsNewform g' ∧ F = FreyPackage.ModMCarrier.rescaleLin hdRM 2 g' ∧
      (fun ℓ : I M S => qCoeff g' ℓ) ≠ cg S g}

def W' (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
  Submodule.span ℂ (𝓑' S g)

include hg in
theorem 𝓑_subset : 𝓑 (M := M) ⊆ ↑((ℂ ∙ g) ⊔ W' S g) := by
  rintro F ⟨R, d, hdRM, g', hg', rfl⟩
  by_cases hpk : (fun ℓ : I M S => qCoeff g' ℓ) = cg S g
  · rw [rescale_eq_of_packet_eq S hg hdRM g' hg' hpk]
    exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self g)
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨R, d, hdRM, g', hg', rfl, hpk⟩)

include hg in
theorem sup_eq_top : (ℂ ∙ g) ⊔ W' S g = ⊤ := by
  rw [eq_top_iff, ← span_𝓑 (M := M), Submodule.span_le]
  exact 𝓑_subset S hg

theorem W'_le_iSup : W' S g ≤ ⨆ μ ∈ {μ : I M S → ℂ | μ ≠ cg S g}, Esp S μ := by
  rw [W', Submodule.span_le]
  rintro F ⟨R, d, hdRM, g', hg', rfl, hpk⟩
  have hmem := rescale_mem_Esp S hdRM g' hg'
  exact (le_biSup (fun μ => Esp S μ) hpk : Esp S (fun ℓ : I M S => qCoeff g' ℓ) ≤ _) hmem

include hg in
theorem disjoint : Disjoint (ℂ ∙ g) (W' S g) := by
  have h := (iSupIndep_Esp (M := M) S).disjoint_biSup (x := cg S g)
    (y := {μ : I M S → ℂ | μ ≠ cg S g}) (fun h => h rfl)
  refine h.mono ?_ (W'_le_iSup S)
  rw [Submodule.span_singleton_le_iff_mem]
  exact g_mem_Esp S hg

include hg in
theorem isCompl : IsCompl (ℂ ∙ g) (W' S g) :=
  ⟨disjoint S hg, codisjoint_iff.mpr (sup_eq_top S hg)⟩

theorem T_mem_W' (ℓ : I M S) {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f ∈ W' S g) :
    T S ℓ f ∈ W' S g := by
  have h : (W' S g).map (T S ℓ) ≤ W' S g := by
    rw [W', Submodule.map_span_le]
    rintro F ⟨R, d, hdRM, g', hg', rfl, hpk⟩
    have hmem := (mem_Esp S).mp (rescale_mem_Esp S hdRM g' hg') ℓ
    rw [hmem]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨R, d, hdRM, g', hg', rfl, hpk⟩)
  exact h ⟨f, hf, rfl⟩

def Edual (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    Submodule ℂ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)) :=
  ⨅ ℓ : I M S, Module.End.eigenspace (T S ℓ).dualMap (cg S g ℓ)

theorem mem_Edual {v : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)} :
    v ∈ Edual S g ↔ ∀ (ℓ : I M S) (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2),
      v (T S ℓ f) = cg S g ℓ * v f := by
  simp only [Edual, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  refine forall_congr' fun ℓ => ?_
  rw [LinearMap.ext_iff]
  refine forall_congr' fun f => ?_
  rw [LinearMap.dualMap_apply, LinearMap.smul_apply, smul_eq_mul]

theorem apply_eq_zero_of_mem_W' {v : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)}
    (hv : v ∈ Edual S g) {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f ∈ W' S g) :
    v f = 0 := by
  rw [W'] at hf
  induction hf using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨R, d, hdRM, g', hg', rfl, hpk⟩ := hF
    obtain ⟨ℓ, hℓ⟩ := Function.ne_iff.mp hpk
    have h1 := (mem_Edual S).mp hv ℓ (FreyPackage.ModMCarrier.rescaleLin hdRM 2 g')
    have h2 := (mem_Esp S).mp (rescale_mem_Esp S hdRM g' hg') ℓ
    rw [h2, map_smul, smul_eq_mul] at h1
    have h3 : (qCoeff g' ℓ - cg S g ℓ) * v (FreyPackage.ModMCarrier.rescaleLin hdRM 2 g') = 0 := by
      rw [sub_mul, h1, sub_self]
    exact (mul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hℓ)
  | zero => exact map_zero v
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [map_smul, hx, smul_zero]

include hg in

theorem eq_zero_of_apply_g {v : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2)}
    (hv : v ∈ Edual S g) (h0 : v g = 0) : v = 0 := by
  refine LinearMap.ext_on (s := (((ℂ ∙ g) ⊔ W' S g : Submodule ℂ _) : Set _))
    (by rw [Submodule.span_eq, sup_eq_top S hg]) ?_
  intro f hf
  rw [SetLike.mem_coe] at hf
  obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp ha
  rw [LinearMap.zero_apply, map_add, map_smul, h0, smul_zero, zero_add,
    apply_eq_zero_of_mem_W' S hv hw]

include hg in

theorem exists_mem_Edual_apply_g_eq_one :
    ∃ v ∈ Edual S g, v g = 1 := by
  have hg0 : g ≠ 0 := hg.ne_zero
  let e := Submodule.prodEquivOfIsCompl (ℂ ∙ g) (W' S g) (isCompl S hg)
  let κ : (ℂ ∙ g) ≃ₗ[ℂ] ℂ := (LinearEquiv.toSpanNonzeroSingleton ℂ _ g hg0).symm
  let v : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 M) 2) :=
    κ.toLinearMap ∘ₗ (LinearMap.fst ℂ _ _) ∘ₗ e.symm.toLinearMap
  have hvg : v g = 1 := by
    show κ ((e.symm g).1) = 1
    have : e.symm g = (⟨g, Submodule.mem_span_singleton_self g⟩, 0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left _ _ (isCompl S hg) ⟨g, _⟩
    rw [this]
    show κ ⟨g, _⟩ = 1
    rw [LinearEquiv.symm_apply_eq, LinearEquiv.toSpanNonzeroSingleton_one]
  have hvw : ∀ w ∈ W' S g, v w = 0 := by
    intro w hw
    show κ ((e.symm w).1) = 0
    have : e.symm w = (0, ⟨w, hw⟩) :=
      Submodule.prodEquivOfIsCompl_symm_apply_right _ _ (isCompl S hg) ⟨w, hw⟩
    rw [this]
    exact map_zero κ
  refine ⟨v, ?_, hvg⟩
  rw [mem_Edual]
  intro ℓ f
  have hf : f ∈ (ℂ ∙ g) ⊔ W' S g := by rw [sup_eq_top S hg]; trivial
  obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp hf
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp ha
  have hTg : T S ℓ g = cg S g ℓ • g := (mem_Esp S).mp (g_mem_Esp S hg) ℓ
  rw [map_add, map_smul, hTg, map_add, map_smul, map_smul, hvg, hvw _ (T_mem_W' S ℓ hw),
    map_add, map_smul, hvg, hvw w hw]
  simp only [smul_eq_mul, mul_one, add_zero]
  ring

include hg in

theorem finrank_Edual : Module.finrank ℂ (Edual S g) = 1 := by
  obtain ⟨v₀, hv₀, hv₀g⟩ := exists_mem_Edual_apply_g_eq_one S hg

  let ev : Edual S g →ₗ[ℂ] ℂ := (LinearMap.applyₗ g).comp (Edual S g).subtype
  have hev : ∀ v : Edual S g, ev v = (v : Module.Dual ℂ _) g := fun v => rfl
  have hinj : Function.Injective ev := by
    intro v w h
    apply Subtype.ext
    rw [← sub_eq_zero]
    apply eq_zero_of_apply_g S hg (Submodule.sub_mem _ v.2 w.2)
    rw [LinearMap.sub_apply, sub_eq_zero]
    rw [hev, hev] at h
    exact h
  have hsurj : Function.Surjective ev := by
    intro t
    refine ⟨t • ⟨v₀, hv₀⟩, ?_⟩
    rw [map_smul, hev, smul_eq_mul]
    change t * v₀ g = t
    rw [hv₀g, mul_one]
  rw [(LinearEquiv.ofBijective ev ⟨hinj, hsurj⟩).finrank_eq, Module.finrank_self]

end NewformDualLine

theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hg : g.IsNewform)
    (S : Finset ℕ) :
    Module.finrank ℂ ↥(⨅ ℓ : {ℓ : ℕ // ℓ.Prime ∧ ¬ ℓ ∣ M ∧ ℓ ∉ S},
        Module.End.eigenspace (CuspForm.heckeTLin 2 ℓ.2.1 ℓ.2.2.1).dualMap
          (ModularFormClass.qCoeff g ℓ)) = 1 :=
  NewformDualLine.finrank_Edual S hg

end
end S_CuspForm_IsNewform_finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one
end P2MW
export P2MW.S_CuspForm_IsNewform_finrank_iInf_eigenspace_dualMap_heckeTLin_eq_one (solution)
