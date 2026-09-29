-- Prove2me | solution 1 for CuspForm.IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/4baf96c7-5ff2-5e4c-ac53-219485fa1984

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_IsNewform_sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero
import Theorems.Thm_CuspForm_sum_range_slash_heckeDiagMatrix_heckeDiagMatrix_conj_eq
import Theorems.Thm_CuspForm_IsNewform_sum_range_slash_heckeDiagMatrix_conj_eq_qCoeff_smul
import Theorems.Thm_CuspForm_norm_lt_of_heckeTLin_eq_smul
import Theorems.Thm_CuspForm_newformBadPrimeCoeff
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_rescaleLin_sub_rescaleLin_notMem_span_sup_span
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero CuspForm.coe_traceLin_apply ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply FreyPackage.ModMCarrier.coe_levelInclusionLin FreyPackage.ModMCarrier.atkinLehnerDatumOfPrimeNotDvd_R FreyPackage.ModMCarrier.latticeRed.mk_eq_tmul CuspForm.coe_heckeULowerLin_apply"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm OnePoint Function
open scoped MatrixGroups ModularForm Manifold

namespace NewformTowerTrace

private abbrev _root_.NewformTowerTrace.S (N : ℕ) := CuspForm (CongruenceSubgroup.Gamma0 N) 2

p2m_export "NewformTowerTrace" "S"
theorem sum_slash {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ) :
    (∑ i ∈ s, f i) ∣[k] g = ∑ i ∈ s, (f i ∣[k] g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

section perm

variable {q : ℕ} [NeZero q]

def σ (b d : ℤ) (j : ℕ) : ℕ := (((b * d + (j : ℤ) * d * d : ℤ)) : ZMod q).val

def σinv (a b d : ℤ) (j : ℕ) : ℕ :=
  ((((j : ℕ) : ZMod q) - ((b * d : ℤ) : ZMod q)) * ((a : ℤ) : ZMod q) ^ 2).val

theorem σ_lt (b d : ℤ) (j : ℕ) : σ (q := q) b d j < q := ZMod.val_lt _

theorem σinv_lt (a b d : ℤ) (j : ℕ) : σinv (q := q) a b d j < q := ZMod.val_lt _

theorem σ_cast (b d : ℤ) (j : ℕ) :
    ((σ (q := q) b d j : ℕ) : ZMod q)
      = ((b : ℤ) : ZMod q) * ((d : ℤ) : ZMod q)
        + ((j : ℕ) : ZMod q) * ((d : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) := by
  unfold σ
  rw [ZMod.natCast_zmod_val]
  push_cast
  ring

theorem σinv_cast (a b d : ℤ) (j : ℕ) :
    ((σinv (q := q) a b d j : ℕ) : ZMod q)
      = (((j : ℕ) : ZMod q) - ((b : ℤ) : ZMod q) * ((d : ℤ) : ZMod q)) * ((a : ℤ) : ZMod q) ^ 2 := by
  unfold σinv
  rw [ZMod.natCast_zmod_val]
  push_cast
  ring

theorem σinv_σ {a b d : ℤ} (had : ((a : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) = 1) {j : ℕ}
    (hj : j < q) : σinv (q := q) a b d (σ (q := q) b d j) = j := by
  unfold σinv
  have h : (((σ (q := q) b d j : ℕ) : ZMod q) - ((b * d : ℤ) : ZMod q)) * ((a : ℤ) : ZMod q) ^ 2
      = ((j : ℕ) : ZMod q) := by
    rw [σ_cast]
    push_cast
    linear_combination (((j : ℕ) : ZMod q) * (((a : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) + 1)) * had
  rw [h, ZMod.val_cast_of_lt hj]

theorem σ_σinv {a b d : ℤ} (had : ((a : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) = 1) {j : ℕ}
    (hj : j < q) : σ (q := q) b d (σinv (q := q) a b d j) = j := by
  unfold σ
  have h : ((b * d + ((σinv (q := q) a b d j : ℕ) : ℤ) * d * d : ℤ) : ZMod q)
      = ((j : ℕ) : ZMod q) := by
    push_cast
    rw [σinv_cast]
    linear_combination ((((j : ℕ) : ZMod q) - ((b : ℤ) : ZMod q) * ((d : ℤ) : ZMod q)) *
      (((a : ℤ) : ZMod q) * ((d : ℤ) : ZMod q) + 1)) * had
  rw [h, ZMod.val_cast_of_lt hj]

end perm

def lowSL (c : ℤ) : SL(2, ℤ) := ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two_of]⟩

theorem lowSL_coe (c : ℤ) : ((lowSL c : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; c, 1] :=
  rfl

def β (L : ℕ) (j : ℕ) : GL (Fin 2) ℝ :=
  (Matrix.SpecialLinearGroup.mapGL ℝ (lowSL ((L : ℤ) * j)) : GL (Fin 2) ℝ)

theorem ad_eq_one {p : ℕ} {γ : SL(2, ℤ)} (hc : (p : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod p) * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod p)
      = 1 := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hc0 : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hc
  have h := congrArg (fun z : ℤ => (z : ZMod p)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc0, mul_zero, sub_zero] at h
  exact h

def τidx (p L : ℕ) [NeZero p] (γ : SL(2, ℤ)) (j : ℕ) : ℕ :=
  σ (q := p) (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) / (L : ℤ)) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) j

def τinv (p L : ℕ) [NeZero p] (γ : SL(2, ℤ)) (j : ℕ) : ℕ :=
  σinv (q := p) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) / (L : ℤ))
    ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0) j

theorem exists_conj {L p : ℕ} [NeZero p] (hp : p ∣ L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 L) (j : ℕ) :
    ∃ γ' : SL(2, ℤ), γ' ∈ CongruenceSubgroup.Gamma0 (L * p) ∧
      lowSL ((L : ℤ) * j) * γ = γ' * lowSL ((L : ℤ) * (τidx p L γ j : ℕ)) := by
  have hdet : (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hLc : (L : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h := hγ; rw [CongruenceSubgroup.Gamma0_mem] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  have hpc : (p : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := (Int.natCast_dvd_natCast.mpr hp).trans hLc
  have had := ad_eq_one hpc
  set a : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 with ha
  set b : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1 with hb
  set c : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 with hc
  set d : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 with hd
  set c' : ℤ := c / (L : ℤ) with hc'
  have hcc : (L : ℤ) * c' = c := Int.mul_ediv_cancel' hLc
  set j' : ℕ := τidx p L γ j with hj'
  have hj'σ : j' = σ (q := p) c' a j := rfl
  have hγmat : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![a, b; c, d] := by
    rw [ha, hb, hc, hd]; exact Matrix.eta_fin_two _
  have hL0 : ((L : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff L p).mpr hp

  have hdiv : (p : ℤ) ∣ (j : ℤ) * a + c' - ((L : ℤ) * j * b + d) * (j' : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hjc : ((j' : ℕ) : ZMod p) = ((c' : ℤ) : ZMod p) * ((a : ℤ) : ZMod p)
        + ((j : ℕ) : ZMod p) * ((a : ℤ) : ZMod p) * ((a : ℤ) : ZMod p) := by
      rw [hj'σ, σ_cast]
    push_cast
    rw [hL0, hjc]
    linear_combination (-(((j : ℕ) : ZMod p) * ((a : ℤ) : ZMod p) + ((c' : ℤ) : ZMod p))) * had
  obtain ⟨e, he⟩ := hdiv
  have hdetγ' : Matrix.det !![a - b * (L : ℤ) * (j' : ℤ), b; (L : ℤ) * (p : ℤ) * e, (L : ℤ) * j * b + d]
      = 1 := by
    rw [Matrix.det_fin_two_of]
    linear_combination hdet + b * (L : ℤ) * he - b * hcc
  refine ⟨⟨_, hdetγ'⟩, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    show (((L : ℤ) * (p : ℤ) * e : ℤ) : ZMod (L * p)) = 0
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨e, by push_cast; ring⟩
  · show (lowSL ((L : ℤ) * j) * γ : SL(2, ℤ)) = ⟨_, hdetγ'⟩ * lowSL ((L : ℤ) * (j' : ℕ))
    apply Subtype.ext
    show (lowSL ((L : ℤ) * j) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ)
      = !![a - b * (L : ℤ) * (j' : ℤ), b; (L : ℤ) * (p : ℤ) * e, (L : ℤ) * j * b + d]
        * (lowSL ((L : ℤ) * (j' : ℕ)) : Matrix (Fin 2) (Fin 2) ℤ)
    rw [hγmat, lowSL_coe, lowSL_coe, Matrix.mul_fin_two, Matrix.mul_fin_two]
    refine Matrix.ext fun i k => ?_
    fin_cases i <;> fin_cases k
    · show (1 * a + 0 * c : ℤ) = (a - b * (L : ℤ) * (j' : ℤ)) * 1 + b * ((L : ℤ) * (j' : ℕ)); ring
    · show (1 * b + 0 * d : ℤ) = (a - b * (L : ℤ) * (j' : ℤ)) * 0 + b * 1; ring
    · show ((L : ℤ) * j * a + 1 * c : ℤ)
        = (L : ℤ) * (p : ℤ) * e * 1 + ((L : ℤ) * j * b + d) * ((L : ℤ) * (j' : ℕ))
      linear_combination (L : ℤ) * he - hcc
    · show ((L : ℤ) * j * b + 1 * d : ℤ) = (L : ℤ) * (p : ℤ) * e * 0 + ((L : ℤ) * j * b + d) * 1; ring

theorem exists_conj_GL {L p : ℕ} [NeZero p] (hp : p ∣ L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 L) (j : ℕ) :
    ∃ γ' : SL(2, ℤ), γ' ∈ CongruenceSubgroup.Gamma0 (L * p) ∧
      β L j * (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
        = (Matrix.SpecialLinearGroup.mapGL ℝ γ' : GL (Fin 2) ℝ) * β L (τidx p L γ j) := by
  obtain ⟨γ', hγ', hconj⟩ := exists_conj hp hγ j
  refine ⟨γ', hγ', ?_⟩
  unfold β
  rw [← map_mul, ← map_mul, hconj]

theorem τinv_τidx {L p : ℕ} [NeZero p] (hp : p ∣ L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 L) {j : ℕ} (hj : j < p) : τinv p L γ (τidx p L γ j) = j := by
  have hLc : (L : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h := hγ; rw [CongruenceSubgroup.Gamma0_mem] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  have had := ad_eq_one ((Int.natCast_dvd_natCast.mpr hp).trans hLc)
  unfold τinv τidx
  exact σinv_σ (by rw [mul_comm]; exact had) hj

theorem τidx_τinv {L p : ℕ} [NeZero p] (hp : p ∣ L) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 L) {j : ℕ} (hj : j < p) : τidx p L γ (τinv p L γ j) = j := by
  have hLc : (L : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    have h := hγ; rw [CongruenceSubgroup.Gamma0_mem] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
  have had := ad_eq_one ((Int.natCast_dvd_natCast.mpr hp).trans hLc)
  unfold τinv τidx
  exact σ_σinv (by rw [mul_comm]; exact had) hj

theorem τidx_lt {L p : ℕ} [NeZero p] (γ : SL(2, ℤ)) (j : ℕ) : τidx p L γ j < p := σ_lt _ _ _

theorem τinv_lt {L p : ℕ} [NeZero p] (γ : SL(2, ℤ)) (j : ℕ) : τinv p L γ j < p := σinv_lt _ _ _ _

def trRaw (L p : ℕ) (F : ℍ → ℂ) : ℍ → ℂ := ∑ j ∈ Finset.range p, F ∣[(2 : ℤ)] β L j

theorem trRaw_slash_eq {M L p : ℕ} [NeZero p] (hLp : L * p = M) (hp : p ∣ L)
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) 2) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 L) :
    trRaw L p ⇑F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = trRaw L p ⇑F := by
  unfold trRaw
  rw [sum_slash]
  have hterm : ∀ j ∈ Finset.range p,
      (⇑F ∣[(2 : ℤ)] β L j) ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
        = ⇑F ∣[(2 : ℤ)] β L (τidx p L γ j) := by
    intro j _
    obtain ⟨γ', hγ', hconj⟩ := exists_conj_GL hp hγ j
    rw [← SlashAction.slash_mul, hconj, SlashAction.slash_mul]
    congr 1
    rw [hLp] at hγ'
    exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map.mpr ⟨γ', hγ', rfl⟩)
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_nbij' (τidx p L γ) (τinv p L γ) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_range.mpr (τidx_lt γ j)
  · intro j _; exact Finset.mem_range.mpr (τinv_lt γ j)
  · intro j hj; exact τinv_τidx hp hγ (Finset.mem_range.mp hj)
  · intro j hj; exact τidx_τinv hp hγ (Finset.mem_range.mp hj)
  · intro j _; rfl

theorem isZeroAt_sum {ι : Type*} (s : Finset ι) {c : OnePoint ℝ} {k : ℤ} (f : ι → ℍ → ℂ)
    (hf : ∀ i ∈ s, IsZeroAt c (f i) k) : IsZeroAt c (∑ i ∈ s, f i) k := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g _
    rw [Finset.sum_empty, SlashAction.zero_slash]
    exact Filter.zero_zeroAtFilter _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isCusp_lowSL_smul {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (x : ℤ) :
    IsCusp ((Matrix.SpecialLinearGroup.mapGL ℝ (lowSL x) : GL (Fin 2) ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff'] at hc ⊢
  obtain ⟨γ₀, rfl⟩ := hc
  exact ⟨lowSL x * γ₀, by rw [map_mul, mul_smul]⟩

theorem mdifferentiable_trRaw {M : ℕ} (L p : ℕ) (F : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (trRaw L p ⇑F) := by
  unfold trRaw
  exact MDifferentiable.sum fun j _ => (CuspFormClass.holo F).slash (2 : ℤ) (β L j)

theorem isZeroAt_trRaw {M : ℕ} [NeZero M] (L p : ℕ) (F : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) : IsZeroAt c (trRaw L p ⇑F) 2 := by
  unfold trRaw
  refine isZeroAt_sum _ _ fun j _ => ?_
  refine IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps F ?_)
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z]
  exact isCusp_lowSL_smul hc _

def trd {M L p : ℕ} [NeZero M] [NeZero L] [NeZero p] (hLp : L * p = M) (hp : p ∣ L)
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) 2) : CuspForm (CongruenceSubgroup.Gamma0 L) 2 where
  toFun := trRaw L p ⇑F
  slash_action_eq' γ hγ := by
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hγ
    exact trRaw_slash_eq hLp hp F hg
  holo' := mdifferentiable_trRaw L p F
  zero_at_cusps' {c} hc :=
    isZeroAt_trRaw L p F ((Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z _).mp hc)

theorem coe_trd {M L p : ℕ} [NeZero M] [NeZero L] [NeZero p] (hLp : L * p = M) (hp : p ∣ L)
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    ⇑(trd hLp hp F) = ∑ j ∈ Finset.range p, ⇑F ∣[(2 : ℤ)] β L j := rfl

theorem trd_add {M L p : ℕ} [NeZero M] [NeZero L] [NeZero p] (hLp : L * p = M) (hp : p ∣ L)
    (F G : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    trd hLp hp (F + G) = trd hLp hp F + trd hLp hp G := by
  refine DFunLike.coe_injective ?_
  show ⇑(trd hLp hp (F + G)) = ⇑(trd hLp hp F + trd hLp hp G)
  rw [CuspForm.coe_add, coe_trd, coe_trd, coe_trd, CuspForm.coe_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [SlashAction.add_slash]

theorem trd_smul {M L p : ℕ} [NeZero M] [NeZero L] [NeZero p] (hLp : L * p = M) (hp : p ∣ L)
    (c : ℂ) (F : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    trd hLp hp (c • F) = c • trd hLp hp F := by
  refine DFunLike.coe_injective ?_
  show ⇑(trd hLp hp (c • F)) = ⇑(c • trd hLp hp F)
  rw [CuspForm.IsGLPos.coe_smul, coe_trd, coe_trd, CuspForm.IsGLPos.coe_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold β
  exact ModularForm.SL_smul_slash (2 : ℤ) (lowSL ((L : ℤ) * j)) ⇑F c

def trdLin {M L p : ℕ} [NeZero M] [NeZero L] [NeZero p] (hLp : L * p = M) (hp : p ∣ L) :
    CuspForm (CongruenceSubgroup.Gamma0 M) 2 →ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma0 L) 2 where
  toFun := trd hLp hp
  map_add' := trd_add hLp hp
  map_smul' := trd_smul hLp hp

theorem mapGL_coe_eq (s : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = (s : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) := rfl

theorem β_val (L j : ℕ) :
    ((β L j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), 0; (L : ℝ) * j, 1] := by
  unfold β
  rw [mapGL_coe_eq, lowSL_coe]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem β_zero (L : ℕ) : β L 0 = 1 := by
  apply Units.ext
  rw [β_val, Units.val_one]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem lowSL_mem_Gamma0 (L : ℕ) (j : ℕ) : lowSL ((L : ℤ) * j) ∈ CongruenceSubgroup.Gamma0 L := by
  rw [CongruenceSubgroup.Gamma0_mem, lowSL_coe]
  show ((((L : ℤ) * j : ℤ)) : ZMod L) = 0
  push_cast
  rw [ZMod.natCast_self, zero_mul]

set_option linter.unnecessarySeqFocus false in

theorem diag_mul_β {q R M : ℕ} (hq : q ≠ 0) (h : q * R = M) (j : ℕ) :
    heckeDiagMatrix q * β M j = β R j * heckeDiagMatrix q := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, val_heckeDiagMatrix hq, β_val, β_val]
  have hM : (M : ℝ) = (q : ℝ) * R := by exact_mod_cast h.symm
  ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hM] <;> ring

theorem heckeDiagMatrix_one : heckeDiagMatrix 1 = 1 := by
  apply Units.ext
  rw [val_heckeDiagMatrix one_ne_zero, Units.val_one]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem sub_slash (k : ℤ) (g : GL (Fin 2) ℝ) (f f' : ℍ → ℂ) :
    (f - f') ∣[k] g = f ∣[k] g - f' ∣[k] g := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]

theorem trd_rescaleLin_one {m p : ℕ} [NeZero m] [NeZero (m * p)] [NeZero p] (hpm : p ∣ m)
    (h1 : 1 * m ∣ m * p) (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2) :
    trd (M := m * p) rfl hpm (FreyPackage.ModMCarrier.rescaleLin h1 2 F) = (p : ℂ) • F := by
  refine DFunLike.coe_injective ?_
  show ⇑(trd (M := m * p) rfl hpm (FreyPackage.ModMCarrier.rescaleLin h1 2 F)) = ⇑((p : ℂ) • F)
  rw [coe_trd, FreyPackage.ModMCarrier.coe_rescaleLin_apply, heckeDiagMatrix_one,
    SlashAction.slash_one, CuspForm.IsGLPos.coe_smul]
  have hterm : ∀ j ∈ Finset.range p, ⇑F ∣[(2 : ℤ)] β m j = ⇑F := by
    intro j _
    exact SlashInvariantFormClass.slash_action_eq F _
      (Subgroup.mem_map.mpr ⟨lowSL ((m : ℤ) * j), lowSL_mem_Gamma0 m j, rfl⟩)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℂ]

theorem trd_rescaleLin_of_ne {m p q R : ℕ} [NeZero m] [NeZero (m * p)] [NeZero p] [NeZero R]
    [NeZero (R * p)] (hpm : p ∣ m) (hq : q ≠ 0) (hqR : q * R = m) (hpR : p ∣ R)
    (hqR' : q * (R * p) ∣ m * p) (h : CuspForm (CongruenceSubgroup.Gamma0 (R * p)) 2) :
    trd (M := m * p) rfl hpm (FreyPackage.ModMCarrier.rescaleLin hqR' 2 h)
      = FreyPackage.ModMCarrier.rescaleLin (Dvd.intro 1 ((mul_one _).trans hqR) : q * R ∣ m) 2
          (trd (M := R * p) rfl hpR h) := by
  refine DFunLike.coe_injective ?_
  show ⇑(trd (M := m * p) rfl hpm (FreyPackage.ModMCarrier.rescaleLin hqR' 2 h))
    = ⇑(FreyPackage.ModMCarrier.rescaleLin (Dvd.intro 1 ((mul_one _).trans hqR) : q * R ∣ m) 2
          (trd (M := R * p) rfl hpR h))
  rw [coe_trd, FreyPackage.ModMCarrier.coe_rescaleLin_apply,
    FreyPackage.ModMCarrier.coe_rescaleLin_apply, coe_trd, sum_slash]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← SlashAction.slash_mul, diag_mul_β hq hqR j, SlashAction.slash_mul]

theorem lowSL_mul_S (c : ℤ) : lowSL c * ModularGroup.S = ModularGroup.S * ModularGroup.T ^ (-c) := by
  apply Subtype.ext
  show (lowSL c : Matrix (Fin 2) (Fin 2) ℤ) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ)
    = (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * ((ModularGroup.T ^ (-c) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [lowSL_coe, ModularGroup.coe_S, ModularGroup.coe_T_zpow]
  ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowSL_eq (c : ℤ) : lowSL c = ModularGroup.S * ModularGroup.T ^ (-c) * ModularGroup.S⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, lowSL_mul_S]

theorem hΓ (M : ℕ) [NeZero M] : (1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 M : Subgroup SL(2, ℤ)) :
    Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp

def qCoeffLin (M n : ℕ) [NeZero M] : CuspForm (CongruenceSubgroup.Gamma0 M) 2 →ₗ[ℂ] ℂ where
  toFun G := ModularFormClass.qCoeff G n
  map_add' f g := by
    show ModularFormClass.qCoeff (⇑(f + g)) n = _
    unfold ModularFormClass.qCoeff
    rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (hΓ M) f g, map_add]
  map_smul' c f := by
    show ModularFormClass.qCoeff (⇑(c • f)) n = _
    unfold ModularFormClass.qCoeff
    rw [CuspForm.IsGLPos.coe_smul, ModularForm.qExpansion_smul one_pos (hΓ M), _root_.map_smul]
    rfl

theorem qCoeffLin_apply (M n : ℕ) [NeZero M] (G : CuspForm (CongruenceSubgroup.Gamma0 M) 2) :
    qCoeffLin M n G = ModularFormClass.qCoeff G n := rfl

theorem qCoeff_zero' (M n : ℕ) [NeZero M] :
    ModularFormClass.qCoeff (0 : CuspForm (CongruenceSubgroup.Gamma0 M) 2) n = 0 := by
  rw [← qCoeffLin_apply, map_zero]

theorem qCoeff_sub_smul {M : ℕ} [NeZero M] (A B : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (c : ℂ)
    (n : ℕ) : ModularFormClass.qCoeff (⇑(A - c • B)) n
      = ModularFormClass.qCoeff (⇑A) n - c * ModularFormClass.qCoeff (⇑B) n := by
  rw [← qCoeffLin_apply, map_sub, _root_.map_smul, qCoeffLin_apply, qCoeffLin_apply, smul_eq_mul]

theorem rescaleLin_apply' {d R M : ℕ} [NeZero M] [NeZero R] (hdRM : d * R ∣ M) (hd : d ≠ 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (τ : ℍ) :
    FreyPackage.ModMCarrier.rescaleLin hdRM 2 f τ = (d : ℂ) * f (heckeDiagMatrix d • τ) := by
  rw [show FreyPackage.ModMCarrier.rescaleLin hdRM 2 f τ
      = (⇑(FreyPackage.ModMCarrier.rescaleLin hdRM 2 f)) τ from rfl,
    FreyPackage.ModMCarrier.coe_rescaleLin_apply, slash_heckeDiagMatrix_apply 2 hd]
  norm_num

theorem qCoeff_rescaleLin {d R M : ℕ} [NeZero M] [NeZero R] (hdRM : d * R ∣ M) (hd : d ≠ 0)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (n : ℕ) :
    ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f) n
      = if d ∣ n then (d : ℂ) * ModularFormClass.qCoeff f (n / d) else 0 := by
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hfun : (fun τ : ℍ => f (heckeDiagMatrix d • τ))
      = (d : ℂ)⁻¹ • ⇑(FreyPackage.ModMCarrier.rescaleLin hdRM 2 f) := by
    funext τ
    rw [Pi.smul_apply, smul_eq_mul, rescaleLin_apply' hdRM hd, ← mul_assoc, inv_mul_cancel₀ hdC,
      one_mul]
  have h1 := ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f (hΓ R) hd n
  rw [hfun] at h1
  have h2 : ModularFormClass.qCoeff ((d : ℂ)⁻¹ • ⇑(FreyPackage.ModMCarrier.rescaleLin hdRM 2 f)) n
      = (d : ℂ)⁻¹ * ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hdRM 2 f) n := by
    unfold ModularFormClass.qCoeff
    rw [ModularForm.qExpansion_smul one_pos (hΓ M), _root_.map_smul, smul_eq_mul]
  rw [h2] at h1
  have h3 := congrArg (fun z : ℂ => (d : ℂ) * z) h1
  rw [← mul_assoc, mul_inv_cancel₀ hdC, one_mul] at h3
  rw [h3]
  split_ifs <;> simp

theorem qCoeff_rescaleLin_one {R M : ℕ} [NeZero M] [NeZero R] (h1 : 1 * R ∣ M)
    (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) (n : ℕ) :
    ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin h1 2 f) n = ModularFormClass.qCoeff f n := by
  rw [qCoeff_rescaleLin h1 one_ne_zero, if_pos (one_dvd n), Nat.cast_one, one_mul, Nat.div_one]

theorem heckeDiagMatrix_mul {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    heckeDiagMatrix (a * b) = heckeDiagMatrix a * heckeDiagMatrix b := by
  apply Units.ext
  rw [Units.val_mul, val_heckeDiagMatrix (Nat.mul_ne_zero ha hb), val_heckeDiagMatrix ha,
    val_heckeDiagMatrix hb]
  ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem rescaleLin_rescaleLin {a b R M₁ M : ℕ} [NeZero R] [NeZero M₁] [NeZero M] (ha : a ≠ 0)
    (hb : b ≠ 0) (hbR : b * R ∣ M₁) (haM : a * M₁ ∣ M) (hab : a * b * R ∣ M)
    (x : S R) :
    FreyPackage.ModMCarrier.rescaleLin haM 2 (FreyPackage.ModMCarrier.rescaleLin hbR 2 x)
      = FreyPackage.ModMCarrier.rescaleLin hab 2 x := by
  refine DFunLike.coe_injective ?_
  show ⇑(FreyPackage.ModMCarrier.rescaleLin haM 2 (FreyPackage.ModMCarrier.rescaleLin hbR 2 x))
    = ⇑(FreyPackage.ModMCarrier.rescaleLin hab 2 x)
  rw [FreyPackage.ModMCarrier.coe_rescaleLin_apply, FreyPackage.ModMCarrier.coe_rescaleLin_apply,
    FreyPackage.ModMCarrier.coe_rescaleLin_apply, ← SlashAction.slash_mul, ← heckeDiagMatrix_mul hb ha,
    mul_comm b a]

theorem lowSL_mul_lowSL (x y : ℤ) : lowSL x * lowSL y = lowSL (x + y) := by
  apply Subtype.ext
  show (lowSL x : Matrix (Fin 2) (Fin 2) ℤ) * (lowSL y : Matrix (Fin 2) (Fin 2) ℤ) = lowSL (x + y)
  rw [lowSL_coe, lowSL_coe, lowSL_coe]
  ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem trd_rescaleLin_q {A B C q : ℕ} [NeZero A] [NeZero B] [NeZero C] [NeZero q]
    (hBq : B * q = A) (hqB : q ∣ B) (hCq : C * q = B) (hqC : q ∣ C)
    (h1 : q * B ∣ A) (h2 : q * C ∣ B) (x : S B) :
    trd hBq hqB (FreyPackage.ModMCarrier.rescaleLin h1 2 x)
      = FreyPackage.ModMCarrier.rescaleLin h2 2 (trd hCq hqC x) := by
  refine DFunLike.coe_injective ?_
  show ⇑(trd hBq hqB (FreyPackage.ModMCarrier.rescaleLin h1 2 x))
    = ⇑(FreyPackage.ModMCarrier.rescaleLin h2 2 (trd hCq hqC x))
  rw [coe_trd, FreyPackage.ModMCarrier.coe_rescaleLin_apply, FreyPackage.ModMCarrier.coe_rescaleLin_apply,
    coe_trd, sum_slash]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← SlashAction.slash_mul, diag_mul_β (NeZero.ne q) ((mul_comm q C).trans hCq) j, SlashAction.slash_mul]

section reindex

variable {q : ℕ} [NeZero q]

def πmul (c : ℕ) (j : ℕ) : ℕ := ((c * j : ℕ) : ZMod q).val

def πinv' (c : ℕ) (j : ℕ) : ℕ := (((c : ZMod q))⁻¹ * (j : ZMod q)).val

theorem πmul_lt (c j : ℕ) : πmul (q := q) c j < q := ZMod.val_lt _

theorem πinv'_lt (c j : ℕ) : πinv' (q := q) c j < q := ZMod.val_lt _

theorem πinv'_πmul {c : ℕ} (hc : c.Coprime q) {j : ℕ} (hj : j < q) :
    πinv' (q := q) c (πmul (q := q) c j) = j := by
  have hu : IsUnit (c : ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hc
  unfold πinv' πmul
  rw [ZMod.natCast_zmod_val, Nat.cast_mul, ← mul_assoc, ZMod.inv_mul_of_unit _ hu, one_mul,
    ZMod.val_cast_of_lt hj]

theorem πmul_πinv' {c : ℕ} (hc : c.Coprime q) {j : ℕ} (hj : j < q) :
    πmul (q := q) c (πinv' (q := q) c j) = j := by
  have hu : IsUnit (c : ZMod q) := (ZMod.isUnit_iff_coprime c q).mpr hc
  unfold πinv' πmul
  rw [Nat.cast_mul, ZMod.natCast_zmod_val, ← mul_assoc, ZMod.mul_inv_of_unit _ hu, one_mul,
    ZMod.val_cast_of_lt hj]

end reindex

theorem sum_slash_β_reindex {A A₀ q c : ℕ} [NeZero q] (hA : A₀ * q = A) (hc : c.Coprime q)
    (y : S A) :
    ∑ j ∈ Finset.range q, ⇑y ∣[(2 : ℤ)] β (A₀ * c) j
      = ∑ j ∈ Finset.range q, ⇑y ∣[(2 : ℤ)] β A₀ j := by
  have hterm : ∀ j ∈ Finset.range q,
      ⇑y ∣[(2 : ℤ)] β (A₀ * c) j = ⇑y ∣[(2 : ℤ)] β A₀ (πmul (q := q) c j) := by
    intro j _
    set t : ℕ := c * j / q with ht
    have hdiv : c * j = q * t + πmul (q := q) c j := by
      unfold πmul; rw [ZMod.val_natCast, ht]; exact (Nat.div_add_mod (c * j) q).symm
    have hmat : lowSL (((A₀ * c : ℕ) : ℤ) * j)
        = lowSL ((A : ℤ) * t) * lowSL ((A₀ : ℤ) * (πmul (q := q) c j : ℕ)) := by
      rw [lowSL_mul_lowSL]
      congr 1
      have h := congrArg (fun n : ℕ => (n : ℤ)) hdiv
      rw [← hA]
      push_cast at h ⊢
      linear_combination (A₀ : ℤ) * h
    unfold β
    rw [hmat, map_mul, SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq y _
      (Subgroup.mem_map.mpr ⟨_, lowSL_mem_Gamma0 A t, rfl⟩)
  rw [Finset.sum_congr rfl hterm]
  refine Finset.sum_nbij' (πmul (q := q) c) (πinv' (q := q) c) ?_ ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_range.mpr (πmul_lt c j)
  · intro j _; exact Finset.mem_range.mpr (πinv'_lt c j)
  · intro j hj; exact πinv'_πmul hc (Finset.mem_range.mp hj)
  · intro j hj; exact πmul_πinv' hc (Finset.mem_range.mp hj)
  · intro j _; rfl

theorem sum_slash_conj_eq (q P : ℕ) (φ : ℍ → ℂ) :
    ∑ j ∈ Finset.range q,
        φ ∣[(2 : ℤ)] (ModularGroup.S * ModularGroup.T ^ (-((P * j : ℕ) : ℤ)) * ModularGroup.S⁻¹)
      = ∑ j ∈ Finset.range q, φ ∣[(2 : ℤ)] β P j := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (-((P * j : ℕ) : ℤ)) = -((P : ℤ) * j) := by push_cast; ring
  rw [hc, ← lowSL_eq]
  rfl

def J (q N : ℕ) [NeZero N] : Submodule ℂ (S N) :=
  Submodule.span ℂ {F | ∃ (p N' : ℕ) (h : p * N' ∣ N) (x : S N'),
    p.Prime ∧ p ≠ q ∧ p * N' = N ∧ F = FreyPackage.ModMCarrier.rescaleLin h 2 x}

def Tw (q N : ℕ) [NeZero N] {R' : ℕ} (g' : S R') : Submodule ℂ (S N) :=
  Submodule.span ℂ {F | ∃ (i : ℕ) (h : q ^ i * R' ∣ N),
    1 ≤ i ∧ F = FreyPackage.ModMCarrier.rescaleLin h 2 g'}

theorem rescaleLin_mem_J {q N p N' : ℕ} [NeZero N] (h : p * N' ∣ N) (x : S N') (hp : p.Prime)
    (hpq : p ≠ q) (hpN : p * N' = N) : FreyPackage.ModMCarrier.rescaleLin h 2 x ∈ J q N :=
  Submodule.subset_span ⟨p, N', h, x, hp, hpq, hpN, rfl⟩

theorem qCoeff_eq_zero_of_mem_J {q N : ℕ} [NeZero N] (n : ℕ)
    (hn : ∀ p : ℕ, p.Prime → p ≠ q → ¬ p ∣ n) :
    ∀ F ∈ J q N, ModularFormClass.qCoeff F n = 0 := by
  intro F hF
  have hle : J q N ≤ LinearMap.ker (qCoeffLin N n) := by
    refine Submodule.span_le.mpr ?_
    rintro F ⟨p, N', h, x, hp, hpq, hpN, rfl⟩
    haveI : NeZero N' := ⟨fun h0 => NeZero.ne N (by rw [← hpN, h0, mul_zero])⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, qCoeffLin_apply, qCoeff_rescaleLin h hp.ne_zero,
      if_neg (hn p hp hpq)]
  have := hle hF
  rwa [LinearMap.mem_ker, qCoeffLin_apply] at this

theorem prime_not_dvd_pow {q p : ℕ} (hq : q.Prime) (i : ℕ) (hp : p.Prime) (hpq : p ≠ q) :
    ¬ p ∣ q ^ i := fun h =>
  hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h))

theorem trd_mem_J {L₀ q : ℕ} [NeZero (L₀ * q)] [NeZero L₀] [NeZero q] (hq : q.Prime)
    (hqL₀ : q ∣ L₀) :
    ∀ F ∈ J q (L₀ * q), trd (M := L₀ * q) rfl hqL₀ F ∈ J q L₀ := by
  intro F hF
  have hle : J q (L₀ * q) ≤ (J q L₀).comap (trdLin (M := L₀ * q) rfl hqL₀) := by
    refine Submodule.span_le.mpr ?_
    rintro F ⟨p, N', h, x, hp, hpq, hpN, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap]
    show trd (M := L₀ * q) rfl hqL₀ (FreyPackage.ModMCarrier.rescaleLin h 2 x) ∈ J q L₀
    have hpL₀ : p ∣ L₀ := by
      have h1 : p ∣ L₀ * q := ⟨N', hpN.symm⟩
      rcases (Nat.Prime.dvd_mul hp).mp h1 with h2 | h2
      · exact h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp h2) hpq
    obtain ⟨N'', hN''⟩ := hpL₀
    have hN' : N' = N'' * q := by
      apply Nat.eq_of_mul_eq_mul_left hp.pos
      rw [hpN, hN'']; ring
    subst hN'
    haveI : NeZero N'' := ⟨fun h0 => NeZero.ne L₀ (by rw [hN'', h0, mul_zero])⟩
    haveI : NeZero (N'' * q) := ⟨Nat.mul_ne_zero (NeZero.ne N'') hq.ne_zero⟩
    have hqN'' : q ∣ N'' := by
      have h1 : q ∣ p * N'' := hN'' ▸ hqL₀
      rcases (Nat.Prime.dvd_mul hq).mp h1 with h2 | h2
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp h2) (Ne.symm hpq)
      · exact h2
    have hpN'' : p * N'' = L₀ := hN''.symm
    rw [trd_rescaleLin_of_ne (m := L₀) (p := q) (q := p) (R := N'') hqL₀ hp.ne_zero hpN'' hqN'' h x]
    exact rescaleLin_mem_J _ _ hp hpq hpN''
  exact hle hF

theorem one_lt_q {q : ℕ} (hq : q.Prime) : 1 < q := hq.one_lt

theorem qCoeff_tower {q N R' : ℕ} [NeZero N] [NeZero R'] (hq : q.Prime) {i : ℕ} (h : q ^ i * R' ∣ N)
    (g' : S R') (j : ℕ) :
    ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin h 2 g') (q ^ j)
      = if i ≤ j then (q : ℂ) ^ i * ModularFormClass.qCoeff g' (q ^ (j - i)) else 0 := by
  rw [qCoeff_rescaleLin h (pow_ne_zero i hq.ne_zero)]
  by_cases hij : i ≤ j
  · rw [if_pos ((Nat.pow_dvd_pow_iff_le_right hq.one_lt).mpr hij), if_pos hij, Nat.pow_div hij hq.pos,
      Nat.cast_pow]
  · rw [if_neg (fun h' => hij ((Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp h')), if_neg hij]

section tower

variable {L₀ q : ℕ} [NeZero (L₀ * q)] [NeZero L₀] [NeZero q]

theorem trd_rescaleLin_of_dvd (hqL₀ : q ∣ L₀) {d N : ℕ} [NeZero N]
    (hdN : d * N ∣ L₀ * q) (hdN₀ : d * N ∣ L₀) (x : S N) :
    trd (M := L₀ * q) rfl hqL₀ (FreyPackage.ModMCarrier.rescaleLin hdN 2 x)
      = (q : ℂ) • FreyPackage.ModMCarrier.rescaleLin hdN₀ 2 x := by
  have h1 : 1 * L₀ ∣ L₀ * q := ⟨q, by ring⟩
  have hfac : FreyPackage.ModMCarrier.rescaleLin hdN 2 x
      = FreyPackage.ModMCarrier.rescaleLin h1 2 (FreyPackage.ModMCarrier.rescaleLin hdN₀ 2 x) := by
    refine DFunLike.coe_injective ?_
    show ⇑(FreyPackage.ModMCarrier.rescaleLin hdN 2 x)
      = ⇑(FreyPackage.ModMCarrier.rescaleLin h1 2 (FreyPackage.ModMCarrier.rescaleLin hdN₀ 2 x))
    rw [FreyPackage.ModMCarrier.coe_rescaleLin_apply, FreyPackage.ModMCarrier.coe_rescaleLin_apply,
      FreyPackage.ModMCarrier.coe_rescaleLin_apply, heckeDiagMatrix_one, SlashAction.slash_one]
  rw [hfac, trd_rescaleLin_one hqL₀ h1]

theorem trd_rescaleLin_one_newform_eq_zero (hq : q.Prime) (hqL₀ : q ∣ L₀) {R R₀ c : ℕ} [NeZero R]
    [NeZero R₀] (hRq : R₀ * q = R) (hqR₀ : q ∣ R₀) (hc : R₀ * c = L₀) (hcq : c.Coprime q)
    (h1 : 1 * R ∣ L₀ * q) {g : S R} (hg : CuspForm.IsNewform g) :
    trd (M := L₀ * q) rfl hqL₀ (FreyPackage.ModMCarrier.rescaleLin h1 2 g) = 0 := by
  refine DFunLike.coe_injective ?_
  show ⇑(trd (M := L₀ * q) rfl hqL₀ (FreyPackage.ModMCarrier.rescaleLin h1 2 g)) = ⇑(0 : S L₀)
  rw [coe_trd, FreyPackage.ModMCarrier.coe_rescaleLin_apply, heckeDiagMatrix_one, SlashAction.slash_one,
    CuspForm.coe_zero, ← hc, sum_slash_β_reindex hRq hcq g, ← sum_slash_conj_eq]
  exact hg.sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero hq ((mul_comm q R₀).trans hRq) hqR₀

theorem trd_tower_two_one (hq : q.Prime) (hqL₀ : q ∣ L₀) {R' R₁' c : ℕ} [NeZero R']
    (hR' : q * R₁' = R') (hqR₁' : ¬ q ∣ R₁') (hc : R' * c = L₀) (hcq : c.Coprime q)
    (hqR' : q ^ 1 * R' ∣ L₀ * q) (h1 : 1 * R' ∣ L₀) {g' : S R'} (hg' : CuspForm.IsNewform g') :
    trd (M := L₀ * q) rfl hqL₀ (FreyPackage.ModMCarrier.rescaleLin hqR' 2 g')
      = ModularFormClass.qCoeff g' q • FreyPackage.ModMCarrier.rescaleLin h1 2 g' := by
  haveI : NeZero (R' * q) := ⟨Nat.mul_ne_zero (NeZero.ne R') hq.ne_zero⟩
  refine DFunLike.coe_injective ?_
  show ⇑(trd (M := L₀ * q) rfl hqL₀ (FreyPackage.ModMCarrier.rescaleLin hqR' 2 g'))
    = ⇑(ModularFormClass.qCoeff g' q • FreyPackage.ModMCarrier.rescaleLin h1 2 g')
  rw [coe_trd, FreyPackage.ModMCarrier.coe_rescaleLin_apply, pow_one, CuspForm.IsGLPos.coe_smul,
    FreyPackage.ModMCarrier.coe_rescaleLin_apply, heckeDiagMatrix_one, SlashAction.slash_one, ← hc]

  have hy : (⇑g' ∣[(2 : ℤ)] heckeDiagMatrix q)
      = ⇑(FreyPackage.ModMCarrier.rescaleLin (⟨1, by ring⟩ : q * R' ∣ R' * q) 2 g') :=
    (FreyPackage.ModMCarrier.coe_rescaleLin_apply _ 2 g').symm
  rw [hy, sum_slash_β_reindex rfl hcq, ← hy, ← sum_slash_conj_eq]
  exact hg'.sum_range_slash_heckeDiagMatrix_conj_eq_qCoeff_smul hq hR' hqR₁'

theorem trd_tower_two_zero (hq : q.Prime) (hqL₀ : q ∣ L₀) {R' c : ℕ} [NeZero R']
    (hqR' : ¬ q ∣ R') (hc : q * R' * c = L₀) (hcq : c.Coprime q)
    (hqqR' : q ^ 2 * R' ∣ L₀ * q) (hq1 : q * R' ∣ L₀) (h1 : 1 * R' ∣ L₀) (g' : S R') :
    trd (M := L₀ * q) rfl hqL₀ (FreyPackage.ModMCarrier.rescaleLin hqqR' 2 g')
      = FreyPackage.ModMCarrier.rescaleLin hq1 2 (CuspForm.heckeTLin 2 hq hqR' g')
        - FreyPackage.ModMCarrier.rescaleLin h1 2 g' := by
  haveI : NeZero (q * R') := ⟨Nat.mul_ne_zero hq.ne_zero (NeZero.ne R')⟩
  haveI : NeZero (q * R' * q) := ⟨Nat.mul_ne_zero (NeZero.ne (q * R')) hq.ne_zero⟩
  refine DFunLike.coe_injective ?_
  show ⇑(trd (M := L₀ * q) rfl hqL₀ (FreyPackage.ModMCarrier.rescaleLin hqqR' 2 g'))
    = ⇑(FreyPackage.ModMCarrier.rescaleLin hq1 2 (CuspForm.heckeTLin 2 hq hqR' g')
        - FreyPackage.ModMCarrier.rescaleLin h1 2 g')
  rw [coe_trd, FreyPackage.ModMCarrier.coe_rescaleLin_apply, CuspForm.coe_sub,
    FreyPackage.ModMCarrier.coe_rescaleLin_apply, FreyPackage.ModMCarrier.coe_rescaleLin_apply,
    CuspForm.coe_heckeTLin_apply, heckeDiagMatrix_one, SlashAction.slash_one, ← hc, sq,
    heckeDiagMatrix_mul hq.ne_zero hq.ne_zero, SlashAction.slash_mul]

  have hy : ((⇑g' ∣[(2 : ℤ)] heckeDiagMatrix q) ∣[(2 : ℤ)] heckeDiagMatrix q)
      = ⇑(FreyPackage.ModMCarrier.rescaleLin (⟨1, by ring⟩ : q * (q * R') ∣ q * R' * q) 2
          (FreyPackage.ModMCarrier.rescaleLin (dvd_refl (q * R')) 2 g')) := by
    rw [FreyPackage.ModMCarrier.coe_rescaleLin_apply, FreyPackage.ModMCarrier.coe_rescaleLin_apply]
  rw [hy, sum_slash_β_reindex rfl hcq, ← hy]
  have h := CuspForm.sum_range_slash_heckeDiagMatrix_heckeDiagMatrix_conj_eq g' hq hqR'
  rw [sum_slash_conj_eq] at h
  exact h

theorem qCoeff_one_trd_tower_top (hq : q.Prime) (hqL₀ : q ∣ L₀) {L₀₀ : ℕ} [NeZero L₀₀]
    (hL₀₀ : L₀₀ * q = L₀)
    {R' R₁' e T c : ℕ} [NeZero R'] (hR' : q ^ e * R₁' = R') (hT : 1 ≤ T)
    (hTe : 3 ≤ T + e) (hc : q ^ (T + e - 2) * R₁' * c = L₀₀) (hcq : c.Coprime q)
    (h : q ^ T * R' ∣ L₀ * q) {g' : S R'} (hg' : CuspForm.IsNewform g') :
    ModularFormClass.qCoeff (trd (M := L₀ * q) rfl hqL₀ (FreyPackage.ModMCarrier.rescaleLin h 2 g')) 1
      = 0 := by

  obtain ⟨T₀, rfl⟩ : ∃ T₀, T = T₀ + 1 := ⟨T - 1, by omega⟩
  have hfun : ⇑(trd (M := L₀ * q) rfl hqL₀ (FreyPackage.ModMCarrier.rescaleLin h 2 g'))
      = (∑ j ∈ Finset.range q, (⇑g' ∣[(2 : ℤ)] heckeDiagMatrix (q ^ T₀)) ∣[(2 : ℤ)] β L₀₀ j)
          ∣[(2 : ℤ)] heckeDiagMatrix q := by
    rw [coe_trd, FreyPackage.ModMCarrier.coe_rescaleLin_apply, pow_succ,
      heckeDiagMatrix_mul (pow_ne_zero T₀ hq.ne_zero) hq.ne_zero, SlashAction.slash_mul, sum_slash]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← SlashAction.slash_mul, diag_mul_β hq.ne_zero ((mul_comm q L₀₀).trans hL₀₀) j,
      SlashAction.slash_mul]

  rcases Nat.eq_zero_or_pos T₀ with hT0 | hT0
  ·
    subst hT0
    obtain ⟨e₀, rfl⟩ : ∃ e₀, e = e₀ + 2 := ⟨e - 2, by omega⟩

    have hR₀ : q ^ (e₀ + 1) * R₁' * q = R' := by rw [← hR']; ring
    haveI : NeZero (q ^ (e₀ + 1) * R₁' * q) := ⟨by rw [hR₀]; exact NeZero.ne R'⟩
    haveI : NeZero (q ^ (e₀ + 1) * R₁') :=
      ⟨fun h0 => NeZero.ne (q ^ (e₀ + 1) * R₁' * q) (by rw [h0, zero_mul])⟩
    have hcL : q ^ (e₀ + 1) * R₁' * c = L₀₀ := by
      rw [← hc, show 0 + 1 + (e₀ + 2) - 2 = e₀ + 1 by omega]
    have hinner : ∀ (y : S (q ^ (e₀ + 1) * R₁' * q)), CuspForm.IsNewform y →
        ∑ j ∈ Finset.range q, ⇑y ∣[(2 : ℤ)] β L₀₀ j = 0 := by
      intro y hy
      rw [← hcL, sum_slash_β_reindex rfl hcq y, ← sum_slash_conj_eq]
      exact hy.sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero hq (by ring) ⟨q ^ e₀ * R₁', by ring⟩

    subst hR₀
    rw [show ModularFormClass.qCoeff (trd (M := L₀ * q) rfl hqL₀
        (FreyPackage.ModMCarrier.rescaleLin h 2 g')) 1
        = ModularFormClass.qCoeff (⇑(trd (M := L₀ * q) rfl hqL₀
            (FreyPackage.ModMCarrier.rescaleLin h 2 g'))) 1 from rfl, hfun, pow_zero,
      heckeDiagMatrix_one]
    simp only [SlashAction.slash_one]
    rw [hinner g' hg', SlashAction.zero_slash]
    exact qCoeff_zero' L₀ 1
  ·
    obtain ⟨T₁, rfl⟩ : ∃ T₁, T₀ = T₁ + 1 := ⟨T₀ - 1, by omega⟩

    set A₀ : ℕ := q ^ T₁ * R' with hA₀
    haveI : NeZero A₀ := ⟨Nat.mul_ne_zero (pow_ne_zero T₁ hq.ne_zero) (NeZero.ne R')⟩
    haveI : NeZero (A₀ * q) := ⟨Nat.mul_ne_zero (NeZero.ne A₀) hq.ne_zero⟩
    have hqA₀ : q ∣ A₀ := by
      have h1 : 1 ≤ T₁ + e := by omega
      rcases Nat.eq_zero_or_pos T₁ with h0 | h0
      · subst h0
        obtain ⟨e₀, rfl⟩ : ∃ e₀, e = e₀ + 1 := ⟨e - 1, by omega⟩
        exact ⟨q ^ e₀ * R₁', by rw [hA₀, ← hR']; ring⟩
      · obtain ⟨T₂, rfl⟩ : ∃ T₂, T₁ = T₂ + 1 := ⟨T₁ - 1, by omega⟩
        exact ⟨q ^ T₂ * R', by rw [hA₀]; ring⟩

    have hA : q ^ (T₁ + 1) * R' ∣ A₀ * q := ⟨1, by rw [hA₀]; ring⟩
    set y : S (A₀ * q) := FreyPackage.ModMCarrier.rescaleLin hA 2 g' with hydef
    have hy : (⇑g' ∣[(2 : ℤ)] heckeDiagMatrix (q ^ (T₁ + 1))) = ⇑y := by
      rw [hydef, FreyPackage.ModMCarrier.coe_rescaleLin_apply]

    have hcA : A₀ * c = L₀₀ := by
      rw [← hc, hA₀, ← hR']
      have : T₁ + 1 + 1 + e - 2 = T₁ + e := by omega
      rw [this]; ring
    have hz : ∑ j ∈ Finset.range q, ⇑y ∣[(2 : ℤ)] β L₀₀ j = ⇑(trd (M := A₀ * q) rfl hqA₀ y) := by
      rw [coe_trd, ← hcA, sum_slash_β_reindex rfl hcq y]
    have hqA₀L : q * A₀ ∣ L₀ := by
      refine ⟨c, ?_⟩
      rw [← hL₀₀, ← hcA]; ring
    rw [show ModularFormClass.qCoeff (trd (M := L₀ * q) rfl hqL₀
        (FreyPackage.ModMCarrier.rescaleLin h 2 g')) 1
        = ModularFormClass.qCoeff (⇑(trd (M := L₀ * q) rfl hqL₀
            (FreyPackage.ModMCarrier.rescaleLin h 2 g'))) 1 from rfl, hfun, hy, hz,
      ← FreyPackage.ModMCarrier.coe_rescaleLin_apply hqA₀L 2]
    rw [show ModularFormClass.qCoeff (⇑(FreyPackage.ModMCarrier.rescaleLin hqA₀L 2
        (trd (M := A₀ * q) rfl hqA₀ y))) 1
        = ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hqA₀L 2
            (trd (M := A₀ * q) rfl hqA₀ y)) 1 from rfl,
      qCoeff_rescaleLin hqA₀L hq.ne_zero, if_neg (fun hq1 : q ∣ 1 => hq.one_lt.ne' (Nat.eq_one_of_dvd_one hq1))]

end tower

theorem exp_le_of_pow_mul_dvd {q L₁ a b X : ℕ} (hq : q.Prime) (hqL₁ : ¬ q ∣ L₁)
    (h : q ^ a * X ∣ q ^ b * L₁) : a ≤ b := by
  have hcop : Nat.Coprime (q ^ a) L₁ := Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqL₁)
  have h1 : q ^ a ∣ q ^ b * L₁ := (Dvd.intro X rfl).trans h
  have h2 : q ^ a ∣ q ^ b := hcop.dvd_of_dvd_mul_right h1
  exact (Nat.pow_dvd_pow_iff_le_right hq.one_lt).mp h2

theorem not_dvd_of_dvd {q X L₁ : ℕ} (hqL₁ : ¬ q ∣ L₁) (hX : X ∣ L₁) : ¬ q ∣ X :=
  fun h => hqL₁ (h.trans hX)

theorem coprime_of_dvd {q c L₁ : ℕ} (hq : q.Prime) (hqL₁ : ¬ q ∣ L₁) (hc : c ∣ L₁) : c.Coprime q :=
  (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr (not_dvd_of_dvd hqL₁ hc)))

theorem qCoeff_sub' {M : ℕ} [NeZero M] (A B : S M) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(A - B)) n = ModularFormClass.qCoeff (⇑A) n - ModularFormClass.qCoeff (⇑B) n := by
  rw [← qCoeffLin_apply, map_sub, qCoeffLin_apply, qCoeffLin_apply]

theorem notmem {L L₁ q m e R R₁ R' R₁' : ℕ} [NeZero L] (hq : q.Prime)
    (hL : q ^ m * L₁ = L) (hqL₁ : ¬ q ∣ L₁)
    (hR : q ^ m * R₁ = R) (hqR₁ : ¬ q ∣ R₁)
    (hR' : q ^ e * R₁' = R') (hqR₁' : ¬ q ∣ R₁') (he : e < m)
    {g : S R} {g' : S R'} (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g')
    (h1 : 1 * R ∣ L) (h1' : 1 * R' ∣ L) :
    FreyPackage.ModMCarrier.rescaleLin h1 2 g - FreyPackage.ModMCarrier.rescaleLin h1' 2 g'
      ∉ Tw q L g' ⊔ J q L := by
  intro hmem

  have hq0 : q ≠ 0 := hq.ne_zero
  have hL0 : L ≠ 0 := NeZero.ne L
  have hL₁0 : L₁ ≠ 0 := fun h0 => hL0 (by rw [← hL, h0, mul_zero])

  have hR₁ : R₁ ∣ L₁ := by
    refine Nat.dvd_of_mul_dvd_mul_left (pow_pos hq.pos m) ?_
    rw [hR, hL]; rw [one_mul] at h1; exact h1
  have hR₁' : R₁' ∣ L₁ := by
    have h2 : q ^ e * R₁' ∣ q ^ e * (q ^ (m - e) * L₁) := by
      rw [hR', ← mul_assoc, ← pow_add, show e + (m - e) = m by omega, hL]; rw [one_mul] at h1'; exact h1'
    have h3 : R₁' ∣ L₁ * q ^ (m - e) := by
      rw [mul_comm]; exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hq.pos e) h2
    exact (Nat.Coprime.pow_right (m - e)
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqR₁'))).dvd_of_dvd_mul_right h3
  have hR0 : R ≠ 0 := fun h0 => by
    rw [← hR, mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact pow_ne_zero m hq0 h0
    · exact hL₁0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hR₁))
  have hR'0 : R' ≠ 0 := fun h0 => by
    rw [← hR', mul_eq_zero] at h0
    rcases h0 with h0 | h0
    · exact pow_ne_zero e hq0 h0
    · exact hL₁0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hR₁'))
  haveI : NeZero R := ⟨hR0⟩
  haveI : NeZero R' := ⟨hR'0⟩
  haveI : NeZero q := ⟨hq0⟩
  have hqR : q ∣ R := ⟨q ^ (m - 1) * R₁, by
    rw [← hR, ← mul_assoc, ← pow_succ']; congr 2; omega⟩

  have ha1 : ModularFormClass.qCoeff g 1 = 1 := hg.1.qCoeff_one
  have ha1' : ModularFormClass.qCoeff g' 1 = 1 := hg'.1.qCoeff_one
  obtain ⟨ε, hε⟩ : ∃ ε : ℂ, ε = ModularFormClass.qCoeff g q := ⟨_, rfl⟩
  obtain ⟨lam, hlam⟩ : ∃ lam : ℂ, lam = ModularFormClass.qCoeff g' q := ⟨_, rfl⟩
  have hqR'v : ∀ (_ : e = 0), ¬ q ∣ R' := by
    intro he0 hdvd; subst he0
    rw [pow_zero, one_mul] at hR'
    exact hqR₁' (hR' ▸ hdvd)
  have hbad := CuspForm.newformBadPrimeCoeff R g hg q hq hqR

  have hd : ∀ n, ModularFormClass.qCoeff
      (⇑(FreyPackage.ModMCarrier.rescaleLin h1 2 g - FreyPackage.ModMCarrier.rescaleLin h1' 2 g')) n
      = ModularFormClass.qCoeff g n - ModularFormClass.qCoeff g' n := by
    intro n; rw [qCoeff_sub', qCoeff_rescaleLin_one, qCoeff_rescaleLin_one]

  have hexp : ∀ i : ℕ, q ^ i * R' ∣ L → i + e ≤ m := by
    intro i hi
    refine exp_le_of_pow_mul_dvd (X := R₁') hq hqL₁ ?_
    rw [hL, pow_add, mul_assoc, hR']; exact hi

  have hJ : ∀ (j : ℕ), ∀ F ∈ J q L, ModularFormClass.qCoeff F (q ^ j) = 0 := fun j =>
    qCoeff_eq_zero_of_mem_J (q ^ j) (fun p hp hpq => prime_not_dvd_pow hq j hp hpq)
  rcases Nat.lt_or_ge m 2 with hm | hm
  ·
    have hm1 : m = 1 := by omega
    subst hm1
    have he0 : e = 0 := by omega
    subst he0
    have hqR' : ¬ q ∣ R' := hqR'v rfl
    rw [pow_one] at hR hL

    have hsq : ¬ q ^ 2 ∣ R := by
      rintro ⟨c, hc⟩
      apply hqR₁
      refine ⟨c, Nat.eq_of_mul_eq_mul_left hq.pos ?_⟩
      rw [hR, hc]; ring
    have hε2 : ε ^ 2 = 1 := hε ▸ hbad.1 hsq
    have hgqq : ModularFormClass.qCoeff g (q ^ 2) = ε * ε := by
      have h := hg.1.qCoeff_prime_pow_of_dvd q 0 hq hqR
      simp only [zero_add, pow_one] at h; rw [hε]; exact h
    have hg'qq : ModularFormClass.qCoeff g' (q ^ 2) = lam * lam - q := by
      have h := hg'.1.qCoeff_prime_pow_of_not_dvd q 0 hq hqR'
      simp only [zero_add, pow_one, pow_zero, ha1', mul_one] at h; rw [hlam]; exact h

    let Ψ : S L →ₗ[ℂ] ℂ := lam • qCoeffLin L (q ^ 1) - qCoeffLin L (q ^ 2)
    have hΨ : ∀ F : S L, Ψ F = lam * ModularFormClass.qCoeff F (q ^ 1) - ModularFormClass.qCoeff F (q ^ 2) := by
      intro F; simp only [Ψ, LinearMap.sub_apply, LinearMap.smul_apply, qCoeffLin_apply, smul_eq_mul]
    have hTw : Tw q L g' ≤ LinearMap.ker Ψ := by
      refine Submodule.span_le.mpr ?_
      rintro F ⟨i, hi, hi1, rfl⟩
      have hile : i ≤ 1 := by have := hexp i hi; omega
      have hi1' : i = 1 := le_antisymm hile hi1
      subst hi1'
      rw [SetLike.mem_coe, LinearMap.mem_ker, hΨ, qCoeff_tower hq hi g' 1, qCoeff_tower hq hi g' 2,
        if_pos le_rfl, if_pos (by norm_num)]
      simp only [Nat.sub_self, pow_zero, ha1', pow_one, show 2 - 1 = 1 from rfl]
      rw [← hlam]; ring
    have hJker : J q L ≤ LinearMap.ker Ψ := by
      intro F hF
      rw [LinearMap.mem_ker, hΨ, hJ 1 F hF, hJ 2 F hF]; ring
    have hΨd := (sup_le hTw hJker) hmem
    rw [LinearMap.mem_ker, hΨ, pow_one, hd, hd, hgqq, hg'qq, ← hε, ← hlam] at hΨd

    have hprod : lam * ε = q + 1 := by
      have hε2' : ε * ε = 1 := by rw [← sq]; exact hε2
      linear_combination hΨd + hε2'

    have hnε : ‖ε‖ = 1 := by
      have h2 : ‖ε‖ ^ 2 = 1 ^ 2 := by rw [← norm_pow, hε2, norm_one, one_pow]
      exact (pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero).mp h2
    have hnlam : ‖lam‖ = q + 1 := by
      have h := congrArg norm hprod
      rw [norm_mul, hnε, mul_one] at h
      rw [h, show ((q : ℂ) + 1) = ((q + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    have heig : CuspForm.heckeTLin 2 hq hqR' g' = lam • g' := by
      rw [hlam]; exact (((CuspForm.isNormalizedEigenform_iff_heckeTLin g').mp hg'.1).2 q hq).1 hqR'
    have hlt := CuspForm.norm_lt_of_heckeTLin_eq_smul hg'.ne_zero hq hqR' heig
    rw [hnlam] at hlt
    exact lt_irrefl _ hlt
  ·
    obtain ⟨m₁, rfl⟩ : ∃ m₁, m = m₁ + 2 := ⟨m - 2, by omega⟩

    obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℕ, L₀ = q ^ (m₁ + 1) * L₁ := ⟨_, rfl⟩
    have hLf : L = L₀ * q := by rw [hL₀, ← hL]; ring
    subst hLf
    obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℕ, R₀ = q ^ (m₁ + 1) * R₁ := ⟨_, rfl⟩
    have hRq : R₀ * q = R := by rw [hR₀, ← hR]; ring
    haveI : NeZero L₀ := ⟨fun h0 => hL0 (by rw [h0, zero_mul])⟩
    haveI : NeZero (L₀ * q) := ⟨hL0⟩
    haveI : NeZero R₀ := ⟨fun h0 => hR0 (by rw [← hRq, h0, zero_mul])⟩
    have hqL₀ : q ∣ L₀ := ⟨q ^ m₁ * L₁, by rw [hL₀]; ring⟩
    have hqR₀ : q ∣ R₀ := ⟨q ^ m₁ * R₁, by rw [hR₀]; ring⟩
    obtain ⟨c, hc⟩ := hR₁
    have hcq : c.Coprime q := coprime_of_dvd hq hqL₁ ⟨R₁, by rw [hc]; ring⟩
    have hR₀c : R₀ * c = L₀ := by rw [hR₀, hL₀, hc]; ring
    obtain ⟨c', hc'⟩ := hR₁'
    have hc'q : c'.Coprime q := coprime_of_dvd hq hqL₁ ⟨R₁', by rw [hc']; ring⟩

    have hsq : q ^ 2 ∣ R := ⟨q ^ m₁ * R₁, by rw [← hR]; ring⟩
    have hε0 : ε = 0 := hε ▸ hbad.2 hsq
    have hgqq : ModularFormClass.qCoeff g (q ^ 2) = 0 := by
      have h := hg.1.qCoeff_prime_pow_of_dvd q 0 hq hqR
      simp only [zero_add, pow_one] at h; rw [h, ← hε, hε0, zero_mul]

    have h1'₀ : 1 * R' ∣ L₀ := by
      rw [one_mul, hL₀, ← hR', hc', show m₁ + 1 = e + (m₁ + 1 - e) by omega, pow_add]
      exact ⟨q ^ (m₁ + 1 - e) * c', by ring⟩

    let Φ₁ : S (L₀ * q) →ₗ[ℂ] ℂ := (qCoeffLin L₀ 1).comp (trdLin (M := L₀ * q) rfl hqL₀)
    have hΦ₁ : ∀ F : S (L₀ * q), Φ₁ F = ModularFormClass.qCoeff (trd (M := L₀ * q) rfl hqL₀ F) 1 := by
      intro F; rfl

    have hΦ₁J : ∀ F ∈ J q (L₀ * q), Φ₁ F = 0 := by
      intro F hF
      rw [hΦ₁]
      have h := qCoeff_eq_zero_of_mem_J (q := q) (N := L₀) (q ^ 0)
        (fun p hp hpq => prime_not_dvd_pow hq 0 hp hpq) _ (trd_mem_J hq hqL₀ F hF)
      rwa [pow_zero] at h

    have hΦ₁d : Φ₁ (FreyPackage.ModMCarrier.rescaleLin h1 2 g - FreyPackage.ModMCarrier.rescaleLin h1' 2 g')
        = -(q : ℂ) := by
      rw [map_sub, hΦ₁, hΦ₁, trd_rescaleLin_one_newform_eq_zero hq hqL₀ hRq hqR₀ hR₀c hcq h1 hg,
        trd_rescaleLin_of_dvd hqL₀ h1' h1'₀ g',
        show ModularFormClass.qCoeff (⇑((q : ℂ) • FreyPackage.ModMCarrier.rescaleLin h1'₀ 2 g')) 1
          = (q : ℂ) * ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin h1'₀ 2 g') 1 by
            rw [← qCoeffLin_apply, _root_.map_smul, qCoeffLin_apply, smul_eq_mul],
        qCoeff_rescaleLin_one, ha1', qCoeff_zero']
      ring

    have hΦ₁low : ∀ (i : ℕ) (hi : q ^ i * R' ∣ L₀ * q), 1 ≤ i → q ^ i * R' ∣ L₀ →
        Φ₁ (FreyPackage.ModMCarrier.rescaleLin hi 2 g') = 0 := by
      intro i hi hi1 hi₀
      rw [hΦ₁, trd_rescaleLin_of_dvd hqL₀ hi hi₀ g',
        show ModularFormClass.qCoeff (⇑((q : ℂ) • FreyPackage.ModMCarrier.rescaleLin hi₀ 2 g')) 1
          = (q : ℂ) * ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin hi₀ 2 g') 1 by
            rw [← qCoeffLin_apply, _root_.map_smul, qCoeffLin_apply, smul_eq_mul]]
      have h := qCoeff_tower hq hi₀ g' 0
      rw [pow_zero] at h
      rw [h, if_neg (by omega), mul_zero]

    have hlow_of : ∀ i : ℕ, i + e ≤ m₁ + 1 → q ^ i * R' ∣ L₀ := by
      intro i hie
      rw [hL₀, ← hR', hc', show m₁ + 1 = (i + e) + (m₁ + 1 - (i + e)) by omega, pow_add, pow_add]
      exact ⟨q ^ (m₁ + 1 - (i + e)) * c', by ring⟩
    rcases Nat.lt_or_ge m₁ 1 with hm₁ | hm₁
    ·
      have hm₁0 : m₁ = 0 := by omega
      subst hm₁0

      rcases Nat.lt_or_ge e 1 with he1 | he1
      ·
        have he0 : e = 0 := by omega
        subst he0
        have hqR' : ¬ q ∣ R' := hqR'v rfl
        have hR'₁ : R₁' = R' := by rw [← hR', pow_zero, one_mul]
        have hg'qq : ModularFormClass.qCoeff g' (q ^ 2) = lam * lam - q := by
          have h := hg'.1.qCoeff_prime_pow_of_not_dvd q 0 hq hqR'
          simp only [zero_add, pow_one, pow_zero, ha1', mul_one] at h; rw [hlam]; exact h
        let Ψ : S (L₀ * q) →ₗ[ℂ] ℂ :=
          ((q : ℂ) ^ 2) • Φ₁ - lam • qCoeffLin (L₀ * q) (q ^ 1) + qCoeffLin (L₀ * q) (q ^ 2)
        have hΨ : ∀ F, Ψ F = (q : ℂ) ^ 2 * Φ₁ F - lam * ModularFormClass.qCoeff F (q ^ 1)
            + ModularFormClass.qCoeff F (q ^ 2) := by
          intro F
          simp only [Ψ, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, qCoeffLin_apply,
            smul_eq_mul]
        have hTw : Tw q (L₀ * q) g' ≤ LinearMap.ker Ψ := by
          refine Submodule.span_le.mpr ?_
          rintro F ⟨i, hi, hi1, rfl⟩
          have hile : i ≤ 2 := by have := hexp i hi; omega
          rw [SetLike.mem_coe, LinearMap.mem_ker, hΨ, qCoeff_tower hq hi g' 1, qCoeff_tower hq hi g' 2]
          rcases Nat.lt_or_ge i 2 with hi2 | hi2
          ·
            have hi1' : i = 1 := by omega
            subst hi1'
            rw [hΦ₁low 1 hi le_rfl (hlow_of 1 (by omega)), if_pos le_rfl, if_pos (by norm_num)]
            simp only [Nat.sub_self, pow_zero, pow_one, show 2 - 1 = 1 from rfl, ha1']
            rw [← hlam]; ring
          ·
            have hi2' : i = 2 := le_antisymm hile hi2
            subst hi2'
            have hq1 : q * R' ∣ L₀ := by have h := hlow_of 1 (by omega); rwa [pow_one] at h
            have hΦ₁top : Φ₁ (FreyPackage.ModMCarrier.rescaleLin hi 2 g') = -1 := by
              have hcc : q * R' * c' = L₀ := by rw [hL₀, ← hR'₁, hc']; ring
              rw [hΦ₁, trd_tower_two_zero hq hqL₀ hqR' hcc hc'q hi hq1 h1'₀ g', qCoeff_sub',
                qCoeff_rescaleLin hq1 hq0, if_neg (fun hq1' : q ∣ 1 => hq.one_lt.ne' (Nat.eq_one_of_dvd_one hq1')),
                qCoeff_rescaleLin_one, ha1']
              ring
            rw [hΦ₁top, if_neg (by norm_num), if_pos le_rfl]
            simp only [Nat.sub_self, pow_zero, ha1']
            ring
        have hJker : J q (L₀ * q) ≤ LinearMap.ker Ψ := by
          intro F hF
          rw [LinearMap.mem_ker, hΨ, hΦ₁J F hF, hJ 1 F hF, hJ 2 F hF]; ring
        have hΨd := (sup_le hTw hJker) hmem
        rw [LinearMap.mem_ker, hΨ, hΦ₁d, pow_one, hd, hd, hgqq, hg'qq, ← hε, ← hlam, hε0] at hΨd

        have hq3 : (q : ℂ) * ((q : ℂ) ^ 2 - 1) = 0 := by linear_combination -hΨd
        rcases mul_eq_zero.mp hq3 with h0 | h0
        · exact hq0 (by exact_mod_cast h0)
        · have h1q : (q : ℂ) ^ 2 = 1 := sub_eq_zero.mp h0
          have : (q : ℕ) ^ 2 = 1 := by exact_mod_cast h1q
          have : q = 1 := by simpa using this
          exact hq.one_lt.ne' this
      ·
        have he1' : e = 1 := by omega
        subst he1'
        rw [pow_one] at hR'

        have hsq' : ¬ q ^ 2 ∣ R' := by
          rintro ⟨c₂, hc₂⟩
          apply hqR₁'
          refine ⟨c₂, Nat.eq_of_mul_eq_mul_left hq.pos ?_⟩
          rw [hR', hc₂]; ring
        have hlam2 : lam ^ 2 = 1 := hlam ▸ (CuspForm.newformBadPrimeCoeff R' g' hg' q hq ⟨R₁', hR'.symm⟩).1 hsq'
        let Ψ : S (L₀ * q) →ₗ[ℂ] ℂ := (q : ℂ) • Φ₁ - lam • qCoeffLin (L₀ * q) (q ^ 1)
        have hΨ : ∀ F, Ψ F = (q : ℂ) * Φ₁ F - lam * ModularFormClass.qCoeff F (q ^ 1) := by
          intro F
          simp only [Ψ, LinearMap.sub_apply, LinearMap.smul_apply, qCoeffLin_apply, smul_eq_mul]
        have hTw : Tw q (L₀ * q) g' ≤ LinearMap.ker Ψ := by
          refine Submodule.span_le.mpr ?_
          rintro F ⟨i, hi, hi1, rfl⟩
          have hile : i ≤ 1 := by have := hexp i hi; omega
          have hi1' : i = 1 := le_antisymm hile hi1
          subst hi1'

          have hΦ₁top : Φ₁ (FreyPackage.ModMCarrier.rescaleLin hi 2 g') = lam := by
            have hcc : R' * c' = L₀ := by rw [hL₀, ← hR', hc']; ring
            rw [hΦ₁, trd_tower_two_one hq hqL₀ hR' hqR₁' hcc hc'q hi h1'₀ hg',
              show ModularFormClass.qCoeff (⇑(ModularFormClass.qCoeff (⇑g') q
                  • FreyPackage.ModMCarrier.rescaleLin h1'₀ 2 g')) 1
                = ModularFormClass.qCoeff (⇑g') q
                  * ModularFormClass.qCoeff (FreyPackage.ModMCarrier.rescaleLin h1'₀ 2 g') 1 by
                  rw [← qCoeffLin_apply, _root_.map_smul, qCoeffLin_apply, smul_eq_mul],
              qCoeff_rescaleLin_one, ha1', mul_one, hlam]
          rw [SetLike.mem_coe, LinearMap.mem_ker, hΨ, hΦ₁top, qCoeff_tower hq hi g' 1, if_pos le_rfl]
          simp only [Nat.sub_self, pow_zero, pow_one, ha1']
          ring
        have hJker : J q (L₀ * q) ≤ LinearMap.ker Ψ := by
          intro F hF
          rw [LinearMap.mem_ker, hΨ, hΦ₁J F hF, hJ 1 F hF]; ring
        have hΨd := (sup_le hTw hJker) hmem
        rw [LinearMap.mem_ker, hΨ, hΦ₁d, pow_one, hd, ← hε, ← hlam, hε0] at hΨd

        have h1q : (q : ℂ) ^ 2 = 1 := by
          have hl : lam * lam = 1 := by rw [← sq]; exact hlam2
          linear_combination -hΨd + hl
        have : (q : ℕ) ^ 2 = 1 := by exact_mod_cast h1q
        have : q = 1 := by simpa using this
        exact hq.one_lt.ne' this
    ·
      obtain ⟨m₂, rfl⟩ : ∃ m₂, m₁ = m₂ + 1 := ⟨m₁ - 1, by omega⟩

      obtain ⟨L₀₀, hL₀₀⟩ : ∃ L₀₀ : ℕ, L₀₀ = q ^ (m₂ + 1) * L₁ := ⟨_, rfl⟩
      haveI : NeZero L₀₀ := ⟨by rw [hL₀₀]; exact Nat.mul_ne_zero (pow_ne_zero _ hq0) hL₁0⟩
      have hL₀₀q : L₀₀ * q = L₀ := by rw [hL₀₀, hL₀]; ring
      have hTw : Tw q (L₀ * q) g' ≤ LinearMap.ker Φ₁ := by
        refine Submodule.span_le.mpr ?_
        rintro F ⟨i, hi, hi1, rfl⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker]
        have hie := hexp i hi
        rcases Nat.lt_or_ge (i + e) (m₂ + 1 + 2) with hlt | hge
        · exact hΦ₁low i hi hi1 (hlow_of i (by omega))
        ·
          have hieq : i + e = m₂ + 3 := by omega
          have hcc : q ^ (i + e - 2) * R₁' * c' = L₀₀ := by
            rw [hL₀₀, hc', show i + e - 2 = m₂ + 1 by omega]; ring
          rw [hΦ₁]
          exact qCoeff_one_trd_tower_top hq hqL₀ hL₀₀q hR' hi1 (by omega) hcc hc'q hi hg'
      have hJker : J q (L₀ * q) ≤ LinearMap.ker Φ₁ := fun F hF => LinearMap.mem_ker.mpr (hΦ₁J F hF)
      have hΦd := (sup_le hTw hJker) hmem
      rw [LinearMap.mem_ker, hΦ₁d, neg_eq_zero] at hΦd
      exact hq0 (by exact_mod_cast hΦd)

end NewformTowerTrace

theorem solution
    {L L₁ q m e R R₁ R' R₁' : ℕ} [NeZero L] (hq : q.Prime)
    (hL : q ^ m * L₁ = L) (hqL₁ : ¬ q ∣ L₁)
    (hR : q ^ m * R₁ = R) (hqR₁ : ¬ q ∣ R₁)
    (hR' : q ^ e * R₁' = R') (hqR₁' : ¬ q ∣ R₁') (he : e < m)
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2} {g' : CuspForm (CongruenceSubgroup.Gamma0 R') 2}
    (hg : CuspForm.IsNewform g) (hg' : CuspForm.IsNewform g')
    (h1 : 1 * R ∣ L) (h1' : 1 * R' ∣ L) :
    FreyPackage.ModMCarrier.rescaleLin h1 2 g - FreyPackage.ModMCarrier.rescaleLin h1' 2 g' ∉
      Submodule.span ℂ {F : CuspForm (CongruenceSubgroup.Gamma0 L) 2 |
          ∃ (i : ℕ) (h : q ^ i * R' ∣ L), 1 ≤ i ∧ F = FreyPackage.ModMCarrier.rescaleLin h 2 g'}
        ⊔ Submodule.span ℂ {F : CuspForm (CongruenceSubgroup.Gamma0 L) 2 |
          ∃ (p N' : ℕ) (h : p * N' ∣ L) (x : CuspForm (CongruenceSubgroup.Gamma0 N') 2),
            p.Prime ∧ p ≠ q ∧ p * N' = L ∧ F = FreyPackage.ModMCarrier.rescaleLin h 2 x} :=
  NewformTowerTrace.notmem hq hL hqL₁ hR hqR₁ hR' hqR₁' he hg hg' h1 h1'

end

end S_CuspForm_IsNewform_rescaleLin_sub_rescaleLin_notMem_span_sup_span
end P2MW
export P2MW.S_CuspForm_IsNewform_rescaleLin_sub_rescaleLin_notMem_span_sup_span (solution)
