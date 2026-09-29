-- Prove2me | solution 1 for CuspForm.IsNewform.sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/0085f7df-26ad-507f-8181-cfa88cb3173f

import Definitions.Def_CuspForm_Newforms
import Definitions.Def_CuspForm_Petersson
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_CuspForm_petersson_add_left
import Theorems.Thm_CuspForm_petersson_smul_left
import Theorems.Thm_CuspForm_petersson_conj_symm
import Theorems.Thm_CuspForm_petersson_self_eq_zero_iff
import Theorems.Thm_CuspForm_petersson_heckeTLin
import Theorems.Thm_CuspForm_heckeTLin_rescaleLin
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul
import Theorems.Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNewform_sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2"
p2m_attr_erase "simp" "FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm OnePoint Function
open scoped MatrixGroups ModularForm Manifold ComplexConjugate

namespace AlliAux1Trvan

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

theorem lowSL_mem_Gamma0 (L : ℕ) (j : ℕ) : lowSL ((L : ℤ) * j) ∈ CongruenceSubgroup.Gamma0 L := by
  rw [CongruenceSubgroup.Gamma0_mem, lowSL_coe]
  show ((((L : ℤ) * j : ℤ)) : ZMod L) = 0
  push_cast
  rw [ZMod.natCast_self, zero_mul]

theorem mem_Gamma0_iff_dvd (M : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma0 M ↔ (M : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [CongruenceSubgroup.Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem mul_apply_10 (A B : SL(2, ℤ)) :
    ((A * B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * (B : Matrix (Fin 2) (Fin 2) ℤ) 0 0
        + (A : Matrix (Fin 2) (Fin 2) ℤ) 1 1 * (B : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem Gamma0_mul_le (N p : ℕ) :
    CongruenceSubgroup.Gamma0 (N * p) ≤ CongruenceSubgroup.Gamma0 N := by
  intro γ hγ
  rw [mem_Gamma0_iff_dvd] at hγ ⊢
  push_cast at hγ
  exact (dvd_mul_right (N : ℤ) p).trans hγ

scoped instance fintypeQuot (M : ℕ) [NeZero M] : Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M) :=
  haveI : Finite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 M) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

theorem slash_mem {N : ℕ} {k : ℤ} (g : CuspForm (CongruenceSubgroup.Gamma0 N) k) {γ : SL(2, ℤ)}
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ⇑g ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g :=
  SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)

theorem petersson_smul_SL (k : ℤ) (F G : ℍ → ℂ) (γ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.petersson k F G (γ • τ)
      = UpperHalfPlane.petersson k (F ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ))
          (G ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ :=
  (UpperHalfPlane.petersson_slash_SL k F G γ τ).symm

section unfold

variable {Γ Λ : Subgroup SL(2, ℤ)} (hΛΓ : Λ ≤ Γ)
  {ι : Type*} (r : ι → SL(2, ℤ)) (hr : ∀ i, r i ∈ Γ)
  (hex : ∀ γ ∈ Γ, ∃ i, r i * γ ∈ Λ) (huniq : ∀ i i', r i * (r i')⁻¹ ∈ Λ → i = i')

def eMap (r : ι → SL(2, ℤ)) (x : (SL(2, ℤ) ⧸ Γ) × ι) : SL(2, ℤ) ⧸ Λ :=
  QuotientGroup.mk (x.1.out * (r x.2)⁻¹)

include hΛΓ hr hex huniq in
theorem eMap_bijective : Function.Bijective (eMap (Γ := Γ) (Λ := Λ) r) := by
  constructor
  · rintro ⟨q, i⟩ ⟨q', i'⟩ h
    have hmem : r i * q.out⁻¹ * q'.out * (r i')⁻¹ ∈ Λ := by
      have := QuotientGroup.eq.mp h
      simpa [mul_assoc, mul_inv_rev] using this
    have hqq : q = q' := by
      have hΓ : q.out⁻¹ * q'.out ∈ Γ := by
        have h1 : (r i)⁻¹ * (r i * q.out⁻¹ * q'.out * (r i')⁻¹) * r i' ∈ Γ :=
          mul_mem (mul_mem (inv_mem (hr i)) (hΛΓ hmem)) (hr i')
        simpa [mul_assoc] using h1
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      exact QuotientGroup.eq.mpr hΓ
    subst hqq
    have : r i * (r i')⁻¹ ∈ Λ := by simpa using hmem
    rw [huniq i i' this]
  · intro y
    set σ := y.out
    set q : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk σ
    have hγ : q.out⁻¹ * σ ∈ Γ := by
      rw [← QuotientGroup.eq]
      exact QuotientGroup.out_eq' q
    obtain ⟨i, hi⟩ := hex _ hγ
    refine ⟨(q, i), ?_⟩
    rw [← QuotientGroup.out_eq' y]
    show QuotientGroup.mk (q.out * (r i)⁻¹) = QuotientGroup.mk σ
    rw [QuotientGroup.eq]
    simpa [mul_assoc, mul_inv_rev] using hi

variable [Fintype (SL(2, ℤ) ⧸ Γ)] [Fintype (SL(2, ℤ) ⧸ Λ)] [Fintype ι]

include hΛΓ hr hex huniq in

theorem unfold_sum {X : Type*} [AddCommMonoid X] (Φ : ℍ → X)
    (hΦ : ∀ h ∈ Λ, ∀ x : ℍ, Φ (h • x) = Φ x) (τ : ℍ) :
    ∑ q' : SL(2, ℤ) ⧸ Λ, Φ ((q'.out⁻¹ : SL(2, ℤ)) • τ)
      = ∑ q : SL(2, ℤ) ⧸ Γ, ∑ i, Φ ((r i * q.out⁻¹ : SL(2, ℤ)) • τ) := by
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective (eMap (Γ := Γ) (Λ := Λ) r)
    (eMap_bijective hΛΓ r hr hex huniq) _ _ fun x => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Λ (x.1.out * (r x.2)⁻¹)
  show Φ ((r x.2 * x.1.out⁻¹ : SL(2, ℤ)) • τ) = Φ (((eMap r x).out⁻¹ : SL(2, ℤ)) • τ)
  rw [eMap, hh, mul_inv_rev, mul_inv_rev, inv_inv, mul_smul ((h : SL(2, ℤ))⁻¹) (r x.2 * x.1.out⁻¹) τ,
    hΦ _ (inv_mem h.2)]

end unfold

section petlin

variable {N : ℕ} {k : ℤ} [NeZero N]

theorem pet_add_right (f g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f (g₁ + g₂) = CuspForm.petersson f g₁ + CuspForm.petersson f g₂ := by
  rw [← CuspForm.petersson_conj_symm f (g₁ + g₂), CuspForm.petersson_add_left, map_add,
    CuspForm.petersson_conj_symm, CuspForm.petersson_conj_symm]

theorem pet_smul_right (c : ℂ) (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f (c • g) = c * CuspForm.petersson f g := by
  rw [← CuspForm.petersson_conj_symm f (c • g), CuspForm.petersson_smul_left, map_mul,
    starRingEnd_self_apply, CuspForm.petersson_conj_symm]

theorem pet_sub_left (f₁ f₂ g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (f₁ - f₂) g = CuspForm.petersson f₁ g - CuspForm.petersson f₂ g := by
  rw [sub_eq_add_neg, CuspForm.petersson_add_left, ← neg_one_smul ℂ f₂, CuspForm.petersson_smul_left,
    map_neg, map_one]
  ring

end petlin

section adj

theorem one_mul_dvd' {R₀ q R : ℕ} (hqR : R₀ * q = R) : 1 * R₀ ∣ R := ⟨q, by rw [one_mul, hqR]⟩

theorem heckeDiagMatrix_one : heckeDiagMatrix 1 = 1 := by
  apply Units.ext; rw [val_heckeDiagMatrix one_ne_zero, Units.val_one]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem coe_rescaleLin_one {R₀ R : ℕ} [NeZero R] (h1 : 1 * R₀ ∣ R)
    (v : CuspForm (CongruenceSubgroup.Gamma0 R₀) 2) :
    (⇑(FreyPackage.ModMCarrier.rescaleLin h1 2 v) : ℍ → ℂ) = ⇑v := by
  rw [FreyPackage.ModMCarrier.coe_rescaleLin_apply, heckeDiagMatrix_one, SlashAction.slash_one]

theorem petersson_sum_left {ι : Type*} (s : Finset ι) (k : ℤ) (f : ι → ℍ → ℂ) (g : ℍ → ℂ) (τ : ℍ) :
    UpperHalfPlane.petersson k (∑ i ∈ s, f i) g τ
      = ∑ i ∈ s, UpperHalfPlane.petersson k (f i) g τ := by
  simp only [UpperHalfPlane.petersson, Finset.sum_apply, map_sum, Finset.sum_mul]

variable {R R₀ q : ℕ} (hqR : R₀ * q = R) (hqR₀ : q ∣ R₀)

def r (R₀ q : ℕ) (j : Fin q) : SL(2, ℤ) := lowSL ((R₀ : ℤ) * (j : ℕ))

theorem r_mem (j : Fin q) : r R₀ q j ∈ CongruenceSubgroup.Gamma0 R₀ := lowSL_mem_Gamma0 R₀ j

include hqR in
theorem Gamma0_le : CongruenceSubgroup.Gamma0 R ≤ CongruenceSubgroup.Gamma0 R₀ := by
  rw [← hqR]; exact Gamma0_mul_le R₀ q

theorem lowSL_mul_apply_10 (x : ℤ) (γ : SL(2, ℤ)) :
    ((lowSL x * γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = x * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
  rw [mul_apply_10, lowSL_coe]
  simp

theorem lowSL_mul_lowSL (x y : ℤ) : lowSL x * lowSL y = lowSL (x + y) := by
  apply Subtype.ext
  show (lowSL x : Matrix (Fin 2) (Fin 2) ℤ) * (lowSL y : Matrix (Fin 2) (Fin 2) ℤ) = lowSL (x + y)
  rw [lowSL_coe, lowSL_coe, lowSL_coe]
  ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowSL_zero : lowSL 0 = 1 := by
  apply Subtype.ext
  rw [lowSL_coe]
  ext i k; fin_cases i <;> fin_cases k <;> simp

theorem lowSL_inv (x : ℤ) : (lowSL x)⁻¹ = lowSL (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [lowSL_mul_lowSL, add_neg_cancel, lowSL_zero])

include hqR hqR₀ in

theorem exists_r_mul_mem [NeZero q] {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 R₀) :
    ∃ j : Fin q, r R₀ q j * γ ∈ CongruenceSubgroup.Gamma0 R := by
  rw [mem_Gamma0_iff_dvd] at hγ
  obtain ⟨c', hc'⟩ := hγ
  have hqc : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 :=
    ((Int.natCast_dvd_natCast.mpr hqR₀).mul_right c').trans (by rw [hc'])
  have had' : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod q)
      * (((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod q) = 1 := by
    rw [mul_comm]; exact ad_eq_one hqc
  let j : Fin q :=
    ⟨(((-(c' * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℤ)) : ZMod q).val, ZMod.val_lt _⟩
  refine ⟨j, ?_⟩
  rw [mem_Gamma0_iff_dvd, r, lowSL_mul_apply_10, hc', ← hqR]
  push_cast
  have hdiv : (q : ℤ) ∣ (j : ℕ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + c' := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hj : (((j : ℕ) : ℤ) : ZMod q)
        = (((-(c' * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℤ)) : ZMod q) := by
      show ((((((-(c' * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1) : ℤ)) : ZMod q).val : ℕ) : ℤ) : ZMod q) = _
      rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    push_cast at hj ⊢
    rw [hj]
    linear_combination (-((c' : ℤ) : ZMod q)) * had'
  obtain ⟨e, he⟩ := hdiv
  exact ⟨e, by linear_combination (R₀ : ℤ) * he⟩

include hqR in

theorem r_mul_r_inv_mem [NeZero R₀] [NeZero q] (i i' : Fin q)
    (h : r R₀ q i * (r R₀ q i')⁻¹ ∈ CongruenceSubgroup.Gamma0 R) : i = i' := by
  rw [r, r, lowSL_inv, lowSL_mul_lowSL, mem_Gamma0_iff_dvd, lowSL_coe, ← hqR] at h
  have h' : ((R₀ : ℤ) * q) ∣ (R₀ : ℤ) * ((i : ℕ) - (i' : ℕ)) := by
    have := h; simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one] at this
    push_cast at this
    convert this using 1; ring
  have hR₀ : (R₀ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne R₀
  have hq : (q : ℤ) ∣ ((i : ℕ) : ℤ) - ((i' : ℕ) : ℤ) := (mul_dvd_mul_iff_left hR₀).mp h'
  apply Fin.ext
  have h1 : (((i : ℕ) : ℤ) : ZMod q) = (((i' : ℕ) : ℤ) : ZMod q) := by
    rw [← sub_eq_zero, ← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hq
  rw [Int.cast_natCast, Int.cast_natCast] at h1
  have := congrArg ZMod.val h1
  rwa [ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt i'.isLt] at this

variable [NeZero R] [NeZero R₀] [NeZero q]

include hqR₀ in

theorem petersson_trd (F : CuspForm (CongruenceSubgroup.Gamma0 R) 2)
    (v : CuspForm (CongruenceSubgroup.Gamma0 R₀) 2) :
    CuspForm.petersson (trd hqR hqR₀ F) v
      = CuspForm.petersson F (FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd' hqR) 2 v) := by
  rw [CuspForm.petersson_def, CuspForm.petersson_def]
  congr 1
  funext τ
  unfold CuspForm.peterssonIntegrand
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]

  have hΛ : ∀ q' : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 R,
      UpperHalfPlane.petersson 2 (⇑F ∣[(2 : ℤ)] (q'.out⁻¹ : SL(2, ℤ)))
          (⇑(FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd' hqR) 2 v) ∣[(2 : ℤ)] (q'.out⁻¹ : SL(2, ℤ))) τ
        = UpperHalfPlane.petersson 2 ⇑F ⇑v ((q'.out⁻¹ : SL(2, ℤ)) • τ) := fun q' => by
    rw [UpperHalfPlane.petersson_slash_SL, coe_rescaleLin_one]
  have hΓ : ∀ p : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 R₀,
      UpperHalfPlane.petersson 2 (⇑(trd hqR hqR₀ F) ∣[(2 : ℤ)] (p.out⁻¹ : SL(2, ℤ)))
          (⇑v ∣[(2 : ℤ)] (p.out⁻¹ : SL(2, ℤ))) τ
        = UpperHalfPlane.petersson 2 ⇑(trd hqR hqR₀ F) ⇑v ((p.out⁻¹ : SL(2, ℤ)) • τ) := fun p =>
    UpperHalfPlane.petersson_slash_SL 2 _ _ _ τ
  simp_rw [hΛ, hΓ]
  rw [unfold_sum (Gamma0_le hqR) (r R₀ q) r_mem (fun γ hγ => exists_r_mul_mem hqR hqR₀ hγ)
    (r_mul_r_inv_mem hqR) (UpperHalfPlane.petersson 2 ⇑F ⇑v) (fun h hh x => by
      rw [petersson_smul_SL, slash_mem F hh, slash_mem v (Gamma0_le hqR hh)]) τ]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hi : ∀ i : Fin q,
      UpperHalfPlane.petersson 2 ⇑F ⇑v ((r R₀ q i * p.out⁻¹ : SL(2, ℤ)) • τ)
        = UpperHalfPlane.petersson 2
            (⇑F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (r R₀ q i) : GL (Fin 2) ℝ)) ⇑v
            ((p.out⁻¹ : SL(2, ℤ)) • τ) := fun i => by
    rw [mul_smul, petersson_smul_SL 2 ⇑F ⇑v (r R₀ q i), slash_mem v (r_mem i)]
  have hsum : (∑ i : Fin q, ⇑F ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (r R₀ q i) : GL (Fin 2) ℝ))
      = ∑ j ∈ Finset.range q, ⇑F ∣[(2 : ℤ)] β R₀ j :=
    Fin.sum_univ_eq_sum_range (fun j => ⇑F ∣[(2 : ℤ)] β R₀ j) q
  rw [Finset.sum_congr rfl fun i _ => hi i, ← petersson_sum_left, coe_trd, hsum]

end adj

section hecke

variable {R R₀ q : ℕ} [NeZero R] [NeZero R₀] [NeZero q] (hqR : R₀ * q = R) (hqR₀ : q ∣ R₀)

include hqR₀ in
theorem trd_heckeTLin (F : CuspForm (CongruenceSubgroup.Gamma0 R) 2) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓR : ¬ ℓ ∣ R) (hℓR₀ : ¬ ℓ ∣ R₀) :
    trd hqR hqR₀ (CuspForm.heckeTLin 2 hℓ hℓR F) = CuspForm.heckeTLin 2 hℓ hℓR₀ (trd hqR hqR₀ F) := by
  set x := trd hqR hqR₀ (CuspForm.heckeTLin 2 hℓ hℓR F) - CuspForm.heckeTLin 2 hℓ hℓR₀ (trd hqR hqR₀ F)
    with hx
  have hxx : CuspForm.petersson x x = 0 := by
    have h1 : CuspForm.petersson (trd hqR hqR₀ (CuspForm.heckeTLin 2 hℓ hℓR F)) x
        = CuspForm.petersson F
            (FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd' hqR) 2 (CuspForm.heckeTLin 2 hℓ hℓR₀ x)) := by
      rw [petersson_trd hqR hqR₀, CuspForm.petersson_heckeTLin,
        CuspForm.heckeTLin_rescaleLin (one_mul_dvd' hqR) hℓ hℓR hℓR₀]
    have h2 : CuspForm.petersson (CuspForm.heckeTLin 2 hℓ hℓR₀ (trd hqR hqR₀ F)) x
        = CuspForm.petersson F
            (FreyPackage.ModMCarrier.rescaleLin (one_mul_dvd' hqR) 2 (CuspForm.heckeTLin 2 hℓ hℓR₀ x)) := by
      rw [CuspForm.petersson_heckeTLin, petersson_trd hqR hqR₀]
    rw [show CuspForm.petersson x x
        = CuspForm.petersson (trd hqR hqR₀ (CuspForm.heckeTLin 2 hℓ hℓR F)) x
          - CuspForm.petersson (CuspForm.heckeTLin 2 hℓ hℓR₀ (trd hqR hqR₀ F)) x from pet_sub_left _ _ _,
      h1, h2, sub_self]
  exact sub_eq_zero.mp ((CuspForm.petersson_self_eq_zero_iff x).mp hxx)

end hecke

section main

variable {R R₀ q : ℕ} [NeZero R] [NeZero R₀] [NeZero q] (hqR : R₀ * q = R) (hqR₀ : q ∣ R₀)

include hqR₀ in
theorem trd_eq_zero (hq : q.Prime) {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2}
    (hg : CuspForm.IsNewform g) : trd hqR hqR₀ g = 0 := by
  by_contra hne
  have hR₀R : R₀ ∣ R := ⟨q, hqR.symm⟩

  have hgood : ∀ {ℓ : ℕ}, ℓ.Prime → ¬ ℓ ∣ R₀ → ¬ ℓ ∣ R := by
    intro ℓ hℓ hℓR₀ hℓR
    rw [← hqR] at hℓR
    rcases (Nat.Prime.dvd_mul hℓ).mp hℓR with h | h
    · exact hℓR₀ h
    · exact hℓR₀ (((Nat.prime_dvd_prime_iff_eq hℓ hq).mp h) ▸ hqR₀)
  have heig := ((CuspForm.isNormalizedEigenform_iff_heckeTLin g).mp hg.1).2
  have hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓR₀ : ¬ ℓ ∣ R₀), ℓ ∉ (∅ : Set ℕ) →
      CuspForm.heckeTLin 2 hℓ hℓR₀ (trd hqR hqR₀ g) = ModularFormClass.qCoeff g ℓ • trd hqR hqR₀ g := by
    intro ℓ hℓ hℓR₀ _
    rw [← trd_heckeTLin hqR hqR₀ g hℓ (hgood hℓ hℓR₀) hℓR₀, (heig ℓ hℓ).1 (hgood hℓ hℓR₀)]
    exact trd_smul hqR hqR₀ _ g
  obtain ⟨h, hh, hspec⟩ :=
    CuspForm.exists_isNormalizedEigenform_of_forall_heckeTLin_eq_smul hne
      (fun ℓ => ModularFormClass.qCoeff g ℓ) ∅ hT
  have hocc : CuspForm.GoodEigensystemOccursAt g R₀ :=
    ⟨h, hh, fun ℓ hℓ hℓR => hspec ℓ hℓ (fun h' => hℓR (h'.trans hR₀R)) (by simp)⟩
  have hne' : R₀ ≠ R := by
    intro h0
    have h1 : R₀ * q = R₀ * 1 := by rw [hqR, mul_one, h0]
    exact hq.one_lt.ne' (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (NeZero.ne R₀)) h1)
  exact hg.2 R₀ hR₀R hne' hocc

end main

theorem lowSL_mul_S (c : ℤ) : lowSL c * ModularGroup.S = ModularGroup.S * ModularGroup.T ^ (-c) := by
  apply Subtype.ext
  show (lowSL c : Matrix (Fin 2) (Fin 2) ℤ) * (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ)
    = (ModularGroup.S : Matrix (Fin 2) (Fin 2) ℤ) * ((ModularGroup.T ^ (-c) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [lowSL_coe, ModularGroup.coe_S, ModularGroup.coe_T_zpow]
  ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowSL_eq (c : ℤ) : lowSL c = ModularGroup.S * ModularGroup.T ^ (-c) * ModularGroup.S⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, lowSL_mul_S]

end AlliAux1Trvan
p2m_reactivate "P2MW.S_CuspForm_IsNewform_sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero.AlliAux1Trvan"

theorem solution
    {R R₀ q : ℕ} [NeZero R]
    {g : CuspForm (CongruenceSubgroup.Gamma0 R) 2} (hg : CuspForm.IsNewform g)
    (hq : q.Prime) (hqR : q * R₀ = R) (hqR₀ : q ∣ R₀) :
    ∑ j ∈ Finset.range q,
      (⇑g) ∣[(2 : ℤ)] (ModularGroup.S * ModularGroup.T ^ (-((R₀ * j : ℕ) : ℤ)) * ModularGroup.S⁻¹)
        = 0 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : NeZero R₀ := ⟨fun h => NeZero.ne R (by rw [← hqR, h, mul_zero])⟩
  have hqR' : R₀ * q = R := by rw [mul_comm]; exact hqR
  have h := congrArg (fun F : CuspForm (CongruenceSubgroup.Gamma0 R₀) 2 => (⇑F : ℍ → ℂ))
    (AlliAux1Trvan.trd_eq_zero hqR' hqR₀ hq hg)
  simp only [AlliAux1Trvan.coe_trd, CuspForm.coe_zero] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (-((R₀ * j : ℕ) : ℤ)) = -((R₀ : ℤ) * j) := by push_cast; ring
  rw [hc, ← AlliAux1Trvan.lowSL_eq]
  rfl

end
p2m_reactivate "P2MW.S_CuspForm_IsNewform_sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero.AlliAux1Trvan"

end S_CuspForm_IsNewform_sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero
end P2MW
export P2MW.S_CuspForm_IsNewform_sum_slash_S_mul_T_zpow_mul_S_inv_eq_zero (solution)
