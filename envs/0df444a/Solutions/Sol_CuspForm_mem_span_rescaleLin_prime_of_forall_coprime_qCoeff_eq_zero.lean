-- Prove2me | solution 1 for CuspForm.mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7bda2380-f382-513b-9639-9089effec2f5

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_CuspForm_LevelLoweringTrace
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Theorems.Thm_CuspForm_exists_coe_eq_heckeU_of_mul_eq_of_dvd
import Theorems.Thm_CuspForm_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero
import Theorems.Thm_ModularForm_AtkinLehnerDatum_nonempty_of_prime_of_dvd_of_not_sq_dvd
import Theorems.Thm_ModularForm_alSlash_alSlash
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Theorems.Thm_ModularFormClass_eq_of_forall_qCoeff_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm OnePoint Function
open scoped MatrixGroups ModularForm Manifold

namespace AlliAux1X3

theorem sum_slash {ι : Type*} (s : Finset ι) (f : ι → ℍ → ℂ) (k : ℤ) (g : GL (Fin 2) ℝ) :
    (∑ i ∈ s, f i) ∣[k] g = ∑ i ∈ s, (f i ∣[k] g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

section perm

variable {q : ℕ} [NeZero q]

private def _root_.AlliAux1X3.σ (b d : ℤ) (j : ℕ) : ℕ := (((b * d + (j : ℤ) * d * d : ℤ)) : ZMod q).val

p2m_export "AlliAux1X3" "σ"

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

def Sc (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℝ :=
  upperTriangularGL p 0 p (by exact_mod_cast Nat.mul_ne_zero hp hp)

theorem slash_Sc {p : ℕ} (hp : p ≠ 0) (f : ℍ → ℂ) : f ∣[(2 : ℤ)] Sc p hp = f := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hdet : ((Sc p hp).det : ℝ) = ((p * p : ℕ) : ℝ) := by
    push_cast
    simp [Sc, Matrix.det_fin_two_of]
  have hdetpos : 0 < ((Sc p hp).det : ℝ) := by rw [hdet]; positivity
  have hσ : UpperHalfPlane.σ (Sc p hp) = .refl ℝ ℂ := by
    rw [UpperHalfPlane.σ, if_pos hdetpos]
  funext τ
  have hdenom : UpperHalfPlane.denom (Sc p hp) τ = p := by
    simp [UpperHalfPlane.denom, Sc]
  have hsmul : (Sc p hp • τ : ℍ) = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdetpos, hdenom]
    simp [UpperHalfPlane.num, Sc, hpC]
  rw [ModularForm.slash_apply, hσ, hdet, hdenom, hsmul]
  simp only [ContinuousAlgEquiv.refl_apply, Nat.abs_cast, Complex.ofReal_natCast]
  rw [show ((2 : ℤ) - 1) = 1 by norm_num, zpow_one, zpow_neg, mul_assoc]
  push_cast
  rw [show ((p : ℂ) * p) * ((p : ℂ) ^ (2 : ℤ))⁻¹ = 1 by rw [zpow_two]; field_simp, mul_one]

theorem sub_slash (k : ℤ) (g : GL (Fin 2) ℝ) (f f' : ℍ → ℂ) :
    (f - f') ∣[k] g = f ∣[k] g - f' ∣[k] g := by
  rw [sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ← sub_eq_add_neg]

section T3

variable {m p : ℕ} (W : AtkinLehnerDatum m p)

def δSL (j : ℕ) : SL(2, ℤ) :=
  ⟨!![W.a, W.a * j + W.b; (W.R : ℤ), (W.R : ℤ) * j + p], by
    rw [Matrix.det_fin_two_of]
    linear_combination W.bezout⟩

theorem δSL_coe (j : ℕ) :
    ((δSL W j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![W.a, W.a * j + W.b; (W.R : ℤ), (W.R : ℤ) * j + p] :=
  rfl

theorem δSL_mem (j : ℕ) : δSL W j ∈ CongruenceSubgroup.Gamma0 W.R := by
  rw [CongruenceSubgroup.Gamma0_mem, δSL_coe]
  show (((W.R : ℤ) : ℤ) : ZMod W.R) = 0
  rw [Int.cast_natCast, ZMod.natCast_self]

theorem mat_eq : W.mat = !![(p : ℤ) * W.a, W.b; (p : ℤ) * (W.R : ℤ), (p : ℤ)] := rfl

set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in

theorem alGL_mul_heckeMatrix [NeZero m] (hp : p ≠ 0) (j : ℕ) :
    W.alGL * heckeMatrix p j
      = Sc p hp * (Matrix.SpecialLinearGroup.mapGL ℝ (δSL W j) : GL (Fin 2) ℝ) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, W.alGL_coe, val_heckeMatrix hp, mapGL_coe_eq, δSL_coe, mat_eq]
  unfold Sc
  rw [val_upperTriangularGL]
  ext i k; fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] <;> push_cast <;> ring

set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in

theorem δSL_zero_mul_heckeDiagMatrix [NeZero m] (hp : p ≠ 0) :
    (Matrix.SpecialLinearGroup.mapGL ℝ (δSL W 0) : GL (Fin 2) ℝ) * heckeDiagMatrix p = W.alGL := by
  apply Units.ext
  rw [Units.val_mul, W.alGL_coe, val_heckeDiagMatrix hp, mapGL_coe_eq, δSL_coe, mat_eq]
  ext i k; fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply] <;> push_cast <;> ring

theorem not_dvd_R (hp : p.Prime) : ¬ p ∣ W.R := by
  rintro ⟨t, ht⟩
  have h := W.bezout
  rw [ht] at h
  push_cast at h
  have : (p : ℤ) ∣ 1 := ⟨W.a - t * W.b, by linear_combination -h⟩
  exact hp.not_dvd_one (Int.natCast_dvd_natCast.mp this)

theorem heckeU_alSlash_eq [NeZero m] (hp : p.Prime) (f : ℍ → ℂ) :
    heckeU 2 p (alSlash W 2 f)
      = ∑ j ∈ Finset.range p, f ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (δSL W j) : GL (Fin 2) ℝ) := by
  rw [heckeU_def, alSlash_def]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← SlashAction.slash_mul, alGL_mul_heckeMatrix W hp.ne_zero, SlashAction.slash_mul, slash_Sc]

def ρ (p R : ℕ) (j : ℕ) : ℕ := (((j : ZMod p) * (R : ZMod p))⁻¹).val

theorem ρ_spec (hp : p.Prime) {j : ℕ} (hj : j ∈ Finset.Ico 1 p) :
    ρ p W.R j ∈ Finset.Ico 1 p ∧
      ((j : ZMod p) * (W.R : ZMod p)) * (ρ p W.R j : ZMod p) = 1 ∧ ρ p W.R (ρ p W.R j) = j := by
  haveI := Fact.mk hp
  rw [Finset.mem_Ico] at hj
  have hj0 : (j : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have hR0 : (W.R : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact not_dvd_R W hp
  have hjR : (j : ZMod p) * (W.R : ZMod p) ≠ 0 := mul_ne_zero hj0 hR0
  have hcast : (ρ p W.R j : ZMod p) = ((j : ZMod p) * (W.R : ZMod p))⁻¹ := by
    unfold ρ; rw [ZMod.natCast_zmod_val]
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.mem_Ico]
    refine ⟨Nat.one_le_iff_ne_zero.mpr fun h0 => ?_, ZMod.val_lt _⟩
    have : (ρ p W.R j : ZMod p) = 0 := by rw [h0, Nat.cast_zero]
    rw [hcast] at this
    exact (inv_ne_zero hjR) this
  · rw [hcast, mul_inv_cancel₀ hjR]
  · show ((((ρ p W.R j : ℕ) : ZMod p) * (W.R : ZMod p))⁻¹).val = j
    rw [hcast, mul_inv_rev, inv_inv,
      show ((W.R : ZMod p))⁻¹ * ((j : ZMod p) * (W.R : ZMod p)) = (j : ZMod p) by
        rw [mul_comm, mul_assoc, mul_inv_cancel₀ hR0, mul_one],
      ZMod.val_cast_of_lt hj.2]

end T3

section T3b

variable {m p : ℕ} (W : AtkinLehnerDatum m p)

theorem lowSL_mul_lowSL_neg (c : ℤ) : lowSL c * lowSL (-c) = 1 := by
  apply Subtype.ext
  show (lowSL c : Matrix (Fin 2) (Fin 2) ℤ) * (lowSL (-c) : Matrix (Fin 2) (Fin 2) ℤ) = 1
  rw [lowSL_coe, lowSL_coe]
  ext i k; fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem lowSL_inv (c : ℤ) : (lowSL c)⁻¹ = lowSL (-c) :=
  inv_eq_of_mul_eq_one_right (lowSL_mul_lowSL_neg c)

theorem exists_ε (hp : p.Prime) {j : ℕ} (hj : j ∈ Finset.Ico 1 p) :
    ∃ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma0 m ∧
      lowSL ((W.R : ℤ) * j) = ε * δSL W (ρ p W.R j) := by
  obtain ⟨_, hkey, _⟩ := ρ_spec W hp hj
  set j' : ℕ := ρ p W.R j with hj'
  refine ⟨lowSL ((W.R : ℤ) * j) * (δSL W j')⁻¹, ?_, by rw [inv_mul_cancel_right]⟩
  rw [← Subgroup.inv_mem_iff, mul_inv_rev, inv_inv, lowSL_inv, CongruenceSubgroup.Gamma0_mem]

  have hentry : ((δSL W j' * lowSL (-((W.R : ℤ) * j)) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0
      = (W.R : ℤ) - ((W.R : ℤ) * j' + p) * ((W.R : ℤ) * j) := by
    show ((δSL W j' : Matrix (Fin 2) (Fin 2) ℤ) * (lowSL (-((W.R : ℤ) * j)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0
      = _
    rw [δSL_coe, lowSL_coe, Matrix.mul_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    ring
  rw [hentry, ZMod.intCast_zmod_eq_zero_iff_dvd]

  have hdiv : (p : ℤ) ∣ (j : ℤ) * (W.R : ℤ) * (j' : ℤ) - 1 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [sub_eq_zero]
    exact_mod_cast hkey
  obtain ⟨t, ht⟩ := hdiv
  refine ⟨-(t + j), ?_⟩
  rw [W.hM_int]
  linear_combination (-(W.R : ℤ)) * ht

theorem sum_slash_β_eq [NeZero m] (hp : p.Prime) (g : CuspForm (CongruenceSubgroup.Gamma0 m) 2) :
    ∑ j ∈ Finset.range p, ⇑g ∣[(2 : ℤ)] β W.R j
      = ⇑(CuspForm.traceLin W hp g)
        - ⇑g ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (δSL W 0) : GL (Fin 2) ℝ) := by
  rw [CuspForm.coe_traceLin_apply, heckeU_alSlash_eq W hp, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot hp.pos, Finset.sum_eq_sum_Ico_succ_bot hp.pos, zero_add,
    β_zero, SlashAction.slash_one]
  have hterm : ∀ j ∈ Finset.Ico 1 p, ⇑g ∣[(2 : ℤ)] β W.R j
      = ⇑g ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (δSL W (ρ p W.R j)) : GL (Fin 2) ℝ) := by
    intro j hj
    obtain ⟨ε, hε, hconj⟩ := exists_ε W hp hj
    unfold β
    rw [hconj, map_mul, SlashAction.slash_mul]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map.mpr ⟨ε, hε, rfl⟩)
  rw [Finset.sum_congr rfl hterm]
  have hre : ∑ j ∈ Finset.Ico 1 p,
        ⇑g ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (δSL W (ρ p W.R j)) : GL (Fin 2) ℝ)
      = ∑ j ∈ Finset.Ico 1 p,
        ⇑g ∣[(2 : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ (δSL W j) : GL (Fin 2) ℝ) := by
    refine Finset.sum_nbij' (ρ p W.R) (ρ p W.R) ?_ ?_ ?_ ?_ ?_
    · intro j hj; exact (ρ_spec W hp hj).1
    · intro j hj; exact (ρ_spec W hp hj).1
    · intro j hj; exact (ρ_spec W hp hj).2.2
    · intro j hj; exact (ρ_spec W hp hj).2.2
    · intro j _; rfl
  rw [hre]
  abel

theorem trd_rescaleLin_p [NeZero m] [NeZero p] (hp : p.Prime) (hpm : p ∣ m) (h1 : p * m ∣ m * p)
    [NeZero (m * p)]
    (g : CuspForm (CongruenceSubgroup.Gamma0 m) 2) :
    trd (M := m * p) rfl hpm (FreyPackage.ModMCarrier.rescaleLin h1 2 g)
      = FreyPackage.ModMCarrier.rescaleLin W.q_mul_R_dvd 2 (CuspForm.traceLin W hp g)
        - CuspForm.atkinLehnerLin W 2 g := by
  haveI : NeZero W.R := ⟨W.R_pos.ne'⟩
  refine DFunLike.coe_injective ?_
  show ⇑(trd (M := m * p) rfl hpm (FreyPackage.ModMCarrier.rescaleLin h1 2 g))
    = ⇑(FreyPackage.ModMCarrier.rescaleLin W.q_mul_R_dvd 2 (CuspForm.traceLin W hp g)
        - CuspForm.atkinLehnerLin W 2 g)
  rw [CuspForm.coe_sub, coe_trd, FreyPackage.ModMCarrier.coe_rescaleLin_apply,
    FreyPackage.ModMCarrier.coe_rescaleLin_apply, CuspForm.coe_atkinLehnerLin_apply, alSlash_def]
  have hterm : ∀ j ∈ Finset.range p,
      (⇑g ∣[(2 : ℤ)] heckeDiagMatrix p) ∣[(2 : ℤ)] β m j
        = (⇑g ∣[(2 : ℤ)] β W.R j) ∣[(2 : ℤ)] heckeDiagMatrix p := by
    intro j _
    rw [← SlashAction.slash_mul, diag_mul_β hp.ne_zero W.hM.symm j, SlashAction.slash_mul]
  rw [Finset.sum_congr rfl hterm, ← sum_slash, sum_slash_β_eq W hp g, sub_slash,
    ← SlashAction.slash_mul, δSL_zero_mul_heckeDiagMatrix W hp.ne_zero]

theorem atkinLehnerLin_rescaleLin_one [NeZero m] (hp : p.Prime) (h1 : 1 * W.R ∣ m)
    (f : CuspForm (CongruenceSubgroup.Gamma0 W.R) 2) :
    CuspForm.atkinLehnerLin W 2 (FreyPackage.ModMCarrier.rescaleLin h1 2 f)
      = FreyPackage.ModMCarrier.rescaleLin W.q_mul_R_dvd 2 f := by
  haveI : NeZero W.R := ⟨W.R_pos.ne'⟩
  refine DFunLike.coe_injective ?_
  show ⇑(CuspForm.atkinLehnerLin W 2 (FreyPackage.ModMCarrier.rescaleLin h1 2 f))
    = ⇑(FreyPackage.ModMCarrier.rescaleLin W.q_mul_R_dvd 2 f)
  rw [CuspForm.coe_atkinLehnerLin_apply, FreyPackage.ModMCarrier.coe_rescaleLin_apply,
    FreyPackage.ModMCarrier.coe_rescaleLin_apply, alSlash_def, heckeDiagMatrix_one,
    SlashAction.slash_one, ← δSL_zero_mul_heckeDiagMatrix W hp.ne_zero, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map.mpr ⟨δSL W 0, δSL_mem W 0, rfl⟩)

theorem atkinLehnerLin_atkinLehnerLin [NeZero m] (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2) :
    CuspForm.atkinLehnerLin W 2 (CuspForm.atkinLehnerLin W 2 F) = F := by
  refine DFunLike.coe_injective ?_
  show ⇑(CuspForm.atkinLehnerLin W 2 (CuspForm.atkinLehnerLin W 2 F)) = ⇑F
  rw [CuspForm.coe_atkinLehnerLin_apply, CuspForm.coe_atkinLehnerLin_apply,
    alSlash_alSlash W 2 (fun γ hγ => SlashInvariantFormClass.slash_action_eq F γ hγ)]
  norm_num

theorem rescaleLin_one_traceLin_atkinLehnerLin [NeZero m] (hp : p.Prime) (hpm : p ∣ m) (h1 : 1 * W.R ∣ m)
    (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2) :
    FreyPackage.ModMCarrier.rescaleLin h1 2 (CuspForm.traceLin W hp (CuspForm.atkinLehnerLin W 2 F))
      = CuspForm.atkinLehnerLin W 2 F + CuspForm.heckeULin 2 hpm F := by
  haveI : NeZero W.R := ⟨W.R_pos.ne'⟩
  refine DFunLike.coe_injective ?_
  show ⇑(FreyPackage.ModMCarrier.rescaleLin h1 2
      (CuspForm.traceLin W hp (CuspForm.atkinLehnerLin W 2 F)))
    = ⇑(CuspForm.atkinLehnerLin W 2 F + CuspForm.heckeULin 2 hpm F)
  rw [FreyPackage.ModMCarrier.coe_rescaleLin_apply, heckeDiagMatrix_one, SlashAction.slash_one,
    CuspForm.coe_traceLin_apply, CuspForm.coe_atkinLehnerLin_apply, CuspForm.coe_add,
    CuspForm.coe_atkinLehnerLin_apply, CuspForm.coe_heckeULin_apply,
    alSlash_alSlash W 2 (fun γ hγ => SlashInvariantFormClass.slash_action_eq F γ hγ)]
  norm_num

end T3b

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

section coeff

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

theorem qCoeff_heckeU' {M p : ℕ} [NeZero M] (hp : p ≠ 0) (F : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (n : ℕ) : ModularFormClass.qCoeff (heckeU 2 p ⇑F) n = ModularFormClass.qCoeff F (n * p) :=
  ModularFormClass.qCoeff_heckeU F (hΓ M) hp n

theorem qCoeff_proj {M R L p : ℕ} [NeZero M] [NeZero R] [NeZero L] (hp : p ≠ 0)
    (F : CuspForm (CongruenceSubgroup.Gamma0 L) 2)
    (A : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (B : CuspForm (CongruenceSubgroup.Gamma0 R) 2)
    (hpR : p * R ∣ M)
    (hA : ∀ n, ModularFormClass.qCoeff A n = ModularFormClass.qCoeff F n)
    (hB : ∀ k, ModularFormClass.qCoeff B k = ModularFormClass.qCoeff F (k * p)) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(A - (p : ℂ)⁻¹ • FreyPackage.ModMCarrier.rescaleLin hpR 2 B)) n
      = if p ∣ n then 0 else ModularFormClass.qCoeff F n := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  rw [qCoeff_sub_smul, hA, qCoeff_rescaleLin hpR hp]
  split_ifs with hpn
  · rw [hB, Nat.div_mul_cancel hpn, ← mul_assoc, inv_mul_cancel₀ hpC, one_mul, sub_self]
  · rw [mul_zero, sub_zero]

end coeff

section main

def oldSet (Q : Finset ℕ) (m : ℕ) [NeZero m] : Set (CuspForm (CongruenceSubgroup.Gamma0 m) 2) :=
  {F | ∃ (q R : ℕ) (hqR : q * R ∣ m) (fq : CuspForm (CongruenceSubgroup.Gamma0 R) 2),
    q ∈ Q ∧ q.Prime ∧ q * R = m ∧ F = FreyPackage.ModMCarrier.rescaleLin hqR 2 fq}

def O (Q : Finset ℕ) (m : ℕ) [NeZero m] : Submodule ℂ (CuspForm (CongruenceSubgroup.Gamma0 m) 2) :=
  Submodule.span ℂ (oldSet Q m)

theorem rescaleLin_mem_O {Q : Finset ℕ} {m q R : ℕ} [NeZero m] (hq : q ∈ Q) (hqp : q.Prime)
    (hqRm : q * R = m) (hqR : q * R ∣ m) (f : CuspForm (CongruenceSubgroup.Gamma0 R) 2) :
    FreyPackage.ModMCarrier.rescaleLin hqR 2 f ∈ O Q m :=
  Submodule.subset_span ⟨q, R, hqR, f, hq, hqp, hqRm, rfl⟩

theorem O_mono {Q Q' : Finset ℕ} {m : ℕ} [NeZero m] (hQ : Q' ⊆ Q) : O Q' m ≤ O Q m := by
  refine Submodule.span_mono ?_
  rintro F ⟨q, R, hqR, fq, hq, hqp, hqRm, rfl⟩
  exact ⟨q, R, hqR, fq, hQ hq, hqp, hqRm, rfl⟩

def Hyp (Q : Finset ℕ) {m : ℕ} (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2) : Prop :=
  ∀ n : ℕ, (∀ q ∈ Q, ¬ q ∣ n) → ModularFormClass.qCoeff F n = 0

theorem hyp_erase {Q : Finset ℕ} {m m' p : ℕ} {F : CuspForm (CongruenceSubgroup.Gamma0 m) 2}
    {G : CuspForm (CongruenceSubgroup.Gamma0 m') 2} (hF : Hyp Q F)
    (hG : ∀ n, ModularFormClass.qCoeff G n = if p ∣ n then 0 else ModularFormClass.qCoeff F n) :
    Hyp (Q.erase p) G := by
  intro n hn
  rw [hG]
  split_ifs with hpn
  · rfl
  · refine hF n fun q hq => ?_
    by_cases hqp : q = p
    · subst hqp; exact hpn
    · exact hn q (Finset.mem_erase.mpr ⟨hqp, hq⟩)

theorem sq_ne (p : ℕ) (hp : p.Prime) : (p : ℂ) - (p : ℂ)⁻¹ ≠ 0 := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  intro h
  have h2 : ((p * p : ℕ) : ℂ) = ((1 : ℕ) : ℂ) := by
    push_cast
    have := congrArg (fun z => z * (p : ℂ)) h
    simp only [sub_mul, inv_mul_cancel₀ hpC, zero_mul] at this
    linear_combination this
  have h3 : p * p = 1 := by exact_mod_cast h2
  exact hp.one_lt.ne' (Nat.eq_one_of_mul_eq_one_right h3)

abbrev Motive (Q : Finset ℕ) : Prop :=
  (∀ q ∈ Q, q.Prime) → ∀ (m : ℕ) [NeZero m] (F : CuspForm (CongruenceSubgroup.Gamma0 m) 2),
    Hyp Q F → F ∈ O Q m

theorem main (Q₀ : Finset ℕ) : Motive Q₀ := by
  refine Finset.strongInduction (p := Motive) (fun Q ih => ?_) Q₀
  intro hQ m _ F hF
  by_cases hex : ∃ p ∈ Q, p ∣ m
  · obtain ⟨p, hpQ, hpm⟩ := hex
    have hp : p.Prime := hQ p hpQ
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hQ' : ∀ q ∈ Q.erase p, q.Prime := fun q hq => hQ q (Finset.mem_of_mem_erase hq)
    have ih' := ih (Q.erase p) (Finset.erase_ssubset hpQ) hQ'
    have hsub : O (Q.erase p) m ≤ O Q m := O_mono (Finset.erase_subset p Q)
    by_cases hp2 : p * p ∣ m
    ·
      obtain ⟨t, ht⟩ := hp2
      have hR : p * (p * t) = m := by rw [ht, mul_assoc]
      haveI : NeZero (p * t) := ⟨by rintro h0; exact NeZero.ne m (by rw [← hR, h0, mul_zero])⟩
      obtain ⟨g, hg⟩ :=
        CuspForm.exists_coe_eq_heckeU_of_mul_eq_of_dvd (m := m) (q := p) (R := p * t) hR
          (dvd_mul_right p t) F
      have hpR : p * (p * t) ∣ m := Dvd.intro 1 ((mul_one _).trans hR)
      set G := F - (p : ℂ)⁻¹ • FreyPackage.ModMCarrier.rescaleLin hpR 2 g with hGdef
      have hGc : ∀ n, ModularFormClass.qCoeff G n
          = if p ∣ n then 0 else ModularFormClass.qCoeff F n := by
        intro n
        refine qCoeff_proj hp.ne_zero F F g hpR (fun _ => rfl) (fun k => ?_) n
        rw [show ModularFormClass.qCoeff (⇑g) k = ModularFormClass.qCoeff (heckeU 2 p ⇑F) k by
          rw [hg], qCoeff_heckeU' hp.ne_zero]
      have hGmem : G ∈ O Q m := hsub (ih' m G (hyp_erase hF hGc))
      have hι : FreyPackage.ModMCarrier.rescaleLin hpR 2 g ∈ O Q m :=
        rescaleLin_mem_O hpQ hp hR hpR g
      have : F = G + (p : ℂ)⁻¹ • FreyPackage.ModMCarrier.rescaleLin hpR 2 g := by
        rw [hGdef, sub_add_cancel]
      rw [this]
      exact (O Q m).add_mem hGmem ((O Q m).smul_mem _ hι)
    ·
      have hp2' : ¬ p ^ 2 ∣ m := by rwa [pow_two]
      obtain ⟨W⟩ := AtkinLehnerDatum.nonempty_of_prime_of_dvd_of_not_sq_dvd hp hpm hp2'
      haveI : NeZero W.R := ⟨W.R_pos.ne'⟩
      haveI : NeZero (m * p) := ⟨Nat.mul_ne_zero (NeZero.ne m) hp.ne_zero⟩
      have h1m : 1 * m ∣ m * p := ⟨p, by ring⟩
      have hpm' : p * m ∣ m * p := ⟨1, by ring⟩
      have h1R : 1 * W.R ∣ m := ⟨p, by rw [one_mul, mul_comm]; exact W.hM⟩
      set U := CuspForm.heckeULin 2 hpm F with hUdef
      set G := FreyPackage.ModMCarrier.rescaleLin h1m 2 F
        - (p : ℂ)⁻¹ • FreyPackage.ModMCarrier.rescaleLin hpm' 2 U with hGdef
      have hGc : ∀ n, ModularFormClass.qCoeff G n
          = if p ∣ n then 0 else ModularFormClass.qCoeff F n := by
        intro n
        refine qCoeff_proj hp.ne_zero F _ U hpm' (fun n => qCoeff_rescaleLin_one h1m F n)
          (fun k => ?_) n
        rw [hUdef, show ModularFormClass.qCoeff (⇑(CuspForm.heckeULin 2 hpm F)) k
            = ModularFormClass.qCoeff (heckeU 2 p ⇑F) k by rw [CuspForm.coe_heckeULin_apply],
          qCoeff_heckeU' hp.ne_zero]
      have hGmem : G ∈ O (Q.erase p) (m * p) := ih' (m * p) G (hyp_erase hF hGc)

      set TrD := trdLin (M := m * p) (L := m) (p := p) rfl hpm with hTrD
      have himg : ∀ x ∈ oldSet (Q.erase p) (m * p), TrD x ∈ O Q m := by
        rintro x ⟨q, R', hqR', h, hq, hqp, hqRm, rfl⟩
        have hqp' : q ≠ p := (Finset.mem_erase.mp hq).1
        have hqQ : q ∈ Q := Finset.mem_of_mem_erase hq

        have hqm : q ∣ m := by
          have : q ∣ m * p := ⟨R', hqRm.symm⟩
          rcases (Nat.Prime.dvd_mul hqp).mp this with h | h
          · exact h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hqp hp).mp h) hqp'
        obtain ⟨R, hR⟩ := hqm
        have hR' : R' = R * p := by
          have : q * R' = q * (R * p) := by rw [hqRm, hR, mul_assoc]
          exact Nat.eq_of_mul_eq_mul_left hqp.pos this
        subst hR'
        haveI : NeZero R := ⟨by rintro h0; exact NeZero.ne m (by rw [hR, h0, mul_zero])⟩
        haveI : NeZero (R * p) := ⟨Nat.mul_ne_zero (NeZero.ne R) hp.ne_zero⟩
        have hpR : p ∣ R := by
          have : p ∣ q * R := hR ▸ hpm
          rcases (Nat.Prime.dvd_mul hp).mp this with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hqp).mp h) (Ne.symm hqp')
          · exact h
        show trd (M := m * p) rfl hpm (FreyPackage.ModMCarrier.rescaleLin hqR' 2 h) ∈ O Q m
        rw [trd_rescaleLin_of_ne hpm hqp.ne_zero hR.symm hpR hqR' h]
        exact rescaleLin_mem_O hqQ hqp hR.symm _ _
      have hTrG : TrD G ∈ O Q m := by
        have hle : (O (Q.erase p) (m * p)).map TrD ≤ O Q m := by
          rw [O, Submodule.map_span_le]
          exact himg
        exact hle (Submodule.mem_map_of_mem hGmem)

      have hTrG' : TrD G = (p : ℂ) • F - (p : ℂ)⁻¹ •
          (FreyPackage.ModMCarrier.rescaleLin W.q_mul_R_dvd 2 (CuspForm.traceLin W hp U)
            - CuspForm.atkinLehnerLin W 2 U) := by
        rw [hGdef, map_sub, _root_.map_smul, hTrD]
        show trd (M := m * p) rfl hpm (FreyPackage.ModMCarrier.rescaleLin h1m 2 F)
            - (p : ℂ)⁻¹ • trd (M := m * p) rfl hpm (FreyPackage.ModMCarrier.rescaleLin hpm' 2 U) = _
        rw [trd_rescaleLin_one hpm h1m F, trd_rescaleLin_p W hp hpm hpm' U]

      set fstar := CuspForm.traceLin W hp (CuspForm.atkinLehnerLin W 2 F) with hfstar
      have hWU : CuspForm.atkinLehnerLin W 2 U
          = FreyPackage.ModMCarrier.rescaleLin W.q_mul_R_dvd 2 fstar - F := by
        have hU : U = FreyPackage.ModMCarrier.rescaleLin h1R 2 fstar - CuspForm.atkinLehnerLin W 2 F := by
          rw [hfstar, rescaleLin_one_traceLin_atkinLehnerLin W hp hpm h1R F, hUdef, add_sub_cancel_left]
        rw [hU, map_sub, atkinLehnerLin_rescaleLin_one W hp h1R, atkinLehnerLin_atkinLehnerLin]
      have hι1 : FreyPackage.ModMCarrier.rescaleLin W.q_mul_R_dvd 2 (CuspForm.traceLin W hp U) ∈ O Q m :=
        rescaleLin_mem_O hpQ hp W.hM.symm _ _
      have hι2 : FreyPackage.ModMCarrier.rescaleLin W.q_mul_R_dvd 2 fstar ∈ O Q m :=
        rescaleLin_mem_O hpQ hp W.hM.symm _ _

      have hkey : ((p : ℂ) - (p : ℂ)⁻¹) • F
          = TrD G + (p : ℂ)⁻¹ • FreyPackage.ModMCarrier.rescaleLin W.q_mul_R_dvd 2 (CuspForm.traceLin W hp U)
            - (p : ℂ)⁻¹ • FreyPackage.ModMCarrier.rescaleLin W.q_mul_R_dvd 2 fstar := by
        rw [hTrG', hWU]
        simp only [sub_smul, smul_sub]
        abel
      have hmem : ((p : ℂ) - (p : ℂ)⁻¹) • F ∈ O Q m := by
        rw [hkey]
        exact (O Q m).sub_mem ((O Q m).add_mem hTrG ((O Q m).smul_mem _ hι1)) ((O Q m).smul_mem _ hι2)
      exact ((O Q m).smul_mem_iff (sq_ne p hp)).mp hmem
  · push Not at hex
    rcases Q.eq_empty_or_nonempty with hQe | ⟨p, hpQ⟩
    ·
      subst hQe
      have h0 : F = 0 := ModularFormClass.eq_of_forall_qCoeff_eq (hΓ m) fun n => by
        rw [hF n (by simp)]
        exact (qCoeff_zero' m n).symm
      rw [h0]
      exact (O ∅ m).zero_mem
    ·
      have hp : p.Prime := hQ p hpQ
      have hpm : ¬ p ∣ m := hex p hpQ
      haveI : NeZero p := ⟨hp.ne_zero⟩
      haveI : NeZero (m * p) := ⟨Nat.mul_ne_zero (NeZero.ne m) hp.ne_zero⟩
      haveI : NeZero (m * p * p) := ⟨Nat.mul_ne_zero (NeZero.ne (m * p)) hp.ne_zero⟩
      have hQ' : ∀ q ∈ Q.erase p, q.Prime := fun q hq => hQ q (Finset.mem_of_mem_erase hq)
      have ih' := ih (Q.erase p) (Finset.erase_ssubset hpQ) hQ'
      have h1 : 1 * m ∣ m * p * p := ⟨p * p, by ring⟩
      have hLp : p * (m * p) = m * p * p := by ring
      obtain ⟨g, hg⟩ :=
        CuspForm.exists_coe_eq_heckeU_of_mul_eq_of_dvd (m := m * p * p) (q := p) (R := m * p) hLp
          (dvd_mul_left p m) (FreyPackage.ModMCarrier.rescaleLin h1 2 F)
      have hpR : p * (m * p) ∣ m * p * p := Dvd.intro 1 ((mul_one _).trans hLp)
      set K := FreyPackage.ModMCarrier.rescaleLin h1 2 F
        - (p : ℂ)⁻¹ • FreyPackage.ModMCarrier.rescaleLin hpR 2 g with hKdef
      have hKc : ∀ n, ModularFormClass.qCoeff K n
          = if p ∣ n then 0 else ModularFormClass.qCoeff F n := by
        intro n
        refine qCoeff_proj hp.ne_zero F _ g hpR (fun n => qCoeff_rescaleLin_one h1 F n) (fun k => ?_) n
        rw [show ModularFormClass.qCoeff (⇑g) k
            = ModularFormClass.qCoeff (heckeU 2 p ⇑(FreyPackage.ModMCarrier.rescaleLin h1 2 F)) k by
              rw [hg], qCoeff_heckeU' hp.ne_zero, qCoeff_rescaleLin_one h1 F]
      have hKmem : K ∈ O (Q.erase p) (m * p * p) := ih' (m * p * p) K (hyp_erase hF hKc)

      have hbot : O (Q.erase p) (m * p * p) = ⊥ := by
        rw [O, Submodule.span_eq_bot]
        rintro x ⟨q, R', hqR', h, hq, hqp, hqRm, rfl⟩
        exfalso
        have hqp' : q ≠ p := (Finset.mem_erase.mp hq).1
        have hqQ : q ∈ Q := Finset.mem_of_mem_erase hq
        have hqd : q ∣ m * p * p := ⟨R', hqRm.symm⟩
        rw [mul_assoc] at hqd
        rcases (Nat.Prime.dvd_mul hqp).mp hqd with h | h
        · exact hex q hqQ h
        · rcases (Nat.Prime.dvd_mul hqp).mp h with h' | h' <;>
            exact hqp' ((Nat.prime_dvd_prime_iff_eq hqp hp).mp h')
      rw [hbot, Submodule.mem_bot] at hKmem

      have hsupp : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff F n = 0 := by
        intro n hpn
        have := hKc n
        rw [hKmem, if_neg hpn, qCoeff_zero'] at this
        exact this.symm
      have h0 : F = 0 := CuspForm.eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero hp hpm F hsupp
      rw [h0]
      exact (O Q m).zero_mem

end main

end AlliAux1X3

theorem solution
    {m N : ℕ} [NeZero m]
    {f : CuspForm (CongruenceSubgroup.Gamma0 m) 2}
    (hN : 1 < N)
    (hf : ∀ n : ℕ, Nat.Coprime n N → ModularFormClass.qCoeff f n = 0) :
    f ∈ Submodule.span ℂ
      {F : CuspForm (CongruenceSubgroup.Gamma0 m) 2 |
        ∃ (q R : ℕ) (hqR : q * R ∣ m) (fq : CuspForm (CongruenceSubgroup.Gamma0 R) 2),
          q.Prime ∧ q * R = m ∧ F = FreyPackage.ModMCarrier.rescaleLin hqR 2 fq} := by
  have hQ : ∀ q ∈ N.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  have hHyp : AlliAux1X3.Hyp N.primeFactors f := by
    intro n hn
    refine hf n (Nat.coprime_of_dvd fun k hk hkn hkN => ?_)
    exact hn k (Nat.mem_primeFactors.mpr ⟨hk, hkN, by omega⟩) hkn
  have hmem := AlliAux1X3.main N.primeFactors hQ m f hHyp
  refine Submodule.span_mono ?_ hmem
  rintro F ⟨q, R, hqR, fq, _, hqp, hqRm, rfl⟩
  exact ⟨q, R, hqR, fq, hqp, hqRm, rfl⟩

end
end S_CuspForm_mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero
end P2MW
export P2MW.S_CuspForm_mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero (solution)
