-- Prove2me | solution 1 for CuspForm.exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/d44c765a-426a-514a-86a6-5e5df1e50b04

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_ModularForm_AtkinLehnerDatum
import Definitions.Def_CuspForm_AtkinLehnerOperator
import Definitions.Def_CohCarrier_Level
import Definitions.Def_CuspForm_HeckeOperatorFormsGammaH
import Theorems.Thm_ModularForm_eisenstein_qCoeff_p_integral_dvd
import Theorems.Thm_ModularForm_alSlash_alSlash
import Theorems.Thm_ModularForm_exists_gamma0_qExpansion_eq_of_levelOne
import Theorems.Thm_CuspForm_qCoeff_heckeULinH_eq_qCoeff_mul
import Theorems.Thm_CuspForm_stableU
import Theorems.Thm_CuspForm_stableD
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_alSlash
import Theorems.Thm_CuspForm_exists_GammaH_coe_eq_add_smul_heckeU_alSlash_diamondLinH
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral

set_option autoImplicit false

open UpperHalfPlane ModularFormClass
open scoped MatrixGroups ModularForm

namespace SerreH

namespace SerreAux

section locS
variable (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime)

private def locS : Subring ℂ where
  carrier := {z | ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * z}
  mul_mem' := by
    rintro z z' ⟨x, y, hy, hx⟩ ⟨x', y', hy', hx'⟩
    exact ⟨x * x', y * y', fun h => (h𝔪.mem_or_mem h).elim hy hy', by push_cast; rw [hx, hx']; ring⟩
  one_mem' := ⟨1, 1, fun h => h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  add_mem' := by
    rintro z z' ⟨x, y, hy, hx⟩ ⟨x', y', hy', hx'⟩
    exact ⟨x * y' + x' * y, y * y', fun h => (h𝔪.mem_or_mem h).elim hy hy', by push_cast; rw [hx, hx']; ring⟩
  zero_mem' := ⟨0, 1, fun h => h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩
  neg_mem' := by
    rintro z ⟨x, y, hy, hx⟩
    exact ⟨-x, y, hy, by push_cast; rw [hx]; ring⟩

variable {𝔪 h𝔪}

private lemma mem_locS {z : ℂ} : z ∈ locS 𝔪 h𝔪 ↔ ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * z := Iff.rfl

private lemma coe_mem_locS (x : integralClosure ℤ ℂ) : (x : ℂ) ∈ locS 𝔪 h𝔪 :=
  ⟨x, 1, fun h => h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr h), by simp⟩

include h𝔪 in

private lemma natCast_not_mem {p : ℕ} (hp : p.Prime) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪) {s : ℕ} (hs : ¬ p ∣ s) :
    (s : integralClosure ℤ ℂ) ∉ 𝔪 := by
  intro hsm
  have hcop : IsCoprime (p : ℤ) (s : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hs)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : (1 : integralClosure ℤ ℂ) = (u : integralClosure ℤ ℂ) * p + (v : integralClosure ℤ ℂ) * s := by
    have := congrArg (fun z : ℤ => (z : integralClosure ℤ ℂ)) huv
    push_cast at this
    exact this.symm
  exact h𝔪.ne_top ((Ideal.eq_top_iff_one _).mpr
    (h1 ▸ 𝔪.add_mem (𝔪.mul_mem_left _ hp𝔪) (𝔪.mul_mem_left _ hsm)))

private lemma inv_natCast_mem {p : ℕ} (hp : p.Prime) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪) {s : ℕ} (hs : ¬ p ∣ s) :
    ((s : ℂ))⁻¹ ∈ locS 𝔪 h𝔪 := by
  have hs0 : (s : ℂ) ≠ 0 := by
    have : s ≠ 0 := fun h => hs (h ▸ dvd_zero p)
    exact_mod_cast this
  exact ⟨1, s, natCast_not_mem (h𝔪 := h𝔪) hp hp𝔪 hs, by simp [hs0]⟩

private lemma cross_mem {p : ℕ} (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪) {aF aG s : ℂ} (hs : s ∈ locS 𝔪 h𝔪)
    (hdiff : aG - aF = p * s) (x y x' y' : integralClosure ℤ ℂ)
    (hx : (x : ℂ) = y * aF) (hx' : (x' : ℂ) = y' * aG) : x * y' - x' * y ∈ 𝔪 := by
  obtain ⟨u, v, hv, hu⟩ := hs
  have key : v * (x * y' - x' * y) = -(y * y' * p * u) := by
    apply Subtype.coe_injective
    push_cast
    rw [hx, hx', hu]
    have : aG = aF + p * s := by rw [← hdiff]; ring
    rw [this]; ring
  have hmem : v * (x * y' - x' * y) ∈ 𝔪 := by
    rw [key]
    exact 𝔪.neg_mem (𝔪.mul_mem_right _ (𝔪.mul_mem_left _ hp𝔪))
  exact (h𝔪.mem_or_mem hmem).resolve_left hv

private noncomputable def LS : Subring (PowerSeries ℂ) := (PowerSeries.map (locS 𝔪 h𝔪).subtype).range

private lemma mem_LS_iff {φ : PowerSeries ℂ} : φ ∈ LS (𝔪 := 𝔪) (h𝔪 := h𝔪) ↔ ∀ n, PowerSeries.coeff n φ ∈ locS 𝔪 h𝔪 := by
  constructor
  · rintro ⟨ψ, rfl⟩ n
    rw [PowerSeries.coeff_map]
    exact (PowerSeries.coeff n ψ).2
  · intro h
    refine ⟨PowerSeries.mk fun n => ⟨PowerSeries.coeff n φ, h n⟩, ?_⟩
    ext n
    simp [PowerSeries.coeff_map]

private lemma C_mem_LS {z : ℂ} (hz : z ∈ locS 𝔪 h𝔪) : PowerSeries.C z ∈ LS (𝔪 := 𝔪) (h𝔪 := h𝔪) := by
  rw [mem_LS_iff]; intro n
  rw [PowerSeries.coeff_C]
  split_ifs
  · exact hz
  · exact (locS 𝔪 h𝔪).zero_mem

end locS

section al
variable {M q : ℕ} (A : ModularForm.AtkinLehnerDatum M q)

private def gam0 : SL(2, ℤ) :=
  ⟨!![A.a, A.b; (A.R : ℤ), (q : ℤ)], by rw [Matrix.det_fin_two_of]; linear_combination A.bezout⟩

@[scoped simp] private lemma gam0_coe : ((gam0 A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![A.a, A.b; (A.R : ℤ), (q : ℤ)] := rfl

private lemma alGL_eq [NeZero M] :
    A.alGL = Matrix.SpecialLinearGroup.mapGL ℝ (gam0 A) * ModularForm.heckeDiagMatrix q := by
  have hq0 : q ≠ 0 := A.q_pos.ne'
  apply Units.ext
  rw [Units.val_mul, ModularForm.AtkinLehnerDatum.alGL_coe, ModularForm.val_heckeDiagMatrix hq0]
  change _ = ((gam0 A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (algebraMap ℤ ℝ) * _
  rw [gam0_coe, ModularForm.AtkinLehnerDatum.mat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private lemma alSlash_levelOne_apply [NeZero M] {k : ℤ} (E : ModularForm 𝒮ℒ k) (τ : UpperHalfPlane) :
    ModularForm.alSlash A k ⇑E τ = (q : ℂ) ^ (k - 1) * E (ModularForm.heckeDiagMatrix q • τ) := by
  have hq0 : q ≠ 0 := A.q_pos.ne'
  have hmem : Matrix.SpecialLinearGroup.mapGL ℝ (gam0 A) ∈ 𝒮ℒ := ⟨gam0 A, rfl⟩
  rw [ModularForm.alSlash_def, alGL_eq, SlashAction.slash_mul,
    SlashInvariantForm.slash_action_eqn E _ hmem, ModularForm.slash_heckeDiagMatrix_apply k hq0]

private lemma coeff_qExpansion_alSlash_levelOne [NeZero M] {k : ℤ} (E : ModularForm 𝒮ℒ k)
    (EM : ModularForm (CongruenceSubgroup.Gamma0 M) k) (hEM : (⇑EM : UpperHalfPlane → ℂ) = ⇑E) (n : ℕ) :
    PowerSeries.coeff n (qExpansion 1 (ModularForm.alSlash A k ⇑EM)) =
      (q : ℂ) ^ (k - 1) * (if q ∣ n then PowerSeries.coeff (n / q) (qExpansion 1 ⇑E) else 0) := by
  have hq0 : q ≠ 0 := A.q_pos.ne'
  have hqpos : 0 < q := A.q_pos
  have h1M : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h1S : (1 : ℝ) ∈ (𝒮ℒ).strictPeriods := by simp
  haveI : Fact (IsCusp OnePoint.infty 𝒮ℒ) := ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1S⟩
  have hEW : (⇑(ModularForm.atkinLehnerLin A k EM) : UpperHalfPlane → ℂ) = ModularForm.alSlash A k ⇑EM := rfl
  rw [← hEW]
  symm
  refine ModularFormClass.qExpansion_coeff_unique one_pos h1M (f := ModularForm.atkinLehnerLin A k EM)
    (c := fun n => (q : ℂ) ^ (k - 1) * (if q ∣ n then PowerSeries.coeff (n / q) (qExpansion 1 ⇑E) else 0))
    (fun τ => ?_) n
  rw [show (ModularForm.atkinLehnerLin A k EM) τ = ModularForm.alSlash A k ⇑EM τ from rfl, hEM,
    alSlash_levelOne_apply A E τ]
  have hsum := hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex E h1S) (holo E)
    (bdd_at_infty E) (ModularForm.heckeDiagMatrix q • τ)
  have hq : Function.Periodic.qParam 1 ((ModularForm.heckeDiagMatrix q • τ : UpperHalfPlane) : ℂ) =
      Function.Periodic.qParam 1 (τ : ℂ) ^ q := by
    rw [ModularForm.coe_heckeDiagMatrix_smul hq0 τ]
    simp only [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hq] at hsum
  have hsupp : ∀ x ∉ Set.range (fun m : ℕ => q * m),
      (fun j : ℕ => ((q : ℂ) ^ (k - 1) * (if q ∣ j then PowerSeries.coeff (j / q) (qExpansion 1 ⇑E) else 0)) •
        Function.Periodic.qParam 1 (τ : ℂ) ^ j) x = 0 := by
    intro x hx
    have : ¬ q ∣ x := fun ⟨m, hm⟩ => hx ⟨m, hm.symm⟩
    simp [this]
  refine ((mul_right_injective₀ hq0).hasSum_iff hsupp).mp ?_
  convert hsum.mul_left ((q : ℂ) ^ (k - 1)) using 1
  all_goals first
    | rfl
    | (ext m
       simp only [Function.comp_apply, Nat.mul_div_cancel_left _ hqpos, dvd_mul_right, if_true, pow_mul,
         smul_eq_mul]
       ring)

private lemma alSlash_pow [NeZero M] (k : ℤ) (f : UpperHalfPlane → ℂ) (i : ℕ) (hi : 1 ≤ i) :
    ModularForm.alSlash A (i * k) (f ^ i) = (q : ℂ) ^ ((i : ℤ) - 1) • (ModularForm.alSlash A k f) ^ i := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast A.q_pos.ne'
  induction i, hi using Nat.le_induction with
  | base => simp
  | succ i hi ih =>
    have hdet : |((A.alGL).det : ℝ)| = (q : ℝ) := by
      rw [ModularForm.AtkinLehnerDatum.val_det_alGL]; exact abs_of_nonneg (Nat.cast_nonneg q)
    rw [Nat.cast_succ, add_mul, one_mul, pow_succ, ModularForm.alSlash_def, ModularForm.mul_slash, hdet,
      ← ModularForm.alSlash_def, ← ModularForm.alSlash_def, ih, pow_succ]
    ext τ
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_natCast]
    rw [show (i : ℤ) + 1 - 1 = ((i : ℤ) - 1) + 1 by ring, zpow_add_one₀ hq0]
    ring

end al

end SerreAux
p2m_reactivate "P2MW.S_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral.SerreH.SerreAux"

end SerreH
p2m_reactivate "P2MW.S_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral.SerreH.SerreAux P2MW.S_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral.SerreH"

namespace SerreH

open CongruenceSubgroup

theorem T_mem_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have h0 : ModularGroup.T ∈ Gamma0 M := by
    rw [Gamma0_mem]; simp [ModularGroup.T]
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨ModularGroup.T, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((ModularGroup.T 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    simp [ModularGroup.T]
  rw [this]
  exact one_mem H

theorem one_mem_strictPeriods_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (1 : ℝ) ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_GammaH M H)]
  exact AddSubgroup.mem_zmultiples 1

theorem GammaH_le_Gamma0_GL (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) ≤ (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) :=
  Subgroup.map_mono (CohCarrier.GammaH_le_Gamma0 H)

def restrictH {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ) {k : ℤ} (f : ModularForm (Gamma0 M) k) :
    ModularForm (CohCarrier.GammaH M H) k where
  toFun := f
  slash_action_eq' γ hγ := SlashInvariantForm.slash_action_eqn f γ (GammaH_le_Gamma0_GL M H hγ)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono (GammaH_le_Gamma0_GL M H))

@[scoped simp] theorem coe_restrictH {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ) {k : ℤ} (f : ModularForm (Gamma0 M) k) :
    (⇑(restrictH H f) : UpperHalfPlane → ℂ) = ⇑f := rfl

end SerreH
p2m_reactivate "P2MW.S_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral.SerreH.SerreAux P2MW.S_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral.SerreH"

open SerreH SerreH.SerreAux in

theorem solution
    (p : ℕ) [Fact p.Prime] {M : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M p)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Dvd.intro_left p W.hM.symm) u = 1 → u ∈ H)
    (d : (ZMod M)ˣ) (hd : (ZMod.unitsMap (Dvd.intro_left p W.hM.symm) d : ZMod W.R) * (p : ZMod W.R) = 1)
    (a : ℕ) (ha : 3 ≤ a) (ha2 : Even a) (hpa : p - 1 ∣ a)
    (𝔪 : Ideal (integralClosure ℤ ℂ)) (h𝔪 : 𝔪.IsPrime) (hp𝔪 : (p : integralClosure ℤ ℂ) ∈ 𝔪)
    (w : ℤ) (hw : 2 ≤ w) (F : CuspForm (CohCarrier.GammaH M H) w)
    (hFint : ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff F n)
    (hFW : ∃ c : ℕ, ∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧
      (x : ℂ) = y * (p : ℂ) ^ c * qCoeff (ModularForm.alSlash W w ⇑(CuspForm.diamondLinH w d F)) n) :
    ∃ i₀ : ℕ, ∀ i : ℕ, i₀ ≤ i →
      ∃ G : CuspForm (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm)))) (w + i * a),
        (∀ n : ℕ, ∃ x y : integralClosure ℤ ℂ, y ∉ 𝔪 ∧ (x : ℂ) = y * qCoeff G n) ∧
        (∀ (n : ℕ) (x y x' y' : integralClosure ℤ ℂ), y ∉ 𝔪 → y' ∉ 𝔪 →
          (x : ℂ) = y * qCoeff F n → (x' : ℂ) = y' * qCoeff G n → x * y' - x' * y ∈ 𝔪) := by
  classical
  obtain ⟨c, hFWc⟩ := hFW
  refine ⟨w.toNat + c, fun i hi => ?_⟩
  have hp : p.Prime := Fact.out
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp0
  have hw0 : 0 ≤ w := by omega
  haveI : NeZero W.R := ⟨W.R_pos.ne'⟩
  have h1M : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by simp
  have h1H : (1 : ℝ) ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    SerreH.one_mem_strictPeriods_GammaH M H
  have h1R : (1 : ℝ) ∈ (CohCarrier.GammaH W.R (H.map (ZMod.unitsMap (Dvd.intro_left p W.hM.symm))) :
      Subgroup (GL (Fin 2) ℝ)).strictPeriods := SerreH.one_mem_strictPeriods_GammaH _ _

  have hS1 : ∀ x : integralClosure ℤ ℂ, (x : ℂ) ∈ locS 𝔪 h𝔪 := fun x => coe_mem_locS x

  have ha3 := ha
  have hpa' : ((p : ℤ) - 1 ∣ (a : ℤ)) := by
    have h := Int.natCast_dvd_natCast.mpr hpa
    rw [Nat.cast_sub hp.one_le] at h
    exact_mod_cast h
  have ha1 : 1 ≤ a := by omega
  have hza1 : (p : ℂ) ^ ((a : ℤ) - 1) = (p : ℂ) ^ (a - 1) := by
    rw [← zpow_natCast, Nat.cast_sub ha1]; norm_num
  have hza2 : (p : ℂ) ^ ((a : ℤ) - 2) = (p : ℂ) ^ (a - 2) := by
    rw [← zpow_natCast, Nat.cast_sub (by omega : 2 ≤ a)]; norm_num

  set E : ModularForm 𝒮ℒ a := ModularForm.E ha3 with hEdef
  let e : ℕ → ℂ := fun m => PowerSeries.coeff m (qExpansion 1 ⇑E)
  have he0 : e 0 = 1 := EisensteinSeries.E_qExpansion_coeff_zero ha3 ha2
  let e' : ℕ → ℂ := fun m => if m = 0 then 0 else e m / p
  have he' : ∀ m, e' m ∈ locS 𝔪 h𝔪 := by
    intro m
    by_cases hm : m = 0
    · simp only [e', hm, if_true]; exact (locS 𝔪 h𝔪).zero_mem
    · obtain ⟨x, s, hps, hxs, hpx⟩ :=
        ModularForm.eisenstein_qCoeff_p_integral_dvd p ha3 ha2 hpa m (Nat.pos_of_ne_zero hm)
      have hs0 : (s : ℂ) ≠ 0 := by
        have : s ≠ 0 := fun h => hps (h ▸ dvd_zero p)
        exact_mod_cast this
      have : e' m = ((x / p : ℤ) : ℂ) * ((s : ℂ))⁻¹ := by
        simp only [e', hm, if_false]
        rw [Int.cast_div hpx (by exact_mod_cast hp0 : ((p : ℤ) : ℂ) ≠ 0)]
        have hem : e m = x / s := by
          simp only [e]; rw [hEdef, hxs]; field_simp
        rw [hem]
        push_cast
        field_simp
      rw [this]
      exact (locS 𝔪 h𝔪).mul_mem (intCast_mem (locS 𝔪 h𝔪) _) (inv_natCast_mem hp hp𝔪 hps)
  have hee' : ∀ m, e m = (if m = 0 then 1 else 0) + p * e' m := by
    intro m
    by_cases hm : m = 0
    · simp [e', hm, he0]
    · simp only [e', hm, if_false]; field_simp; ring
  let ε' : PowerSeries ℂ := PowerSeries.mk e'
  have hε'S : ε' ∈ LS (𝔪 := 𝔪) (h𝔪 := h𝔪) := mem_LS_iff.mpr fun n => by simpa [ε'] using he' n
  have hε : qExpansion 1 ⇑E = 1 + PowerSeries.C (p : ℂ) * ε' := by
    ext m
    rw [map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    exact hee' m

  let vε' : PowerSeries ℂ := PowerSeries.mk fun n => if p ∣ n then e' (n / p) else 0
  have hvε'S : vε' ∈ LS (𝔪 := 𝔪) (h𝔪 := h𝔪) := mem_LS_iff.mpr fun n => by
    simp only [vε', PowerSeries.coeff_mk]
    split_ifs
    · exact he' _
    · exact (locS 𝔪 h𝔪).zero_mem

  obtain ⟨EM, hEM⟩ := ModularForm.exists_gamma0_qExpansion_eq_of_levelOne M E
  have hEMinv : ∀ γ ∈ (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)),
      (⇑EM : UpperHalfPlane → ℂ) ∣[(a : ℤ)] γ = ⇑EM := fun γ hγ => SlashInvariantForm.slash_action_eqn EM γ hγ
  let EW : ModularForm (CongruenceSubgroup.Gamma0 M) a := ModularForm.atkinLehnerLin W a EM
  have hEWcoe : (⇑EW : UpperHalfPlane → ℂ) = ModularForm.alSlash W a ⇑EM := rfl
  have hEWq : qExpansion 1 ⇑EW = PowerSeries.C ((p : ℂ) ^ (a - 1)) * (1 + PowerSeries.C (p : ℂ) * vε') := by
    ext n
    rw [hEWcoe, coeff_qExpansion_alSlash_levelOne W E EM hEM n, hza1, PowerSeries.coeff_C_mul, map_add,
      PowerSeries.coeff_one, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
    congr 1
    by_cases hpn : p ∣ n
    · rw [if_pos hpn, if_pos hpn]
      change e (n / p) = _
      rw [hee' (n / p)]
      obtain ⟨m, rfl⟩ := hpn
      rw [Nat.mul_div_cancel_left _ hp.pos]
      by_cases hm : m = 0 <;> simp [hm, hp0]
    · rw [if_neg hpn, if_neg hpn, if_neg (fun h => hpn (by rw [h]; exact dvd_zero p))]
      ring
  let g : ModularForm (CongruenceSubgroup.Gamma0 M) a := EM + (-(p : ℂ)) • EW
  have hgcoe : (⇑g : UpperHalfPlane → ℂ) = ⇑EM + (-(p : ℂ)) • ⇑EW := by
    rw [ModularForm.coe_add, ModularForm.IsGLPos.coe_smul]

  let γ' : PowerSeries ℂ := ε' - PowerSeries.C ((p : ℂ) ^ (a - 1)) * (1 + PowerSeries.C (p : ℂ) * vε')
  have hγ'S : γ' ∈ LS (𝔪 := 𝔪) (h𝔪 := h𝔪) := by
    refine (LS).sub_mem hε'S ((LS).mul_mem (C_mem_LS ?_) ((LS).add_mem (LS).one_mem
      ((LS).mul_mem (C_mem_LS ?_) hvε'S)))
    · exact (locS 𝔪 h𝔪).pow_mem (natCast_mem (locS 𝔪 h𝔪) p) _
    · exact natCast_mem (locS 𝔪 h𝔪) p
  have hX : qExpansion 1 ⇑g = 1 + PowerSeries.C (p : ℂ) * γ' := by
    rw [hgcoe, qExpansion_add (ModularFormClass.analyticAt_cuspFunction_zero EM one_pos h1M)
      (by rw [← ModularForm.IsGLPos.coe_smul]; exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos h1M),
      qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero EW one_pos h1M), hEM, hε, hEWq]
    simp only [γ', PowerSeries.smul_eq_C_mul, map_neg]
    ring

  let gWf : ModularForm (CongruenceSubgroup.Gamma0 M) a := ModularForm.atkinLehnerLin W a g
  have hgWcoe : (⇑gWf : UpperHalfPlane → ℂ) = ⇑EW + (-(p : ℂ) * (p : ℂ) ^ (a - 2)) • ⇑EM := by
    show ModularForm.alSlash W a ⇑g = _
    rw [hgcoe, ModularForm.alSlash_add, ModularForm.alSlash_smul, ← hEWcoe, hEWcoe,
      ModularForm.alSlash_alSlash W a hEMinv, hza2, smul_smul]
  let γW' : PowerSeries ℂ := vε' - ε'
  have hγW'S : γW' ∈ LS (𝔪 := 𝔪) (h𝔪 := h𝔪) := (LS).sub_mem hvε'S hε'S
  have hY : qExpansion 1 ⇑gWf = PowerSeries.C ((p : ℂ) ^ a) * γW' := by
    rw [hgWcoe, qExpansion_add (ModularFormClass.analyticAt_cuspFunction_zero EW one_pos h1M)
      (by rw [← ModularForm.IsGLPos.coe_smul]; exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos h1M),
      qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero EM one_pos h1M), hEM, hε, hEWq]
    simp only [γW', PowerSeries.smul_eq_C_mul, map_neg, map_mul, map_pow]
    have hpa1 : PowerSeries.C (p : ℂ) ^ (a - 1) = PowerSeries.C (p : ℂ) ^ (a - 2) * PowerSeries.C (p : ℂ) := by
      rw [← pow_succ, show a - 2 + 1 = a - 1 by omega]
    have hpa2 : PowerSeries.C (p : ℂ) ^ a = PowerSeries.C (p : ℂ) ^ (a - 2) * PowerSeries.C (p : ℂ) *
        PowerSeries.C (p : ℂ) := by
      rw [← pow_succ, ← pow_succ, show a - 2 + 1 + 1 = a by omega]
    rw [hpa1, hpa2]
    ring

  let gH : ModularForm (CohCarrier.GammaH M H) a := SerreH.restrictH H g
  let gWH : ModularForm (CohCarrier.GammaH M H) a := SerreH.restrictH H gWf
  have hgH : (⇑gH : UpperHalfPlane → ℂ) = ⇑g := rfl
  have hgWH : (⇑gWH : UpperHalfPlane → ℂ) = ⇑gWf := rfl

  have hD : ∀ k : ℤ, CuspForm.StableD M H k := fun k => CuspForm.stableD M H k
  set Fd : CuspForm (CohCarrier.GammaH M H) w := CuspForm.diamondLinH w d F with hFd
  have hΦS : qExpansion 1 ⇑F ∈ LS (𝔪 := 𝔪) (h𝔪 := h𝔪) := mem_LS_iff.mpr fun n => hFint n
  obtain ⟨FWf, hFWcoe⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHp w Fd
  have hΦW'S : PowerSeries.C ((p : ℂ) ^ c) * qExpansion 1 ⇑FWf ∈ LS (𝔪 := 𝔪) (h𝔪 := h𝔪) :=
    mem_LS_iff.mpr fun n => by
      obtain ⟨x, y, hy, hx⟩ := hFWc n
      rw [PowerSeries.coeff_C_mul]
      exact ⟨x, y, hy, by rw [hx, hFWcoe]; simp only [mul_assoc]; rfl⟩

  have hi1 : 1 ≤ i := by omega
  let Hf : CuspForm (CohCarrier.GammaH M H) (w + i * a) := F.mulModularForm (gH.pow i)
  set Hd : CuspForm (CohCarrier.GammaH M H) (w + i * a) := CuspForm.diamondLinH (w + i * a) d Hf with hHd

  have hHdcoe : (⇑Hd : UpperHalfPlane → ℂ) = ⇑Fd * (⇑g) ^ i := by
    have hσ : ((Matrix.SpecialLinearGroup.mapGL ℝ (CuspForm.gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)) ∈
        (CongruenceSubgroup.Gamma0 M : Subgroup (GL (Fin 2) ℝ)) :=
      ⟨(CuspForm.gammaLift M d : SL(2, ℤ)), (CuspForm.gammaLift M d).2, rfl⟩
    have hginv : (⇑(g.pow i) : UpperHalfPlane → ℂ) ∣[((i : ℤ) * a)]
        ((Matrix.SpecialLinearGroup.mapGL ℝ (CuspForm.gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)) = ⇑(g.pow i) :=
      SlashInvariantForm.slash_action_eqn (g.pow i) _ hσ
    have hdet : |(((Matrix.SpecialLinearGroup.mapGL ℝ (CuspForm.gammaLift M d : SL(2, ℤ)) : GL (Fin 2) ℝ)).det : ℝ)| = 1 := by
      simp
    rw [hHd, hFd, CuspForm.coe_diamondLinH_apply _ (hD _), CuspForm.coe_diamondLinH_apply _ (hD _),
      show (⇑Hf : UpperHalfPlane → ℂ) = ⇑F * ⇑(g.pow i) by
        rw [show (⇑Hf : UpperHalfPlane → ℂ) = ⇑F * ⇑(gH.pow i) from rfl, ModularForm.coe_pow, ModularForm.coe_pow]; rfl,
      ModularForm.mul_slash, hdet, one_smul, hginv, ModularForm.coe_pow]
  obtain ⟨G, hG⟩ :=
    CuspForm.exists_GammaH_coe_eq_add_smul_heckeU_alSlash_diamondLinH hp W H hHp (w + i * a) Hf d hd
  rw [← hHd] at hG

  obtain ⟨ALH, hALHcoe⟩ := CuspForm.exists_GammaH_coe_eq_alSlash hp W H hHp (w + i * a) Hd
  have hpM : p ∣ M := Dvd.intro _ W.hM.symm
  have hU : CuspForm.StableU M H (w + i * a) p := CuspForm.stableU M H _ hp hpM
  let Uf : CuspForm (CohCarrier.GammaH M H) (w + i * a) := CuspForm.heckeULinH (w + i * a) p ALH
  have hUf : (⇑Uf : UpperHalfPlane → ℂ) = ModularForm.heckeU (w + i * a) p ⇑ALH :=
    CuspForm.coe_heckeULinH_apply _ hU ALH

  have hGq : qExpansion 1 ⇑G = qExpansion 1 ⇑Hf + (p : ℂ) ^ (2 - (w + i * a)) • qExpansion 1 ⇑Uf := by
    rw [hG, ← hALHcoe, ← hUf, qExpansion_add (ModularFormClass.analyticAt_cuspFunction_zero Hf one_pos h1H)
      (by rw [← CuspForm.IsGLPos.coe_smul]; exact ModularFormClass.analyticAt_cuspFunction_zero _ one_pos h1H),
      qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero Uf one_pos h1H)]
  have hUq : ∀ n, PowerSeries.coeff n (qExpansion 1 ⇑Uf) = PowerSeries.coeff (n * p) (qExpansion 1 ⇑ALH) :=
    fun n => CuspForm.qCoeff_heckeULinH_eq_qCoeff_mul M H _ hp hpM ALH n

  have hHq : qExpansion 1 ⇑Hf = qExpansion 1 ⇑F * (qExpansion 1 ⇑g) ^ i := by
    rw [show (⇑Hf : UpperHalfPlane → ℂ) = ⇑F * ⇑(gH.pow i) from rfl,
      ModularForm.qExpansion_mul_coe one_pos h1H F (gH.pow i), ModularForm.qExpansion_pow one_pos h1H gH i]
    rfl
  let HW : CuspForm (CohCarrier.GammaH M H) (w + i * a) := FWf.mulModularForm (gWH.pow i)
  have hALH : (⇑ALH : UpperHalfPlane → ℂ) = ((p : ℂ) ^ i) • ⇑HW := by
    rw [hALHcoe, hHdcoe, ModularForm.alSlash_def, ModularForm.mul_slash, ← ModularForm.alSlash_def,
      ← ModularForm.alSlash_def, alSlash_pow W a ⇑g i hi1,
      show (⇑HW : UpperHalfPlane → ℂ) = ⇑FWf * ⇑(gWH.pow i) from rfl, ModularForm.coe_pow,
      ModularForm.AtkinLehnerDatum.val_det_alGL, abs_of_nonneg (Nat.cast_nonneg p)]
    ext τ
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.pow_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_natCast]
    have hpi : (p : ℂ) ^ ((i : ℤ) - 1) * p = (p : ℂ) ^ i := by
      rw [← zpow_add_one₀ hpC, sub_add_cancel, zpow_natCast]
    rw [← hpi]
    simp only [hFWcoe, hgWH, show (⇑gWf : UpperHalfPlane → ℂ) = ModularForm.alSlash W a ⇑g from rfl]
    ring
  have hALHq : qExpansion 1 ⇑ALH = PowerSeries.C ((p : ℂ) ^ i) * (qExpansion 1 ⇑FWf * (qExpansion 1 ⇑gWf) ^ i) := by
    rw [hALH, qExpansion_smul (ModularFormClass.analyticAt_cuspFunction_zero HW one_pos h1H),
      show (⇑HW : UpperHalfPlane → ℂ) = ⇑FWf * ⇑(gWH.pow i) from rfl,
      ModularForm.qExpansion_mul_coe one_pos h1H FWf (gWH.pow i), ModularForm.qExpansion_pow one_pos h1H gWH i,
      PowerSeries.smul_eq_C_mul]
    rfl

  set Φ := qExpansion 1 ⇑F with hΦdef
  set X := qExpansion 1 ⇑g with hXdef
  set ΦW' := PowerSeries.C ((p : ℂ) ^ c) * qExpansion 1 ⇑FWf with hΦW'def
  have hXS : X ∈ LS (𝔪 := 𝔪) (h𝔪 := h𝔪) := by
    rw [hX]; exact (LS).add_mem (LS).one_mem ((LS).mul_mem (C_mem_LS (natCast_mem (locS 𝔪 h𝔪) p)) hγ'S)
  have hgeom : X ^ i - 1 = (∑ j ∈ Finset.range i, X ^ j) * (PowerSeries.C (p : ℂ) * γ') := by
    rw [← geom_sum_mul X i, hX]; congr 1; ring

  obtain ⟨t, ht⟩ : ∃ t : ℕ, i = w.toNat + c + t := ⟨i - (w.toNat + c), by omega⟩
  have hkey : ∀ n : ℕ, ∃ s ∈ locS 𝔪 h𝔪, qCoeff (⇑G) n - qCoeff (⇑F) n = p * s := by
    intro n
    set s₁ := PowerSeries.coeff n (Φ * γ' * ∑ j ∈ Finset.range i, X ^ j) with hs₁
    set s₂ := PowerSeries.coeff (n * p) (ΦW' * γW' ^ i) with hs₂
    have hs₁S : s₁ ∈ locS 𝔪 h𝔪 := mem_LS_iff.mp ((LS).mul_mem ((LS).mul_mem hΦS hγ'S)
      ((LS).sum_mem fun j _ => (LS).pow_mem hXS j)) n
    have hs₂S : s₂ ∈ locS 𝔪 h𝔪 := mem_LS_iff.mp ((LS).mul_mem hΦW'S ((LS).pow_mem hγW'S i)) (n * p)
    refine ⟨s₁ + p * (p : ℂ) ^ t * s₂, (locS 𝔪 h𝔪).add_mem hs₁S ((locS 𝔪 h𝔪).mul_mem
      ((locS 𝔪 h𝔪).mul_mem (natCast_mem (locS 𝔪 h𝔪) p) ((locS 𝔪 h𝔪).pow_mem (natCast_mem (locS 𝔪 h𝔪) p) t)) hs₂S), ?_⟩

    have haG : qCoeff (⇑G) n = PowerSeries.coeff n (Φ * X ^ i) +
        (p : ℂ) ^ (2 - (w + i * a)) * ((p : ℂ) ^ i * ((p : ℂ) ^ a) ^ i * ((p : ℂ) ^ c)⁻¹ * s₂) := by
      change PowerSeries.coeff n (qExpansion 1 ⇑G) = _
      rw [hGq, map_add, PowerSeries.coeff_smul, hUq, hHq, hALHq, hY, smul_eq_mul, hs₂, hΦW'def]
      congr 2
      have htt : PowerSeries.coeff (n * p) (PowerSeries.C ((p : ℂ) ^ i) *
          (qExpansion 1 ⇑FWf * (PowerSeries.C ((p : ℂ) ^ a) * γW') ^ i)) =
          (p : ℂ) ^ i * (((p : ℂ) ^ a) ^ i * PowerSeries.coeff (n * p) (qExpansion 1 ⇑FWf * γW' ^ i)) := by
        rw [PowerSeries.coeff_C_mul, mul_pow, ← map_pow, mul_left_comm, PowerSeries.coeff_C_mul]
      have htt' : PowerSeries.coeff (n * p) (PowerSeries.C ((p : ℂ) ^ c) * qExpansion 1 ⇑FWf * γW' ^ i) =
          (p : ℂ) ^ c * PowerSeries.coeff (n * p) (qExpansion 1 ⇑FWf * γW' ^ i) := by
        rw [mul_assoc, PowerSeries.coeff_C_mul]
      rw [htt, htt']
      field_simp
    have hpow : (p : ℂ) ^ (2 - (w + i * a)) * ((p : ℂ) ^ i * ((p : ℂ) ^ a) ^ i * ((p : ℂ) ^ c)⁻¹) =
        (p : ℂ) ^ 2 * (p : ℂ) ^ t := by
      rw [← pow_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hpC, ← zpow_add₀ hpC,
        ← zpow_add₀ hpC, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hpC]
      congr 1
      push_cast
      rw [ht]; push_cast; rw [Int.toNat_of_nonneg hw0]; ring
    rw [haG, ← mul_assoc ((p : ℂ) ^ (2 - (w + i * a))), hpow]
    change _ - PowerSeries.coeff n Φ = _
    have h1 : PowerSeries.coeff n (Φ * X ^ i) - PowerSeries.coeff n Φ = p * s₁ := by
      rw [hs₁, ← PowerSeries.coeff_C_mul, ← map_sub,
        show Φ * X ^ i - Φ = Φ * (X ^ i - 1) by ring, hgeom]
      congr 1; ring
    linear_combination h1

  refine ⟨G, ?_, ?_⟩
  · intro n
    obtain ⟨s, hs, hdiff⟩ := hkey n
    have : qCoeff (⇑G) n = qCoeff (⇑F) n + p * s := by rw [← hdiff]; ring
    have hmem : qCoeff (⇑G) n ∈ locS 𝔪 h𝔪 := by
      rw [this]
      exact (locS 𝔪 h𝔪).add_mem (hFint n) ((locS 𝔪 h𝔪).mul_mem (natCast_mem (locS 𝔪 h𝔪) p) hs)
    exact hmem
  · intro n x y x' y' hy hy' hx hx'
    obtain ⟨s, hs, hdiff⟩ := hkey n
    exact cross_mem hp𝔪 hs hdiff x y x' y' hx hx'

end S_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral
end P2MW
export P2MW.S_CuspForm_exists_forall_weight_add_mul_qCoeff_congr_gammaH_level_div_of_alSlash_diamondLinH_p_integral (solution)
