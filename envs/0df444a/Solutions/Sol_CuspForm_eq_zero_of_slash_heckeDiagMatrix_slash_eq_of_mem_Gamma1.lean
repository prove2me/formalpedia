-- Prove2me | solution 1 for CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/8a5d25ca-d15e-5a20-b602-308cb0b94b8b

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant
import Theorems.Thm_CuspForm_eq_zero_of_forall_vadd_inv_pow_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CongruenceSubgroup ModularForm UpperHalfPlane SlashInvariantForm
open scoped ModularForm UpperHalfPlane MatrixGroups Pointwise

noncomputable section

namespace Gamma1Stretch

variable {M : ℕ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀(" M ")" => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem mapGL_injective : Function.Injective (Matrix.SpecialLinearGroup.mapGL ℝ : SL(2, ℤ) → _) := by
  intro a b h
  ext i j
  have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simpa using this

theorem mem_coe_iff {Γ : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) :
    (Matrix.SpecialLinearGroup.mapGL ℝ γ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)) ↔ γ ∈ Γ := by
  constructor
  · rintro ⟨g, hg, hgg⟩
    rwa [← mapGL_injective hgg]
  · exact fun h => Subgroup.mem_map_of_mem _ h

theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

theorem det_mod {N : ℕ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hγ
  have := congrArg (Int.cast : ℤ → ZMod N) (det_eq γ)
  push_cast at this
  rw [hc] at this
  linear_combination this

theorem mem_Gamma1_iff_of_mem_Gamma0 {N : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    γ ∈ Gamma1 N ↔ ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  rw [Gamma1_mem]
  constructor
  · rintro ⟨-, h, -⟩; simpa using h
  · intro hd
    have ha : ((γ 0 0 : ℤ) : ZMod N) = 1 := by
      have := det_mod γ hγ; rw [hd, mul_one] at this; exact this
    exact ⟨by simpa using ha, by simpa using hd, by simpa using Gamma0_mem.mp hγ⟩

theorem inv_mul_apply_one_one (γ₁ γ₂ : SL(2, ℤ)) :
    (γ₁⁻¹ * γ₂) 1 1 = -(γ₁ 1 0) * γ₂ 0 1 + γ₁ 0 0 * γ₂ 1 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
  simp

theorem inv_mul_mem_Gamma1_iff {N : ℕ} {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 N) (h₂ : γ₂ ∈ Gamma0 N) :
    γ₁⁻¹ * γ₂ ∈ Gamma1 N ↔ ((γ₁ 1 1 : ℤ) : ZMod N) = ((γ₂ 1 1 : ℤ) : ZMod N) := by
  have hmem : γ₁⁻¹ * γ₂ ∈ Gamma0 N := mul_mem (inv_mem h₁) h₂
  rw [mem_Gamma1_iff_of_mem_Gamma0 hmem, inv_mul_apply_one_one]
  have hc : ((γ₁ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp h₁
  have hdet := det_mod γ₁ h₁
  push_cast
  rw [hc, neg_zero, zero_mul, zero_add]
  constructor
  · intro h
    calc ((γ₁ 1 1 : ℤ) : ZMod N) = ((γ₁ 1 1 : ℤ) : ZMod N) * (((γ₁ 0 0 : ℤ) : ZMod N) * ((γ₂ 1 1 : ℤ) : ZMod N)) := by
          rw [h, mul_one]
      _ = ((γ₂ 1 1 : ℤ) : ZMod N) := by
          rw [← mul_assoc, mul_comm ((γ₁ 1 1 : ℤ) : ZMod N), hdet, one_mul]
  · intro h
    rw [← h, hdet]

section Reps

variable {p : ℕ}

theorem T_zpow_mem_Gamma1 (M : ℕ) (t : ℤ) : ModularGroup.T ^ t ∈ Gamma1 M := by
  rw [Gamma1_mem, ModularGroup.coe_T_zpow]
  simp

def lowerV (M : ℕ) : SL(2, ℤ) := ⟨!![1, 0; (M : ℤ), 1], by rw [Matrix.det_fin_two_of]; ring⟩

theorem lowerV_mem_Gamma1 (M : ℕ) : lowerV M ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp [lowerV]

theorem mul_T_zpow_apply_zero_one (r : SL(2, ℤ)) (t : ℤ) :
    (r * ModularGroup.T ^ t) 0 1 = r 0 0 * t + r 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.mul_apply,
    Fin.sum_univ_two]
  simp

theorem mul_lowerV_apply_zero_zero (M : ℕ) (r : SL(2, ℤ)) :
    (r * lowerV M) 0 0 = r 0 0 + r 0 1 * M := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [lowerV]

theorem mul_lowerV_apply_zero_one (M : ℕ) (r : SL(2, ℤ)) :
    (r * lowerV M) 0 1 = r 0 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  simp [lowerV]

theorem exists_T_zpow_dvd [Fact p.Prime] (r : SL(2, ℤ)) (ha : ¬ (p : ℤ) ∣ r 0 0) :
    ∃ t : ℤ, (p : ℤ) ∣ (r * ModularGroup.T ^ t) 0 1 := by
  have ha' : ((r 0 0 : ℤ) : ZMod p) ≠ 0 := by
    rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  refine ⟨((-((r 0 1 : ℤ) : ZMod p)) * ((r 0 0 : ℤ) : ZMod p)⁻¹).val, ?_⟩
  rw [mul_T_zpow_apply_zero_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val, mul_comm, mul_assoc, inv_mul_cancel₀ ha', mul_one, neg_add_cancel]

theorem exists_mul_mem_Gamma1_dvd [Fact p.Prime] (hpM : ¬ p ∣ M) (r : SL(2, ℤ))
    (hr : r ∈ Gamma0 M) :
    ∃ g : SL(2, ℤ), g ∈ Gamma1 M ∧ (p : ℤ) ∣ (r * g) 0 1 := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  by_cases ha : (p : ℤ) ∣ r 0 0
  ·
    have hb : ¬ (p : ℤ) ∣ r 0 1 := by
      intro hb
      have h1 : (p : ℤ) ∣ 1 := by
        rw [← det_eq r]
        exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_left hb _)
      exact hp.not_dvd_one h1
    have ha' : ¬ (p : ℤ) ∣ (r * lowerV M) 0 0 := by
      rw [mul_lowerV_apply_zero_zero]
      intro h
      have : (p : ℤ) ∣ r 0 1 * M := (dvd_add_right ha).mp h
      rcases hp.dvd_or_dvd this with h1 | h1
      · exact hb h1
      · exact hpM (Int.natCast_dvd_natCast.mp h1)
    obtain ⟨t, ht⟩ := exists_T_zpow_dvd (r * lowerV M) ha'
    exact ⟨lowerV M * ModularGroup.T ^ t, mul_mem (lowerV_mem_Gamma1 M) (T_zpow_mem_Gamma1 M t),
      by rwa [← mul_assoc]⟩
  · obtain ⟨t, ht⟩ := exists_T_zpow_dvd r ha
    exact ⟨ModularGroup.T ^ t, T_zpow_mem_Gamma1 M t, ht⟩

def conjRep (p : ℕ) (r : SL(2, ℤ)) (e : ℤ) (he : r 0 1 = p * e) : SL(2, ℤ) :=
  ⟨!![r 0 0, e; p * r 1 0, r 1 1], by
    rw [Matrix.det_fin_two_of]
    linear_combination det_eq r + (r 1 0) * he⟩

@[scoped simp] theorem conjRep_apply_one_one (r : SL(2, ℤ)) (e : ℤ) (he : r 0 1 = p * e) :
    conjRep p r e he 1 1 = r 1 1 := rfl

@[scoped simp] theorem conjRep_apply_one_zero (r : SL(2, ℤ)) (e : ℤ) (he : r 0 1 = p * e) :
    conjRep p r e he 1 0 = p * r 1 0 := rfl

theorem conjRep_mem_Gamma0 (r : SL(2, ℤ)) (e : ℤ) (he : r 0 1 = p * e) (hr : r ∈ Gamma0 M) :
    conjRep p r e he ∈ Gamma0 M := by
  rw [Gamma0_mem] at hr ⊢
  rw [conjRep_apply_one_zero]
  push_cast
  rw [hr, mul_zero]

theorem mapGL_mul_heckeDiagMatrix (hp : p ≠ 0) (r : SL(2, ℤ)) (e : ℤ) (he : r 0 1 = p * e) :
    Matrix.SpecialLinearGroup.mapGL ℝ r * heckeDiagMatrix p
      = heckeDiagMatrix p * Matrix.SpecialLinearGroup.mapGL ℝ (conjRep p r e he) := by
  have he' : ((r 0 1 : ℤ) : ℝ) = (p : ℝ) * (e : ℝ) := by exact_mod_cast he
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hp, Matrix.mul_apply, Fin.sum_univ_two, conjRep, he'] <;> ring

end Reps

section Analytic

variable {p : ℕ} {k : ℤ}

def diagQ (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(p : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [hp])

theorem map_diagQ (hp : p ≠ 0) :
    Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (diagQ p hp) = heckeDiagMatrix p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagQ, hp]

theorem isArithmetic_conj_heckeDiagMatrix (hp : p ≠ 0) (𝒢 : Subgroup (GL (Fin 2) ℝ))
    [𝒢.IsArithmetic] :
    (ConjAct.toConjAct (heckeDiagMatrix p)⁻¹ • 𝒢).IsArithmetic := by
  have := Subgroup.IsArithmetic.conj 𝒢 (diagQ p hp)⁻¹
  rwa [map_inv, map_diagQ hp] at this

variable [NeZero M]

def stretch (hp : p ≠ 0) (y : CuspForm Γ₁(M) k)
    (hy : ∀ γ ∈ Γ₁(M), ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :
    CuspForm Γ₁(M) k where
  toFun := (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p
  slash_action_eq' := hy
  holo' := (CuspForm.holo' y).slash k _
  zero_at_cusps' := by
    intro c hc
    haveI := isArithmetic_conj_heckeDiagMatrix hp Γ₁(M)
    have hc' : IsCusp c (ConjAct.toConjAct (heckeDiagMatrix p)⁻¹ • Γ₁(M)) := by
      rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢; exact hc
    exact (CuspForm.translate y (heckeDiagMatrix p)).zero_at_cusps' hc'

@[scoped simp] theorem coe_stretch (hp : p ≠ 0) (y : CuspForm Γ₁(M) k)
    (hy : ∀ γ ∈ Γ₁(M), ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :
    ⇑(stretch hp y hy) = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p := rfl

scoped instance instIsFiniteRelIndex : (Γ₁(M)).IsFiniteRelIndex Γ₀(M) :=
  Subgroup.isFiniteRelIndex_of_le_right (H := Γ₁(M)) (Subgroup.map_le_range _ _)

abbrev CosetQ (M : ℕ) := (↥(Γ₀(M))) ⧸ (Γ₁(M)).subgroupOf Γ₀(M)

local notation "𝒬" => CosetQ M

def normCusp (f : CuspForm Γ₁(M) k) : CuspForm Γ₀(M) (k * Nat.card 𝒬) where
  __ := ModularForm.norm Γ₀(M) f
  zero_at_cusps' h γ := by
    rintro rfl
    simp only [ModularForm.toFun_eq_coe, ModularForm.coe_norm]
    let := Fintype.ofFinite 𝒬
    rw [IsZeroAtImInfty, Filter.ZeroAtFilter, Nat.card_eq_fintype_card, ← Finset.card_univ,
      ModularForm.prod_slash]
    rw [show (0 : ℂ) = (|(γ.det : ℝ)| ^ ((Finset.univ : Finset 𝒬).card - 1 : ℤ)) • ∏ _c : 𝒬, (0 : ℂ) by
      rw [Finset.prod_const, Finset.card_univ, zero_pow Fintype.card_ne_zero, smul_zero]]
    refine Filter.Tendsto.const_smul ?_ _
    rw [Finset.prod_fn]
    refine tendsto_finset_prod _ (Quotient.forall.mpr fun ⟨r, hr⟩ _ => ?_)
    refine (CuspForm.translate f _).zero_at_cusps' ?_ γ rfl
    simpa using h.of_isFiniteRelIndex_conj hr

theorem coe_normCusp (f : CuspForm Γ₁(M) k) :
    ⇑(normCusp f) = ⇑(ModularForm.norm Γ₀(M) f) := rfl

end Analytic

section Main

variable {p : ℕ} {k : ℤ} [NeZero M] [Fact p.Prime]

local notation "𝒬" => CosetQ M

theorem quotientFunc_mk' {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} {F : Type*} [FunLike F ℍ ℂ] (f : F)
    [SlashInvariantFormClass F 𝒢 k] (h : ℋ) :
    quotientFunc f (QuotientGroup.mk h : ℋ ⧸ 𝒢.subgroupOf ℋ) = (⇑f : ℍ → ℂ) ∣[k] h.val⁻¹ := rfl

variable (M p) in
theorem exists_rep (hpM : ¬ p ∣ M) (q : 𝒬) :
    ∃ (r : SL(2, ℤ)) (hr : r ∈ Gamma0 M), (p : ℤ) ∣ r 0 1 ∧
      (QuotientGroup.mk ⟨Matrix.SpecialLinearGroup.mapGL ℝ r, Subgroup.mem_map_of_mem _ hr⟩ : 𝒬) = q := by
  induction q using QuotientGroup.induction_on with
  | H h =>
    obtain ⟨r₀, hr₀, hr₀h⟩ := h.2
    obtain ⟨g, hg, hdvd⟩ := exists_mul_mem_Gamma1_dvd hpM r₀ hr₀
    have hg0 : g ∈ Gamma0 M := Gamma1_in_Gamma0 M hg
    refine ⟨r₀ * g, mul_mem hr₀ hg0, hdvd, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (Matrix.SpecialLinearGroup.mapGL ℝ (r₀ * g))⁻¹ * (h : GL (Fin 2) ℝ) ∈ Γ₁(M)
    rw [← hr₀h, ← map_inv, ← map_mul, mem_coe_iff]
    simpa using inv_mem hg

def rep (hpM : ¬ p ∣ M) (q : 𝒬) : SL(2, ℤ) := (exists_rep M p hpM q).choose

theorem rep_mem (hpM : ¬ p ∣ M) (q : 𝒬) : rep hpM q ∈ Gamma0 M :=
  (exists_rep M p hpM q).choose_spec.1

theorem rep_dvd (hpM : ¬ p ∣ M) (q : 𝒬) : (p : ℤ) ∣ rep hpM q 0 1 :=
  (exists_rep M p hpM q).choose_spec.2.1

theorem mk_rep (hpM : ¬ p ∣ M) (q : 𝒬) :
    (QuotientGroup.mk ⟨Matrix.SpecialLinearGroup.mapGL ℝ (rep hpM q),
      Subgroup.mem_map_of_mem _ (rep_mem hpM q)⟩ : 𝒬) = q :=
  (exists_rep M p hpM q).choose_spec.2.2

def repE (hpM : ¬ p ∣ M) (q : 𝒬) : ℤ := (rep_dvd hpM q).choose

theorem rep_eq (hpM : ¬ p ∣ M) (q : 𝒬) : rep hpM q 0 1 = p * repE hpM q :=
  (rep_dvd hpM q).choose_spec

def rep' (hpM : ¬ p ∣ M) (q : 𝒬) : SL(2, ℤ) := conjRep p (rep hpM q) (repE hpM q) (rep_eq hpM q)

theorem rep'_mem (hpM : ¬ p ∣ M) (q : 𝒬) : rep' hpM q ∈ Gamma0 M :=
  conjRep_mem_Gamma0 _ _ _ (rep_mem hpM q)

def Phi (hpM : ¬ p ∣ M) (q : 𝒬) : 𝒬 :=
  QuotientGroup.mk ⟨Matrix.SpecialLinearGroup.mapGL ℝ (rep' hpM q),
    Subgroup.mem_map_of_mem _ (rep'_mem hpM q)⟩

theorem Phi_injective (hpM : ¬ p ∣ M) : Function.Injective (Phi (M := M) hpM) := by
  intro q₁ q₂ h
  rw [Phi, Phi, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
  change (Matrix.SpecialLinearGroup.mapGL ℝ (rep' hpM q₁))⁻¹
    * Matrix.SpecialLinearGroup.mapGL ℝ (rep' hpM q₂) ∈ Γ₁(M) at h
  rw [← map_inv, ← map_mul, mem_coe_iff, inv_mul_mem_Gamma1_iff (rep'_mem hpM q₁) (rep'_mem hpM q₂),
    rep', rep', conjRep_apply_one_one, conjRep_apply_one_one,
    ← inv_mul_mem_Gamma1_iff (rep_mem hpM q₁) (rep_mem hpM q₂)] at h
  rw [← mk_rep hpM q₁, ← mk_rep hpM q₂, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  change (Matrix.SpecialLinearGroup.mapGL ℝ (rep hpM q₁))⁻¹
    * Matrix.SpecialLinearGroup.mapGL ℝ (rep hpM q₂) ∈ Γ₁(M)
  rwa [← map_inv, ← map_mul, mem_coe_iff]

theorem Phi_bijective (hpM : ¬ p ∣ M) : Function.Bijective (Phi (M := M) hpM) :=
  Finite.injective_iff_bijective.mp (Phi_injective hpM)

theorem quotientFunc_slash_heckeDiagMatrix (hpM : ¬ p ∣ M) (y : CuspForm Γ₁(M) k)
    (hy : ∀ γ ∈ Γ₁(M), ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p)
    (q : 𝒬) :
    quotientFunc y q ∣[k] heckeDiagMatrix p
      = quotientFunc (stretch (Fact.out : p.Prime).ne_zero y hy) (Phi hpM q) := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  conv_lhs => rw [← mk_rep hpM q]
  rw [Phi, quotientFunc_mk', quotientFunc_mk', coe_stretch, ← SlashAction.slash_mul,
    ← SlashAction.slash_mul]
  congr 1
  have h := mapGL_mul_heckeDiagMatrix hp0 (rep hpM q) (repE hpM q) (rep_eq hpM q)
  change (Matrix.SpecialLinearGroup.mapGL ℝ (rep hpM q))⁻¹ * heckeDiagMatrix p
    = heckeDiagMatrix p * (Matrix.SpecialLinearGroup.mapGL ℝ (rep' hpM q))⁻¹
  rw [rep', eq_mul_inv_iff_mul_eq, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact h.symm

theorem normCusp_slash_heckeDiagMatrix (hpM : ¬ p ∣ M) (y : CuspForm Γ₁(M) k)
    (hy : ∀ γ ∈ Γ₁(M), ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :
    ∃ C : ℝ, (⇑(normCusp y) : ℍ → ℂ) ∣[k * Nat.card 𝒬] heckeDiagMatrix p
      = C • ⇑(SlashInvariantForm.norm Γ₀(M) (stretch (Fact.out : p.Prime).ne_zero y hy)) := by
  let _ := Fintype.ofFinite 𝒬
  refine ⟨|((heckeDiagMatrix p).det : ℝ)| ^ ((Finset.univ : Finset 𝒬).card - 1 : ℤ), ?_⟩
  rw [coe_normCusp, ModularForm.coe_norm, SlashInvariantForm.coe_norm, Nat.card_eq_fintype_card,
    ← Finset.card_univ, ModularForm.prod_slash]
  congr 1
  rw [← (Phi_bijective hpM).prod_comp fun q => quotientFunc (stretch _ y hy) q]
  exact Finset.prod_congr rfl fun q _ => quotientFunc_slash_heckeDiagMatrix hpM y hy q

theorem main (hp : p.Prime) (hpM : ¬ p ∣ M) (y : CuspForm Γ₁(M) k)
    (hy : ∀ γ ∈ Γ₁(M), ((⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) ∣[k] γ = (⇑y : ℍ → ℂ) ∣[k] heckeDiagMatrix p) :
    y = 0 := by
  obtain ⟨C, hC⟩ := normCusp_slash_heckeDiagMatrix hpM y hy
  have hinv : ∀ γ ∈ Γ₀(M), ((⇑(normCusp y) : ℍ → ℂ) ∣[k * Nat.card 𝒬] heckeDiagMatrix p)
      ∣[k * Nat.card 𝒬] γ = (⇑(normCusp y) : ℍ → ℂ) ∣[k * Nat.card 𝒬] heckeDiagMatrix p := by
    intro γ hγ
    obtain ⟨r, hr, rfl⟩ := hγ
    rw [hC]
    change (C • ⇑(SlashInvariantForm.norm Γ₀(M) (stretch _ y hy))) ∣[k * Nat.card 𝒬] r = _
    rw [ModularForm.SL_smul_slash]
    congr 1
    exact SlashInvariantFormClass.slash_action_eq _ _ (Subgroup.mem_map_of_mem _ hr)
  have hper := CuspForm.vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant hp hpM _ (normCusp y) hinv
  have h0 := CuspForm.eq_zero_of_forall_vadd_inv_pow_eq hp.one_lt _ (normCusp y) hper
  have hy0 : (⇑y : ℍ → ℂ) = 0 := by
    by_contra hne
    apply ModularForm.norm_ne_zero Γ₀(M) hne
    apply DFunLike.coe_injective
    change ⇑(normCusp y) = ⇑(0 : ModularForm Γ₀(M) (k * Nat.card 𝒬))
    rw [h0]
    rfl
  apply DFunLike.coe_injective
  change ⇑y = ⇑(0 : CuspForm Γ₁(M) k)
  rw [hy0]
  rfl

end Main

end Gamma1Stretch
p2m_reactivate "P2MW.S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.Gamma1Stretch"

end
p2m_reactivate "P2MW.S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.Gamma1Stretch"

open Gamma1Stretch in
theorem solution
    {M p : ℕ} [NeZero M] (hp : p.Prime) (hpM : ¬ p ∣ M) (k : ℤ)
    (y : CuspForm ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) k)
    (hy : ∀ γ ∈ ((CongruenceSubgroup.Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      ((⇑y : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix p) ∣[k] γ
        = (⇑y : ℍ → ℂ) ∣[k] ModularForm.heckeDiagMatrix p) :
    y = 0 :=
  haveI : Fact p.Prime := ⟨hp⟩
  Gamma1Stretch.main hp hpM y hy

end S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1
end P2MW
export P2MW.S_CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1 (solution)
