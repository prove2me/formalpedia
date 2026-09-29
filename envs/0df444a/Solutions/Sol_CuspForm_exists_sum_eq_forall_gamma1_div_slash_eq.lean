-- Prove2me | solution 1 for CuspForm.exists_sum_eq_forall_gamma1_div_slash_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/787bca5e-82d4-57dc-a887-6ba081c7e7bd

import Mathlib
import Theorems.Thm_CongruenceSubgroup_Gamma_div_le_gamma1_inf_Gamma_sup_zpowers
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace DS575Sol

open CongruenceSubgroup ModularForm SlashInvariantForm Matrix MatrixGroups Function OnePoint Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup

p2m_open "UpperHalfPlane~I"
open scoped ModularForm

local notation "𝒢(" M ")" =>
  ((CongruenceSubgroup.Gamma M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Action

variable (N : ℕ) [NeZero N] {k : ℤ}

def slashV (γ : SL(2, ℤ)) (G : CuspForm 𝒢(N) k) : CuspForm 𝒢(N) k where
  toFun := (⇑G : ℍ → ℂ) ∣[k] γ
  slash_action_eq' A hA := by
    obtain ⟨δ, hδ, rfl⟩ := hA
    have hδ' : γ * δ * γ⁻¹ ∈ CongruenceSubgroup.Gamma N := (Gamma_normal N).conj_mem δ hδ γ
    have h1 : (⇑G : ℍ → ℂ) ∣[k] (γ * δ * γ⁻¹) = ⇑G :=
      SlashInvariantFormClass.slash_action_eq G _ (Subgroup.mem_map_of_mem _ hδ')
    calc ((⇑G : ℍ → ℂ) ∣[k] γ) ∣[k] mapGL ℝ δ
        = ((⇑G : ℍ → ℂ) ∣[k] γ) ∣[k] δ := rfl
      _ = (⇑G : ℍ → ℂ) ∣[k] (γ * δ) := by rw [SlashAction.slash_mul]
      _ = (⇑G : ℍ → ℂ) ∣[k] ((γ * δ * γ⁻¹) * γ) := by group
      _ = ((⇑G : ℍ → ℂ) ∣[k] (γ * δ * γ⁻¹)) ∣[k] γ := by rw [SlashAction.slash_mul]
      _ = (⇑G : ℍ → ℂ) ∣[k] γ := by rw [h1]
  holo' := (CuspFormClass.holo G).slash k _
  zero_at_cusps' {c} hc := by
    change IsZeroAt c ((⇑G : ℍ → ℂ) ∣[k] (mapGL ℝ γ)) k
    refine OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps G ?_)
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
    exact hc.smul_of_mem ⟨γ, rfl⟩

lemma coe_slashV (γ : SL(2, ℤ)) (G : CuspForm 𝒢(N) k) :
    ⇑(slashV N γ G) = (⇑G : ℍ → ℂ) ∣[k] γ := rfl

lemma slashV_apply_coe (γ : SL(2, ℤ)) (G : CuspForm 𝒢(N) k) (τ : ℍ) :
    slashV N γ G τ = ((⇑G : ℍ → ℂ) ∣[k] γ) τ := rfl

lemma slashV_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma N)
    (G : CuspForm 𝒢(N) k) : slashV N γ G = G :=
  CuspForm.ext fun τ => by
    rw [slashV_apply_coe]
    exact congrFun (SlashInvariantFormClass.slash_action_eq G (mapGL ℝ γ)
      (Subgroup.mem_map_of_mem _ hγ)) τ

lemma slashV_mul (γ δ : SL(2, ℤ)) (G : CuspForm 𝒢(N) k) :
    slashV N (γ * δ) G = slashV N δ (slashV N γ G) :=
  CuspForm.ext fun τ => by
    show ((⇑G : ℍ → ℂ) ∣[k] (γ * δ)) τ = (((⇑G : ℍ → ℂ) ∣[k] γ) ∣[k] δ) τ
    rw [SlashAction.slash_mul]

lemma slashV_one (G : CuspForm 𝒢(N) k) : slashV N (1 : SL(2, ℤ)) G = G :=
  CuspForm.ext fun τ => by
    show ((⇑G : ℍ → ℂ) ∣[k] (1 : SL(2, ℤ))) τ = G τ; rw [SlashAction.slash_one]

lemma slashV_inv_slashV (γ : SL(2, ℤ)) (G : CuspForm 𝒢(N) k) :
    slashV N γ⁻¹ (slashV N γ G) = G := by
  rw [← slashV_mul, mul_inv_cancel, slashV_one]

lemma slashV_slashV_inv (γ : SL(2, ℤ)) (G : CuspForm 𝒢(N) k) :
    slashV N γ (slashV N γ⁻¹ G) = G := by
  rw [← slashV_mul, inv_mul_cancel, slashV_one]

lemma slashV_add (γ : SL(2, ℤ)) (G H : CuspForm 𝒢(N) k) :
    slashV N γ (G + H) = slashV N γ G + slashV N γ H :=
  CuspForm.ext fun τ => by
    show (((⇑G + ⇑H : ℍ → ℂ)) ∣[k] γ) τ = ((⇑G : ℍ → ℂ) ∣[k] γ) τ + ((⇑H : ℍ → ℂ) ∣[k] γ) τ
    rw [SlashAction.add_slash]; rfl

lemma slashV_smul (γ : SL(2, ℤ)) (c : ℂ) (G : CuspForm 𝒢(N) k) :
    slashV N γ (c • G) = c • slashV N γ G :=
  CuspForm.ext fun τ => by
    show (((c • ⇑G : ℍ → ℂ)) ∣[k] γ) τ = c • ((⇑G : ℍ → ℂ) ∣[k] γ) τ
    rw [ModularForm.SL_smul_slash]; rfl

lemma slashV_zero (γ : SL(2, ℤ)) : slashV N γ (0 : CuspForm 𝒢(N) k) = 0 :=
  CuspForm.ext fun τ => by
    show (((⇑(0 : CuspForm 𝒢(N) k)) : ℍ → ℂ) ∣[k] γ) τ = 0
    rw [CuspForm.coe_zero, SlashAction.zero_slash]; rfl

lemma slashV_neg (γ : SL(2, ℤ)) (G : CuspForm 𝒢(N) k) : slashV N γ (-G) = -slashV N γ G := by
  have h := slashV_add N γ G (-G)
  rw [add_neg_cancel, slashV_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

lemma slashV_sub (γ : SL(2, ℤ)) (G H : CuspForm 𝒢(N) k) :
    slashV N γ (G - H) = slashV N γ G - slashV N γ H := by
  rw [sub_eq_add_neg, slashV_add, slashV_neg, ← sub_eq_add_neg]

lemma slashV_sum (γ : SL(2, ℤ)) {ι : Type*} (s : Finset ι) (G : ι → CuspForm 𝒢(N) k) :
    slashV N γ (∑ i ∈ s, G i) = ∑ i ∈ s, slashV N γ (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, slashV_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, slashV_add, ih]

end Action

section Average

variable (N M : ℕ) [NeZero N] {k : ℤ}

scoped instance instNormalGamma (n : ℕ) : (CongruenceSubgroup.Gamma n).Normal := Gamma_normal n

abbrev Q (N M : ℕ) := CongruenceSubgroup.Gamma M ⧸
  (CongruenceSubgroup.Gamma N).subgroupOf (CongruenceSubgroup.Gamma M)

scoped instance instFintypeQ : Fintype (Q N M) := Fintype.ofFinite _

def Fbar (v : CuspForm 𝒢(N) k) : Q N M → CuspForm 𝒢(N) k :=
  Quotient.lift (fun a : CongruenceSubgroup.Gamma M => slashV N a.1 v) (by
    intro a b hab
    have hab' : (a⁻¹ * b : CongruenceSubgroup.Gamma M) ∈
        (CongruenceSubgroup.Gamma N).subgroupOf (CongruenceSubgroup.Gamma M) :=
      QuotientGroup.leftRel_apply.mp hab
    rw [Subgroup.mem_subgroupOf] at hab'
    show slashV N a.1 v = slashV N b.1 v
    have : b.1 = a.1 * (a⁻¹ * b).1 := by simp
    rw [this, slashV_mul, slashV_of_mem N hab'])

lemma Fbar_mk (v : CuspForm 𝒢(N) k) (a : CongruenceSubgroup.Gamma M) :
    Fbar N M v (QuotientGroup.mk a) = slashV N a.1 v := rfl

def E (v : CuspForm 𝒢(N) k) : CuspForm 𝒢(N) k :=
  (Fintype.card (Q N M) : ℂ)⁻¹ • ∑ q : Q N M, Fbar N M v q

lemma card_Q_ne_zero : (Fintype.card (Q N M) : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

lemma Fbar_add (v w : CuspForm 𝒢(N) k) (q : Q N M) :
    Fbar N M (v + w) q = Fbar N M v q + Fbar N M w q := by
  induction q using QuotientGroup.induction_on with
  | H a => rw [Fbar_mk, Fbar_mk, Fbar_mk, slashV_add]

lemma Fbar_smul (c : ℂ) (v : CuspForm 𝒢(N) k) (q : Q N M) :
    Fbar N M (c • v) q = c • Fbar N M v q := by
  induction q using QuotientGroup.induction_on with
  | H a => rw [Fbar_mk, Fbar_mk, slashV_smul]

lemma E_add (v w : CuspForm 𝒢(N) k) : E N M (v + w) = E N M v + E N M w := by
  simp only [E, Fbar_add, Finset.sum_add_distrib, smul_add]

lemma E_smul (c : ℂ) (v : CuspForm 𝒢(N) k) : E N M (c • v) = c • E N M v := by
  simp only [E, Fbar_smul, ← Finset.smul_sum, smul_comm c]

lemma E_neg (v : CuspForm 𝒢(N) k) : E N M (-v) = -E N M v := by
  rw [← neg_one_smul ℂ v, E_smul, neg_one_smul]

lemma E_sub (v w : CuspForm 𝒢(N) k) : E N M (v - w) = E N M v - E N M w := by
  rw [sub_eq_add_neg, E_add, E_neg, ← sub_eq_add_neg]

lemma E_sum {ι : Type*} (s : Finset ι) (v : ι → CuspForm 𝒢(N) k) :
    E N M (∑ i ∈ s, v i) = ∑ i ∈ s, E N M (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    have := E_smul N M (0 : ℂ) (0 : CuspForm 𝒢(N) k)
    rwa [zero_smul, zero_smul] at this
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, E_add, ih]

lemma slashV_E_of_mem {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma M) (v : CuspForm 𝒢(N) k) :
    slashV N γ (E N M v) = E N M v := by
  rw [E, slashV_smul, slashV_sum]
  congr 1
  set c : Q N M := QuotientGroup.mk (⟨γ, hγ⟩ : CongruenceSubgroup.Gamma M) with hc
  have key : ∀ q : Q N M, slashV N γ (Fbar N M v q) = Fbar N M v (q * c) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [hc, ← QuotientGroup.mk_mul, Fbar_mk, Fbar_mk]
      show slashV N γ (slashV N a.1 v) = slashV N (a.1 * γ) v
      rw [slashV_mul]
  simp_rw [key]
  exact Fintype.sum_equiv (Equiv.mulRight c) _ _ (fun q => rfl)

lemma E_eq_self_of_fixed (v : CuspForm 𝒢(N) k)
    (hv : ∀ γ ∈ CongruenceSubgroup.Gamma M, slashV N γ v = v) : E N M v = v := by
  rw [E]
  have : ∀ q : Q N M, Fbar N M v q = v := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a => rw [Fbar_mk]; exact hv a.1 a.2
  simp_rw [this]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (card_Q_ne_zero N M), one_smul]

lemma E_E (v : CuspForm 𝒢(N) k) : E N M (E N M v) = E N M v :=
  E_eq_self_of_fixed N M _ (fun _ hγ => slashV_E_of_mem N M hγ v)

lemma slashV_E (x : SL(2, ℤ)) (v : CuspForm 𝒢(N) k) :
    slashV N x (E N M v) = E N M (slashV N x v) := by

  let φ : CongruenceSubgroup.Gamma M → CongruenceSubgroup.Gamma M :=
    fun a => ⟨x⁻¹ * a.1 * x, by
      have := (Gamma_normal M).conj_mem a.1 a.2 x⁻¹
      simpa using this⟩
  have hφ : ∀ a b : CongruenceSubgroup.Gamma M,
      QuotientGroup.leftRel ((CongruenceSubgroup.Gamma N).subgroupOf (CongruenceSubgroup.Gamma M))
        a b →
      (QuotientGroup.mk (φ a) : Q N M) = QuotientGroup.mk (φ b) := by
    intro a b hab
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hab' := (Subgroup.mem_subgroupOf).mp (QuotientGroup.leftRel_apply.mp hab)
    have : ((φ a)⁻¹ * φ b : CongruenceSubgroup.Gamma M).1 = x⁻¹ * (a⁻¹ * b : _).1 * x⁻¹⁻¹ := by
      simp [φ, mul_assoc]
    rw [this]
    exact (Gamma_normal N).conj_mem _ hab' x⁻¹
  let ψ : Q N M → Q N M := Quotient.lift (fun a => QuotientGroup.mk (φ a)) hφ
  have hψ_mk : ∀ a, ψ (QuotientGroup.mk a) = QuotientGroup.mk (φ a) := fun a => rfl
  have hψinj : Function.Injective ψ := by
    intro q₁ q₂ h
    induction q₁ using QuotientGroup.induction_on with
    | H a =>
      induction q₂ using QuotientGroup.induction_on with
      | H b =>
        rw [hψ_mk, hψ_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at h
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have h2 : ((φ a)⁻¹ * φ b : CongruenceSubgroup.Gamma M).1 = x⁻¹ * (a⁻¹ * b : _).1 * x⁻¹⁻¹ := by
          simp [φ, mul_assoc]
        rw [h2] at h
        have := (Gamma_normal N).conj_mem _ h x
        simpa [mul_assoc] using this
  have hψbij : Function.Bijective ψ := Finite.injective_iff_bijective.mp hψinj

  rw [E, E, slashV_smul, slashV_sum]
  congr 1
  have key : ∀ q : Q N M, slashV N x (Fbar N M v q) = Fbar N M (slashV N x v) (ψ q) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      rw [hψ_mk, Fbar_mk, Fbar_mk, ← slashV_mul, ← slashV_mul]
      congr 1
      simp [φ, mul_assoc]
  simp_rw [key]
  exact hψbij.sum_comp (fun q => Fbar N M (slashV N x v) q)

lemma E_sub_self_mem (U : Submodule ℂ (CuspForm 𝒢(N) k)) (v : CuspForm 𝒢(N) k)
    (h : ∀ γ ∈ CongruenceSubgroup.Gamma M, slashV N γ v - v ∈ U) : E N M v - v ∈ U := by
  have hv : v = (Fintype.card (Q N M) : ℂ)⁻¹ • ∑ _q : Q N M, v := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
      inv_mul_cancel₀ (card_Q_ne_zero N M), one_smul]
  rw [E, hv, ← smul_sub, ← Finset.sum_sub_distrib]
  refine U.smul_mem _ (U.sum_mem fun q _ => ?_)
  rw [← hv]
  induction q using QuotientGroup.induction_on with
  | H a => rw [Fbar_mk]; exact h a.1 a.2

end Average

section Group

def gL (m : ℤ) : SL(2, ℤ) := ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹

lemma coe_gL (m : ℤ) : (gL m : Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -m, 1] := by
  rw [gL, ModularGroup.S_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow, Matrix.SpecialLinearGroup.coe_neg,
    ModularGroup.coe_S]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma gL_apply (m : ℤ) (i j : Fin 2) : (gL m) i j = !![(1 : ℤ), 0; -m, 1] i j := by
  rw [← coe_gL]

lemma gL_mem_Gamma (m : ℕ) : gL (m : ℤ) ∈ CongruenceSubgroup.Gamma m := by
  rw [Gamma_mem]; simp [gL_apply]

lemma gL_comm (m m' : ℤ) : gL m * gL m' = gL m' * gL m := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_gL, coe_gL]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]; ring

lemma comm_gL_eq_one (m m' : ℤ) : gL m * gL m' * (gL m)⁻¹ * (gL m')⁻¹ = 1 := by
  rw [gL_comm, mul_inv_cancel_right, mul_inv_cancel]

lemma conj_gL_mem_Gamma (N : ℕ) {h : SL(2, ℤ)} (hh : h ∈ Gamma1 N) (c : ℤ)
    (hbc : (N : ℤ) ∣ h 0 1 * c) : h * gL c * h⁻¹ * (gL c)⁻¹ ∈ CongruenceSubgroup.Gamma N := by
  rw [Gamma_mem']
  simp only [map_mul, map_inv]
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
  rw [Gamma1_mem] at hh
  obtain ⟨ha, hd, hc0⟩ := hh
  have hbc' : ((h 0 1 : ℤ) : ZMod N) * (c : ZMod N) = 0 := by
    rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hbc
  have hcb : (c : ZMod N) * ((h 0 1 : ℤ) : ZMod N) = 0 := by rw [mul_comm]; exact hbc'
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, SL_reduction_mod_hom_val, gL_apply, ha, hd, hc0,
      mul_neg, neg_mul, hbc', hcb]

lemma T_zpow_mem_Gamma1 (N : ℕ) (b : ℤ) : ModularGroup.T ^ b ∈ Gamma1 N := by
  rw [Gamma1_mem]; simp [ModularGroup.coe_T_zpow]

lemma T_zpow_neg_mul_mem_Gamma {M : ℕ} {m : SL(2, ℤ)} (hm : m ∈ Gamma1 M) :
    ModularGroup.T ^ (-(m 0 1)) * m ∈ CongruenceSubgroup.Gamma M := by
  rw [Gamma1_mem] at hm
  obtain ⟨ha, hd, hc⟩ := hm
  rw [Gamma_mem]
  have e : ∀ i j, (ModularGroup.T ^ (-(m 0 1)) * m) i j
      = !![m 0 0 - m 0 1 * m 1 0, m 0 1 - m 0 1 * m 1 1; m 1 0, m 1 1] i j := by
    intro i j
    show ((ModularGroup.T ^ (-(m 0 1)) * m : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) i j = _
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  simp only [e, of_apply, cons_val', cons_val_zero, cons_val_one, empty_val', cons_val_fin_one]
  push_cast
  rw [ha, hd, hc]
  exact ⟨by ring, by ring, rfl, rfl⟩

end Group

section Induction

variable (N : ℕ) [NeZero N] {k : ℤ}

abbrev g (N p : ℕ) : SL(2, ℤ) := gL ((N / p : ℕ) : ℤ)

def USub (J : Finset ℕ) : Submodule ℂ (CuspForm 𝒢(N) k) where
  carrier := {u | ∃ x : ℕ → CuspForm 𝒢(N) k,
    (∀ j ∈ J, slashV N (g N j) (x j) = x j) ∧ u = ∑ j ∈ J, x j}
  add_mem' := by
    rintro u u' ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
    refine ⟨x + x', fun j hj => ?_, ?_⟩
    · rw [Pi.add_apply, slashV_add, hx j hj, hx' j hj]
    · rw [← Finset.sum_add_distrib]; rfl
  zero_mem' := ⟨0, fun j _ => by rw [Pi.zero_apply, slashV_zero], by simp⟩
  smul_mem' := by
    rintro c u ⟨x, hx, rfl⟩
    refine ⟨c • x, fun j hj => ?_, ?_⟩
    · rw [Pi.smul_apply, slashV_smul, hx j hj]
    · rw [Finset.smul_sum]; rfl

lemma mem_USub_iff (J : Finset ℕ) (u : CuspForm 𝒢(N) k) :
    u ∈ USub N J ↔ ∃ x : ℕ → CuspForm 𝒢(N) k,
      (∀ j ∈ J, slashV N (g N j) (x j) = x j) ∧ u = ∑ j ∈ J, x j := Iff.rfl

lemma single_mem_USub (J : Finset ℕ) {j : ℕ} (hj : j ∈ J) {x : CuspForm 𝒢(N) k}
    (hx : slashV N (g N j) x = x) : x ∈ USub N J := by
  classical
  refine ⟨Function.update 0 j x, fun i hi => ?_, ?_⟩
  · by_cases h : i = j
    · subst h; rwa [Function.update_self]
    · rw [Function.update_of_ne h, Pi.zero_apply, slashV_zero]
  · rw [Finset.sum_update_of_mem hj]; simp

lemma sum_mem_USub (J : Finset ℕ) (x : ℕ → CuspForm 𝒢(N) k)
    (hx : ∀ j ∈ J, slashV N (g N j) (x j) = x j) : ∑ j ∈ J, x j ∈ USub N J := ⟨x, hx, rfl⟩

lemma slashV_mem_USub (J : Finset ℕ) (γ : SL(2, ℤ))
    (hγ : ∀ j ∈ J, γ * g N j * γ⁻¹ * (g N j)⁻¹ ∈ CongruenceSubgroup.Gamma N)
    {u : CuspForm 𝒢(N) k} (hu : u ∈ USub N J) : slashV N γ u ∈ USub N J := by
  obtain ⟨x, hx, rfl⟩ := hu
  refine ⟨fun j => slashV N γ (x j), fun j hj => ?_, by rw [slashV_sum]⟩
  have h1 : γ * g N j = (γ * g N j * γ⁻¹ * (g N j)⁻¹) * (g N j * γ) := by group
  rw [← slashV_mul, h1, slashV_mul, slashV_of_mem N (hγ j hj), slashV_mul, hx j hj]

def Sgrp (U : Submodule ℂ (CuspForm 𝒢(N) k)) (w : CuspForm 𝒢(N) k) : Subgroup SL(2, ℤ) where
  carrier := {γ | (∀ u ∈ U, slashV N γ u ∈ U ∧ slashV N γ⁻¹ u ∈ U) ∧ slashV N γ w - w ∈ U}
  one_mem' := by
    refine ⟨fun u hu => ?_, ?_⟩
    · rw [inv_one, slashV_one]; exact ⟨hu, hu⟩
    · rw [slashV_one, sub_self]; exact U.zero_mem
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun u hu => ⟨?_, ?_⟩, ?_⟩
    · rw [slashV_mul]; exact (hb _ (ha u hu).1).1
    · rw [_root_.mul_inv_rev, slashV_mul]; exact (ha _ (hb u hu).2).2
    · have : slashV N (a * b) w - w = slashV N b (slashV N a w - w) + (slashV N b w - w) := by
        rw [slashV_mul, slashV_sub]; abel
      rw [this]
      exact U.add_mem (hb _ ha').1 hb'
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨fun u hu => ⟨(ha u hu).2, by rw [inv_inv]; exact (ha u hu).1⟩, ?_⟩
    have : slashV N a⁻¹ w - w = -(slashV N a⁻¹ (slashV N a w - w)) := by
      rw [slashV_sub, slashV_inv_slashV]; abel
    rw [this]
    exact U.neg_mem (ha _ ha').2

lemma mem_Sgrp_iff (U : Submodule ℂ (CuspForm 𝒢(N) k)) (w : CuspForm 𝒢(N) k) (γ : SL(2, ℤ)) :
    γ ∈ Sgrp N U w ↔
      (∀ u ∈ U, slashV N γ u ∈ U ∧ slashV N γ⁻¹ u ∈ U) ∧ slashV N γ w - w ∈ U := Iff.rfl

lemma dvd_ordCompl {i j : ℕ} (hi : i ∈ N.primeFactors) (hj : j ∈ N.primeFactors) (hne : j ≠ i) :
    j ∣ N / i ^ N.factorization i := by
  have hip : i.Prime := Nat.prime_of_mem_primeFactors hi
  have hjp : j.Prime := Nat.prime_of_mem_primeFactors hj
  have hjN : j ∣ N := Nat.dvd_of_mem_primeFactors hj
  have h := Nat.ordProj_mul_ordCompl_eq_self N i
  rw [← h] at hjN
  exact (Nat.Coprime.pow_right _ ((Nat.coprime_primes hjp hip).mpr hne)).dvd_of_dvd_mul_left hjN

theorem induct (J : Finset ℕ) (hJ : J ⊆ N.primeFactors) :
    ∀ v : CuspForm 𝒢(N) k, (∀ h ∈ Gamma1 N, slashV N h v = v) → v ∈ USub N J →
      ∃ w : ℕ → CuspForm 𝒢(N) k,
        (∀ j ∈ J, (∀ h ∈ Gamma1 N, slashV N h (w j) = w j) ∧
          (∀ γ ∈ CongruenceSubgroup.Gamma (N / j), slashV N γ (w j) = w j)) ∧
        v = ∑ j ∈ J, w j := by
  classical
  induction J using Finset.induction_on with
  | empty =>
    intro v _ hv
    obtain ⟨x, -, rfl⟩ := hv
    exact ⟨fun _ => 0, fun j hj => (Finset.notMem_empty j hj).elim, by simp⟩
  | insert i J' hiJ ih =>
    intro v hv hvU
    have hi : i ∈ N.primeFactors := hJ (Finset.mem_insert_self i J')
    have hJ' : J' ⊆ N.primeFactors := (Finset.subset_insert i J').trans hJ
    have hip : i.Prime := Nat.prime_of_mem_primeFactors hi
    have hiN : i ∣ N := Nat.dvd_of_mem_primeFactors hi
    obtain ⟨x, hx, hvx⟩ := hvU
    rw [Finset.sum_insert hiJ] at hvx

    set Ei : CuspForm 𝒢(N) k → CuspForm 𝒢(N) k := E N (N / i) with hEi
    have hgi : g N i ∈ CongruenceSubgroup.Gamma (N / i) := gL_mem_Gamma (N / i)

    have hEv_H : ∀ h ∈ Gamma1 N, slashV N h (Ei v) = Ei v := by
      intro h hh; rw [hEi, slashV_E, hv h hh]
    have hEv_Λ : ∀ γ ∈ CongruenceSubgroup.Gamma (N / i), slashV N γ (Ei v) = Ei v :=
      fun γ hγ => slashV_E_of_mem N (N / i) hγ v
    set v'' := v - Ei v with hv''def
    have hv''H : ∀ h ∈ Gamma1 N, slashV N h v'' = v'' := by
      intro h hh; rw [hv''def, slashV_sub, hv h hh, hEv_H h hh]
    set u'' := ∑ j ∈ J', (x j - Ei (x j)) with hu''def
    have hu''U : u'' ∈ USub N J' := by
      refine sum_mem_USub N J' (fun j => x j - Ei (x j)) fun j hj => ?_
      show slashV N (g N j) (x j - Ei (x j)) = x j - Ei (x j)
      rw [slashV_sub, hEi, slashV_E, hx j (Finset.mem_insert_of_mem hj)]
    have hv''eq : v'' = (x i - Ei (x i)) + u'' := by
      rw [hv''def, hvx, hu''def, hEi, E_add, E_sum, Finset.sum_sub_distrib]; abel

    set S := Sgrp N (USub N J') v'' with hSdef
    have hH : Gamma1 N ⊓ CongruenceSubgroup.Gamma (N / i ^ N.factorization i) ≤ S := by
      intro h hh
      obtain ⟨hh1, hhM⟩ := Subgroup.mem_inf.mp hh
      have hcomm : ∀ (h' : SL(2, ℤ)), h' ∈ Gamma1 N →
          h' ∈ CongruenceSubgroup.Gamma (N / i ^ N.factorization i) →
          ∀ j ∈ J', h' * g N j * h'⁻¹ * (g N j)⁻¹ ∈ CongruenceSubgroup.Gamma N := by
        intro h' hh1' hhM' j hj
        apply conj_gL_mem_Gamma N hh1'
        have hjN : j ∈ N.primeFactors := hJ' hj
        have hjne : j ≠ i := ne_of_mem_of_not_mem hj hiJ
        have hjM : (j : ℤ) ∣ ((N / i ^ N.factorization i : ℕ) : ℤ) :=
          Int.natCast_dvd_natCast.mpr (dvd_ordCompl N hi hjN hjne)
        have hMb : ((N / i ^ N.factorization i : ℕ) : ℤ) ∣ h' 0 1 :=
          (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp ((Gamma_mem.mp hhM').2.1)
        obtain ⟨t, ht⟩ := hjM.trans hMb
        rw [ht]
        have hjdvd : j ∣ N := Nat.dvd_of_mem_primeFactors hjN
        have : (j : ℤ) * t * ((N / j : ℕ) : ℤ) = (N : ℤ) * t := by
          have e : ((N / j : ℕ) : ℤ) * j = N := by exact_mod_cast Nat.div_mul_cancel hjdvd
          linear_combination t * e
        rw [this]; exact dvd_mul_right _ _
      refine ⟨fun u hu => ⟨slashV_mem_USub N J' h (hcomm h hh1 hhM) hu,
        slashV_mem_USub N J' h⁻¹ (hcomm h⁻¹ (inv_mem hh1) (inv_mem hhM)) hu⟩, ?_⟩
      rw [hv''H h hh1, sub_self]; exact Submodule.zero_mem _
    have hgS : g N i ∈ S := by
      refine ⟨fun u hu => ⟨slashV_mem_USub N J' _ (fun j _ => ?_) hu,
        slashV_mem_USub N J' _ (fun j _ => ?_) hu⟩, ?_⟩
      · rw [comm_gL_eq_one]; exact Subgroup.one_mem _
      · have : (g N i)⁻¹ * g N j * (g N i)⁻¹⁻¹ * (g N j)⁻¹ = 1 := by
          rw [inv_inv]
          have := gL_comm ((N / i : ℕ) : ℤ) ((N / j : ℕ) : ℤ)
          calc (g N i)⁻¹ * g N j * g N i * (g N j)⁻¹
              = (g N i)⁻¹ * (g N j * g N i) * (g N j)⁻¹ := by group
            _ = (g N i)⁻¹ * (g N i * g N j) * (g N j)⁻¹ := by rw [this]
            _ = 1 := by group
        rw [this]; exact Subgroup.one_mem _
      · have h1 : slashV N (g N i) (x i - Ei (x i)) = x i - Ei (x i) := by
          rw [slashV_sub, hx i (Finset.mem_insert_self i J'), hEi, slashV_E_of_mem N (N / i) hgi]
        have h2 : slashV N (g N i) u'' ∈ USub N J' :=
          slashV_mem_USub N J' _ (fun j _ => by rw [comm_gL_eq_one]; exact Subgroup.one_mem _) hu''U
        have : slashV N (g N i) v'' - v'' = slashV N (g N i) u'' - u'' := by
          rw [hv''eq, slashV_add, h1]; abel
        rw [this]
        exact Submodule.sub_mem _ h2 hu''U

    have hΛS : CongruenceSubgroup.Gamma (N / i) ≤ S := by
      refine (CongruenceSubgroup.Gamma_div_le_gamma1_inf_Gamma_sup_zpowers N i hip hiN).trans ?_
      refine sup_le hH ?_
      rw [Subgroup.zpowers_le]
      exact hgS
    have hdiff : ∀ γ ∈ CongruenceSubgroup.Gamma (N / i), slashV N γ v'' - v'' ∈ USub N J' :=
      fun γ hγ => ((mem_Sgrp_iff N _ _ γ).mp (hΛS hγ)).2
    have hE1 : Ei v'' - v'' ∈ USub N J' := by
      rw [hEi]; exact E_sub_self_mem N (N / i) (USub N J') v'' hdiff
    have hE0 : Ei v'' = 0 := by
      rw [hv''def, hEi, E_sub, E_E, sub_self]
    have hv''U : v'' ∈ USub N J' := by
      rw [hE0, zero_sub] at hE1
      have := Submodule.neg_mem _ hE1
      rwa [neg_neg] at this

    obtain ⟨w', hw', hv''w⟩ := ih hJ' v'' hv''H hv''U
    refine ⟨Function.update w' i (Ei v), fun j hj => ?_, ?_⟩
    · rcases Finset.mem_insert.mp hj with rfl | hj'
      · rw [Function.update_self]; exact ⟨hEv_H, hEv_Λ⟩
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hj' hiJ)]; exact hw' j hj'
    · rw [Finset.sum_insert hiJ, Function.update_self]
      have : ∑ j ∈ J', Function.update w' i (Ei v) j = ∑ j ∈ J', w' j :=
        Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hiJ)]
      rw [this, ← hv''w, hv''def]; abel

lemma slashV_eq_of_gamma1_of_Gamma {p : ℕ} (w : CuspForm 𝒢(N) k)
    (hH : ∀ h ∈ Gamma1 N, slashV N h w = w)
    (hΛ : ∀ γ ∈ CongruenceSubgroup.Gamma (N / p), slashV N γ w = w)
    {m : SL(2, ℤ)} (hm : m ∈ Gamma1 (N / p)) : slashV N m w = w := by
  have h1 : m = ModularGroup.T ^ (m 0 1) * (ModularGroup.T ^ (-(m 0 1)) * m) := by
    rw [← mul_assoc, ← _root_.zpow_add, add_neg_cancel, zpow_zero, one_mul]
  rw [h1, slashV_mul, hH _ (T_zpow_mem_Gamma1 N _), hΛ _ (T_zpow_neg_mul_mem_Gamma hm)]

lemma coe_finset_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {ι : Type*} (s : Finset ι)
    (F : ι → CuspForm Γ k) : ⇑(∑ i ∈ s, F i) = ∑ i ∈ s, ⇑(F i) :=
  map_sum (FunLike.coeAddMonoidHom (CuspForm Γ k) UpperHalfPlane ℂ) F s

theorem main (F : ℕ → CuspForm 𝒢(N) k)
    (hF : ∀ p ∈ N.primeFactors,
      (⇑(F p) : ℍ → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹) = ⇑(F p))
    (hsum : ∀ γ ∈ Gamma1 N,
      (⇑(∑ p ∈ N.primeFactors, F p) : ℍ → ℂ) ∣[k] γ = ⇑(∑ p ∈ N.primeFactors, F p)) :
    ∃ G : ℕ → CuspForm 𝒢(N) k,
      (∀ p ∈ N.primeFactors, ∀ γ ∈ Gamma1 (N / p), (⇑(G p) : ℍ → ℂ) ∣[k] γ = ⇑(G p)) ∧
      ∑ p ∈ N.primeFactors, G p = ∑ p ∈ N.primeFactors, F p := by
  set v := ∑ p ∈ N.primeFactors, F p with hvdef
  have hv : ∀ h ∈ Gamma1 N, slashV N h v = v := fun h hh => CuspForm.ext fun τ => by
    rw [slashV_apply_coe]; exact congrFun (hsum h hh) τ
  have hvU : v ∈ USub N N.primeFactors :=
    sum_mem_USub N _ F fun p hp => CuspForm.ext fun τ => by
      rw [slashV_apply_coe]; exact congrFun (hF p hp) τ
  obtain ⟨w, hw, hvw⟩ := induct N N.primeFactors subset_rfl v hv hvU
  refine ⟨w, fun p hp γ hγ => ?_, hvw.symm⟩
  have := slashV_eq_of_gamma1_of_Gamma N (w p) (hw p hp).1 (hw p hp).2 hγ
  exact congrArg (fun G : CuspForm 𝒢(N) k => (⇑G : ℍ → ℂ)) this

end Induction

end DS575Sol
p2m_reactivate "P2MW.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq.DS575Sol"

end
p2m_reactivate "P2MW.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq.DS575Sol"

open CongruenceSubgroup in
open scoped MatrixGroups ModularForm in
theorem solution
    (N : ℕ) [NeZero N] (k : ℤ) (F : ℕ → CuspForm (Gamma N) k)
    (hF : ∀ p ∈ N.primeFactors,
      (⇑(F p) : UpperHalfPlane → ℂ) ∣[k]
        (ModularGroup.S * ModularGroup.T ^ ((N / p : ℕ) : ℤ) * ModularGroup.S⁻¹) = ⇑(F p))
    (hsum : ∀ γ ∈ Gamma1 N,
      (⇑(∑ p ∈ N.primeFactors, F p) : UpperHalfPlane → ℂ) ∣[k] γ =
        ⇑(∑ p ∈ N.primeFactors, F p)) :
    ∃ G : ℕ → CuspForm (Gamma N) k,
      (∀ p ∈ N.primeFactors, ∀ γ ∈ Gamma1 (N / p),
        (⇑(G p) : UpperHalfPlane → ℂ) ∣[k] γ = ⇑(G p)) ∧
      ∑ p ∈ N.primeFactors, G p = ∑ p ∈ N.primeFactors, F p :=
  DS575Sol.main N F hF hsum

end S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq
end P2MW
export P2MW.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq (solution)
