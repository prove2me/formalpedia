-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isODHom_map_iterateFrobenius_comp_X_pow_eq_act_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/248e20e0-e248-5957-bab7-38342fb2bed3

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvFormalGroup_coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP
import Theorems.Thm_CerednikDrinfeld_FormalODModule_HasKernelOfDegree_comp_map_of_field
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_map_iterateFrobenius_comp_X_pow_eq_act_pow
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

universe u

namespace R4Versch

open MvPowerSeries (subst HasSubst hasSubst_of_constantCoeff_zero constantCoeff coeff subst_X coe_substAlgHom)
open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

variable {B : Type u} [CommRing B]

local notation "S" => MvPowerSeries (Fin 2) B
local notation "Deg" => (Fin 2 →₀ ℕ)

def xq (B : Type u) [CommRing B] (q : ℕ) : Series B :=
  fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q

theorem xq_def (q : ℕ) : xq B q = fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q := rfl

theorem constantCoeff_xq {q : ℕ} (hq : q ≠ 0) (i : Fin 2) : constantCoeff (xq B q i) = 0 := by
  rw [xq, map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]

theorem hasSubst_xq {q : ℕ} (hq : q ≠ 0) : HasSubst (xq B q) := hasSubst_of_constantCoeff_zero (constantCoeff_xq hq)

theorem prod_xq_pow {q : ℕ} (hq : q ≠ 0) (d : Deg) : (d.prod fun s n => xq B q s ^ n) = MvPowerSeries.monomial (q • d) (1 : B) := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have h : ∀ i : Fin 2, xq B q i ^ d i = MvPowerSeries.monomial (Finsupp.single i ((q • d) i)) (1 : B) := by
    intro i
    rw [xq, ← pow_mul, MvPowerSeries.X_pow_eq, Finsupp.smul_apply, smul_eq_mul]
  simp_rw [h]
  rw [MvPowerSeries.prod_monomial, Finset.prod_const_one, Finsupp.univ_sum_single]

theorem smul_deg_injective {q : ℕ} (hq : q ≠ 0) {d d' : Deg} (h : q • d = q • d') : d = d' := by
  ext i
  have := DFunLike.congr_fun h i
  simp only [Finsupp.smul_apply, smul_eq_mul] at this
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) this

theorem le_smul_self {q : ℕ} (hq : q ≠ 0) (d : Deg) : d ≤ q • d := by
  intro i
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hq)

def theta {q : ℕ} (h : S) : S := subst (xq B q) h

theorem theta_def {q : ℕ} (h : S) : theta (q := q) h = subst (xq B q) h := rfl

theorem coeff_theta {q : ℕ} (hq : q ≠ 0) (h : S) (n : Deg) :
    coeff n (theta (q := q) h) = ∑ d ∈ Finset.Iic n, if n = q • d then coeff d h else 0 := by
  classical
  rw [theta, MvPowerSeries.coeff_subst (hasSubst_xq hq)]
  have hh : ∀ d : Deg,
      coeff d h • coeff n (d.prod fun s m => xq B q s ^ m) = if n = q • d then coeff d h else 0 := by
    intro d
    rw [prod_xq_pow hq, MvPowerSeries.coeff_monomial]
    by_cases hd : n = q • d
    · rw [if_pos hd, if_pos hd, smul_eq_mul, mul_one]
    · rw [if_neg hd, if_neg hd, smul_zero]
  simp_rw [hh]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  rw [Function.mem_support] at hd
  have hnd : n = q • d := by by_contra h'; exact hd (if_neg h')
  rw [Finset.mem_coe, Finset.mem_Iic, hnd]
  exact le_smul_self hq d

theorem theta_monomial {q : ℕ} (hq : q ≠ 0) (d : Deg) (c : B) :
    theta (q := q) (MvPowerSeries.monomial d c) = MvPowerSeries.monomial (q • d) c := by
  classical
  ext n
  rw [coeff_theta hq, MvPowerSeries.coeff_monomial]
  simp_rw [MvPowerSeries.coeff_monomial]
  by_cases hn : n = q • d
  · rw [if_pos hn, Finset.sum_eq_single d]
    · rw [if_pos hn, if_pos rfl]
    · intro d' _ hd'
      by_cases h1 : n = q • d'
      · exact absurd (smul_deg_injective hq (hn.symm.trans h1)).symm hd'
      · rw [if_neg h1]
    · intro hd
      exfalso; apply hd
      rw [Finset.mem_Iic, hn]; exact le_smul_self hq d
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro d' _
    by_cases h1 : n = q • d'
    · rw [if_pos h1, if_neg]
      rintro rfl; exact hn h1
    · rw [if_neg h1]

theorem theta_add {q : ℕ} (hq : q ≠ 0) (h h' : S) : theta (q := q) (h + h') = theta (q := q) h + theta (q := q) h' := by
  rw [theta, theta, theta, ← coe_substAlgHom (hasSubst_xq hq), map_add]

theorem theta_mul {q : ℕ} (hq : q ≠ 0) (h h' : S) : theta (q := q) (h * h') = theta (q := q) h * theta (q := q) h' := by
  rw [theta, theta, theta, ← coe_substAlgHom (hasSubst_xq hq), map_mul]

theorem theta_sum {q : ℕ} (hq : q ≠ 0) {ι : Type*} (s : Finset ι) (h : ι → S) :
    theta (q := q) (∑ i ∈ s, h i) = ∑ i ∈ s, theta (q := q) (h i) := by
  simp only [theta_def]
  rw [← coe_substAlgHom (hasSubst_xq hq), map_sum]

theorem comp_xq {q : ℕ} (φ : Series B) : φ.comp (xq B q) = fun i => theta (q := q) (φ i) := rfl

abbrev Idx (q : ℕ) : Type := Fin 2 → Fin q

def emb {q : ℕ} (α : Idx q) (m : Deg) : Deg :=
  Finsupp.equivFunOnFinite.symm fun i => (α i : ℕ) + q * m i

@[scoped simp] theorem emb_apply {q : ℕ} (α : Idx q) (m : Deg) (i : Fin 2) : emb α m i = (α i : ℕ) + q * m i := rfl

def resIdx {q : ℕ} (hq : q ≠ 0) (n : Deg) : Idx q := fun i => ⟨n i % q, Nat.mod_lt _ (Nat.pos_of_ne_zero hq)⟩

def quo (q : ℕ) (n : Deg) : Deg := Finsupp.equivFunOnFinite.symm fun i => n i / q

@[scoped simp] theorem quo_apply (q : ℕ) (n : Deg) (i : Fin 2) : quo q n i = n i / q := rfl

@[scoped simp] theorem resIdx_apply {q : ℕ} (hq : q ≠ 0) (n : Deg) (i : Fin 2) : ((resIdx hq n i : Fin q) : ℕ) = n i % q := rfl

theorem emb_resIdx_quo {q : ℕ} (hq : q ≠ 0) (n : Deg) : emb (resIdx hq n) (quo q n) = n := by
  ext i; simp only [emb_apply, resIdx_apply, quo_apply]; exact Nat.mod_add_div (n i) q

theorem resIdx_emb {q : ℕ} (hq : q ≠ 0) (α : Idx q) (m : Deg) : resIdx hq (emb α m) = α := by
  funext i; apply Fin.ext
  simp only [resIdx_apply, emb_apply]
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (α i).isLt]

theorem quo_emb {q : ℕ} (hq : q ≠ 0) (α : Idx q) (m : Deg) : quo q (emb α m) = m := by
  ext i
  simp only [quo_apply, emb_apply]
  rw [Nat.add_mul_div_left _ _ (Nat.pos_of_ne_zero hq), Nat.div_eq_of_lt (α i).isLt, zero_add]

theorem emb_injective {q : ℕ} (hq : q ≠ 0) {α α' : Idx q} {m m' : Deg} (h : emb α m = emb α' m') : α = α' ∧ m = m' := by
  constructor
  · rw [← resIdx_emb hq α m, h, resIdx_emb hq]
  · rw [← quo_emb hq α m, h, quo_emb hq]

def decim {q : ℕ} (hq : q ≠ 0) : S ≃ₗ[B] (Idx q → S) where
  toFun f α := fun m => f (emb α m)
  invFun g := fun n => g (resIdx hq n) (quo q n)
  map_add' f f' := by funext α; rfl
  map_smul' c f := by funext α; rfl
  left_inv f := by
    funext n
    show f (emb (resIdx hq n) (quo q n)) = f n
    rw [emb_resIdx_quo]
  right_inv g := by
    funext α m
    show g (resIdx hq (emb α m)) (quo q (emb α m)) = g α m
    rw [resIdx_emb, quo_emb hq]

theorem coeff_decim {q : ℕ} (hq : q ≠ 0) (f : S) (α : Idx q) (m : Deg) : coeff m (decim hq f α) = coeff (emb α m) f := rfl

theorem smul_le_emb_iff {q : ℕ} (hq : q ≠ 0) (α : Idx q) (d m : Deg) : q • d ≤ emb α m ↔ d ≤ m := by
  constructor
  · intro h i
    have hi := h i
    simp only [Finsupp.smul_apply, smul_eq_mul, emb_apply] at hi
    by_contra hlt
    push Not at hlt
    have : q * (m i + 1) ≤ q * d i := Nat.mul_le_mul_left _ hlt
    have hα := (α i).isLt
    nlinarith
  · intro h i
    simp only [Finsupp.smul_apply, smul_eq_mul, emb_apply]
    exact (Nat.mul_le_mul_left q (h i)).trans (Nat.le_add_left _ _)

theorem emb_sub_smul {q : ℕ} (hq : q ≠ 0) (α : Idx q) {d m : Deg} (h : d ≤ m) : emb α m - q • d = emb α (m - d) := by
  ext i
  simp only [Finsupp.coe_tsub, Pi.sub_apply, emb_apply, Finsupp.smul_apply, smul_eq_mul]
  have hle : q * d i ≤ q * m i := Nat.mul_le_mul_left q (h i)
  rw [Nat.mul_sub]
  omega

theorem decim_theta_monomial_mul {q : ℕ} (hq : q ≠ 0) (d : Deg) (c : B) (f : S) (α : Idx q) :
    decim hq (theta (q := q) (MvPowerSeries.monomial d c) * f) α = MvPowerSeries.monomial d c * decim hq f α := by
  ext m
  rw [coeff_decim, theta_monomial hq, MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul]
  by_cases hdm : d ≤ m
  · rw [if_pos ((smul_le_emb_iff hq α d m).2 hdm), if_pos hdm, emb_sub_smul hq α hdm, coeff_decim]
  · rw [if_neg (fun h => hdm ((smul_le_emb_iff hq α d m).1 h)), if_neg hdm]

theorem coeff_decim_theta_mul_eq_zero {q : ℕ} (hq : q ≠ 0) (h f : S) (α : Idx q) (m : Deg) (hh : ∀ d, d ≤ m → coeff d h = 0) :
    coeff m (decim hq (theta (q := q) h * f) α) = 0 ∧ coeff m (h * decim hq f α) = 0 := by
  classical
  constructor
  · rw [coeff_decim, MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    have hx1 : x.1 ≤ emb α m := by rw [← hx]; exact le_self_add
    rw [coeff_theta hq]
    rw [Finset.sum_eq_zero, zero_mul]
    intro d hd
    by_cases h1 : x.1 = q • d
    · rw [if_pos h1]
      apply hh
      rw [← smul_le_emb_iff hq α, ← h1]; exact hx1
    · rw [if_neg h1]
  · rw [MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [hh x.1 (by rw [← hx]; exact le_self_add), zero_mul]

theorem decim_theta_mul {q : ℕ} (hq : q ≠ 0) (h f : S) (α : Idx q) :
    decim hq (theta (q := q) h * f) α = h * decim hq f α := by
  classical
  ext m

  set P : S := ∑ d ∈ Finset.Iic m, MvPowerSeries.monomial d (coeff d h) with hP
  set g : S := h - P with hg
  have hgcoeff : ∀ a, a ≤ m → coeff a g = 0 := by
    intro a ha
    rw [hg, map_sub, hP, map_sum]
    simp_rw [MvPowerSeries.coeff_monomial]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_Iic.2 ha), sub_self]
  have hf : h = P + g := by rw [hg]; abel
  obtain ⟨hz1, hz2⟩ := coeff_decim_theta_mul_eq_zero hq g f α m hgcoeff
  have hPeq : decim hq (theta (q := q) P * f) α = P * decim hq f α := by
    rw [hP, theta_sum hq, Finset.sum_mul, map_sum, Finset.sum_mul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun d _ => ?_
    exact decim_theta_monomial_mul hq d _ f α
  conv_lhs => rw [hf, theta_add hq, add_mul, map_add, Pi.add_apply, map_add, hPeq, hz1, add_zero]
  conv_rhs => rw [hf, add_mul, map_add, hz2, add_zero]

abbrev I (φ : Series B) : Submodule B S := (Ideal.span (Set.range φ)).restrictScalars B

abbrev J (q : ℕ) (φ : Series B) : Submodule B S := (Ideal.span (Set.range (φ.comp (xq B q)))).restrictScalars B

theorem decim_mem_pi_of_mem {q : ℕ} (hq : q ≠ 0) (φ : Series B) (f : S)
    (hf : f ∈ Ideal.span (Set.range (φ.comp (xq B q)))) :
    decim hq f ∈ Submodule.pi Set.univ (fun _ : Idx q => I φ) := by
  rw [Ideal.mem_span_range_iff_exists_fun] at hf
  obtain ⟨c, rfl⟩ := hf
  rw [Submodule.mem_pi]
  intro α _
  rw [map_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun i _ => ?_
  show decim hq (c i * theta (q := q) (φ i)) α ∈ Ideal.span (Set.range φ)
  rw [mul_comm, decim_theta_mul hq]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem symm_mem_of_mem_pi {q : ℕ} (hq : q ≠ 0) (φ : Series B) (g : Idx q → S)
    (hg : g ∈ Submodule.pi Set.univ (fun _ : Idx q => I φ)) :
    (decim hq).symm g ∈ Ideal.span (Set.range (φ.comp (xq B q))) := by
  classical

  have hdec : g = ∑ α : Idx q, Pi.single α (g α) := by
    rw [Finset.univ_sum_single]
  rw [hdec, map_sum]
  refine Ideal.sum_mem _ fun α _ => ?_
  have hα : g α ∈ Ideal.span (Set.range φ) := (Submodule.mem_pi.1 hg) α (Set.mem_univ _)
  rw [Ideal.mem_span_range_iff_exists_fun] at hα
  obtain ⟨c, hc⟩ := hα
  rw [← hc]
  have hsingle : (Pi.single α (∑ i, c i * φ i) : Idx q → S) = ∑ i, Pi.single α (c i * φ i) :=
    map_sum (AddMonoidHom.single (fun _ : Idx q => S) α) _ _
  rw [hsingle, map_sum]
  refine Ideal.sum_mem _ fun i _ => ?_

  have key : (decim hq).symm (Pi.single α (c i * φ i)) =
      theta (q := q) (φ i) * (decim hq).symm (Pi.single α (c i)) := by
    apply (decim hq).injective
    rw [LinearEquiv.apply_symm_apply]
    funext β
    rw [decim_theta_mul hq, LinearEquiv.apply_symm_apply]
    by_cases hβ : β = α
    · subst hβ; simp [mul_comm]
    · simp [Pi.single_eq_of_ne hβ]
  rw [key]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem map_decim_J {q : ℕ} (hq : q ≠ 0) (φ : Series B) :
    Submodule.map ((decim hq : S ≃ₗ[B] (Idx q → S)) : S →ₗ[B] (Idx q → S)) (J q φ) =
    Submodule.pi Set.univ (fun _ : Idx q => I φ) := by
  apply le_antisymm
  · rintro _ ⟨f, hf, rfl⟩
    exact decim_mem_pi_of_mem hq φ f hf
  · intro g hg
    refine ⟨(decim hq).symm g, symm_mem_of_mem_pi hq φ g hg, ?_⟩
    simp

def kerEquiv {q : ℕ} (hq : q ≠ 0) (φ : Series B) :
    FormalODModule.KerAlgebra (φ.comp (xq B q)) ≃ₗ[B] (Idx q → FormalODModule.KerAlgebra φ) := by
  classical
  refine (Submodule.Quotient.restrictScalarsEquiv B (Ideal.span (Set.range (φ.comp (xq B q))))).symm ≪≫ₗ ?_
  refine Submodule.Quotient.equiv (J q φ) (Submodule.pi Set.univ (fun _ : Idx q => I φ)) (decim hq) (map_decim_J hq φ) ≪≫ₗ ?_
  refine Submodule.quotientPi (fun _ : Idx q => I φ) ≪≫ₗ ?_
  exact LinearEquiv.piCongrRight fun _ => Submodule.Quotient.restrictScalarsEquiv B (Ideal.span (Set.range φ))

theorem map_comp_xq {q : ℕ} (φ : Series B) {B' : Type u} [CommRing B'] (f : B →+* B') (hq : q ≠ 0) :
    (φ.comp (xq B q)).map f = (φ.map f).comp (xq B' q) := by
  rw [Series.map_comp f _ _ (constantCoeff_xq hq)]
  congr 1
  funext i
  show MvPowerSeries.map f ((MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ q) = _
  rw [map_pow, MvPowerSeries.map_X]; rfl

section Generic

variable {σ : Type} [Fintype σ] [DecidableEq σ]

def xqG (σ : Type) (B : Type u) [CommRing B] (q : ℕ) : σ → MvPowerSeries σ B :=
  fun s => (MvPowerSeries.X s : MvPowerSeries σ B) ^ q

theorem constantCoeff_xqG {q : ℕ} (hq : q ≠ 0) (s : σ) : constantCoeff (xqG σ B q s) = 0 := by
  rw [xqG, map_pow, MvPowerSeries.constantCoeff_X, zero_pow hq]

theorem hasSubst_xqG {q : ℕ} (hq : q ≠ 0) : HasSubst (xqG σ B q) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_xqG hq)

theorem prod_xqG_pow {q : ℕ} (hq : q ≠ 0) (d : σ →₀ ℕ) :
    (d.prod fun s n => xqG σ B q s ^ n) = MvPowerSeries.monomial (q • d) (1 : B) := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  have h : ∀ i : σ, xqG σ B q i ^ d i = MvPowerSeries.monomial (Finsupp.single i ((q • d) i)) (1 : B) := by
    intro i
    rw [xqG, ← pow_mul, MvPowerSeries.X_pow_eq, Finsupp.smul_apply, smul_eq_mul]
  simp_rw [h]
  rw [MvPowerSeries.prod_monomial, Finset.prod_const_one, Finsupp.univ_sum_single]

theorem smul_degG_injective {q : ℕ} (hq : q ≠ 0) {d d' : σ →₀ ℕ} (h : q • d = q • d') : d = d' := by
  ext i
  have := DFunLike.congr_fun h i
  simp only [Finsupp.smul_apply, smul_eq_mul] at this
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hq) this

theorem le_smul_selfG {q : ℕ} (hq : q ≠ 0) (d : σ →₀ ℕ) : d ≤ q • d := by
  intro i
  rw [Finsupp.smul_apply, smul_eq_mul]
  exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero hq)

def thetaG (q : ℕ) (h : MvPowerSeries σ B) : MvPowerSeries σ B := subst (xqG σ B q) h

theorem coeff_thetaG {q : ℕ} (hq : q ≠ 0) (h : MvPowerSeries σ B) (n : σ →₀ ℕ) :
    coeff n (thetaG q h) = ∑ d ∈ Finset.Iic n, if n = q • d then coeff d h else 0 := by
  classical
  rw [thetaG, MvPowerSeries.coeff_subst (hasSubst_xqG hq)]
  have hh : ∀ d : σ →₀ ℕ,
      coeff d h • coeff n (d.prod fun s m => xqG σ B q s ^ m) = if n = q • d then coeff d h else 0 := by
    intro d
    rw [prod_xqG_pow hq, MvPowerSeries.coeff_monomial]
    by_cases hd : n = q • d
    · rw [if_pos hd, if_pos hd, smul_eq_mul, mul_one]
    · rw [if_neg hd, if_neg hd, smul_zero]
  simp_rw [hh]
  apply finsum_eq_sum_of_support_subset
  intro d hd
  rw [Function.mem_support] at hd
  have hnd : n = q • d := by by_contra h'; exact hd (if_neg h')
  rw [Finset.mem_coe, Finset.mem_Iic, hnd]
  exact le_smul_selfG hq d

theorem coeff_smul_thetaG {q : ℕ} (hq : q ≠ 0) (h : MvPowerSeries σ B) (d : σ →₀ ℕ) :
    coeff (q • d) (thetaG q h) = coeff d h := by
  classical
  rw [coeff_thetaG hq, Finset.sum_eq_single d]
  · rw [if_pos rfl]
  · intro d' _ hd'
    rw [if_neg]
    intro h1
    exact hd' (smul_degG_injective hq h1).symm
  · intro hd
    exfalso; apply hd
    rw [Finset.mem_Iic]; exact le_smul_selfG hq d

theorem thetaG_injective {q : ℕ} (hq : q ≠ 0) : Function.Injective (thetaG (σ := σ) (B := B) q) := by
  intro h h' e
  ext d
  rw [← coeff_smul_thetaG hq h d, ← coeff_smul_thetaG hq h' d, e]

theorem thetaG_monomial {q : ℕ} (hq : q ≠ 0) (d : σ →₀ ℕ) (c : B) :
    thetaG q (MvPowerSeries.monomial d c) = MvPowerSeries.monomial (q • d) c := by
  classical
  ext n
  rw [coeff_thetaG hq, MvPowerSeries.coeff_monomial]
  simp_rw [MvPowerSeries.coeff_monomial]
  by_cases hn : n = q • d
  · rw [if_pos hn, Finset.sum_eq_single d]
    · rw [if_pos hn, if_pos rfl]
    · intro d' _ hd'
      by_cases h1 : n = q • d'
      · exact absurd (smul_degG_injective hq (hn.symm.trans h1)).symm hd'
      · rw [if_neg h1]
    · intro hd
      exfalso; apply hd
      rw [Finset.mem_Iic, hn]; exact le_smul_selfG hq d
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro d' _
    by_cases h1 : n = q • d'
    · rw [if_pos h1, if_neg]
      rintro rfl; exact hn h1
    · rw [if_neg h1]

theorem coeff_thetaG_eq_zero {q : ℕ} (hq : q ≠ 0) (g : MvPowerSeries σ B) (n : σ →₀ ℕ)
    (hg : ∀ d, d ≤ n → coeff d g = 0) : coeff n (thetaG q g) = 0 := by
  classical
  rw [coeff_thetaG hq]
  apply Finset.sum_eq_zero
  intro d hd
  by_cases h1 : n = q • d
  · rw [if_pos h1]
    exact hg d ((le_smul_selfG hq d).trans (le_of_eq h1.symm))
  · rw [if_neg h1]

end Generic

section FrobComm

variable (p : ℕ) [Fact p.Prime] {κ : Type u} [Field κ] [CharP κ p]
variable {σ : Type} [Fintype σ] [DecidableEq σ]

scoped instance charP_mvPowerSeries : CharP (MvPowerSeries σ κ) p :=
  charP_of_injective_ringHom (MvPowerSeries.C_injective (σ := σ) (R := κ)) p

theorem coeff_pow_eq_zero_of_low (g : MvPowerSeries σ κ) (n : σ →₀ ℕ)
    (hg : ∀ d, d ≤ n → coeff d g = 0) {N : ℕ} (hN : N ≠ 0) : coeff n (g ^ N) = 0 := by
  classical
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  rw [pow_succ, MvPowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [hg x.2 (by rw [← hx]; exact le_add_self), mul_zero]

theorem thetaG_add {q : ℕ} (hq : q ≠ 0) (a b : MvPowerSeries σ κ) :
    thetaG q (a + b) = thetaG q a + thetaG q b := by
  unfold thetaG
  rw [← coe_substAlgHom (hasSubst_xqG hq), map_add]

theorem thetaG_sum {q : ℕ} (hq : q ≠ 0) {ι : Type*} (s : Finset ι) (h : ι → MvPowerSeries σ κ) :
    thetaG q (∑ i ∈ s, h i) = ∑ i ∈ s, thetaG q (h i) := by
  unfold thetaG
  rw [← coe_substAlgHom (hasSubst_xqG hq), map_sum]

theorem pow_eq_thetaG_map (m : ℕ) (f : MvPowerSeries σ κ) :
    f ^ (p ^ m) = thetaG (p ^ m) (MvPowerSeries.map (iterateFrobenius κ p m) f) := by
  classical
  have hq : p ^ m ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  ext n

  set P : MvPowerSeries σ κ := ∑ d ∈ Finset.Iic n, MvPowerSeries.monomial d (coeff d f) with hP
  set g : MvPowerSeries σ κ := f - P with hg
  have hgcoeff : ∀ a, a ≤ n → coeff a g = 0 := by
    intro a ha
    rw [hg, map_sub, hP, map_sum]
    simp_rw [MvPowerSeries.coeff_monomial]
    rw [Finset.sum_ite_eq, if_pos (Finset.mem_Iic.2 ha), sub_self]
  have hf : f = P + g := by rw [hg]; abel
  have hPpow : P ^ (p ^ m) = thetaG (p ^ m) (MvPowerSeries.map (iterateFrobenius κ p m) P) := by
    rw [hP, ← iterateFrobenius_def, map_sum (iterateFrobenius (MvPowerSeries σ κ) p m),
      map_sum (MvPowerSeries.map (iterateFrobenius κ p m)), thetaG_sum hq]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [iterateFrobenius_def, MvPowerSeries.monomial_pow, MvPowerSeries.map_monomial,
      iterateFrobenius_def, thetaG_monomial hq]
  rw [hf, add_pow_char_pow, map_add (coeff n), hPpow, map_add (MvPowerSeries.map (iterateFrobenius κ p m)),
    thetaG_add hq, map_add (coeff n)]
  congr 1
  rw [coeff_pow_eq_zero_of_low g n hgcoeff hq]
  symm
  apply coeff_thetaG_eq_zero hq
  intro d hd
  rw [MvPowerSeries.coeff_map, hgcoeff d hd, map_zero]

end FrobComm

section Unfrob

theorem hasKernelOfDegree_of_comp_xq {q : ℕ} (hq : q ≠ 0) (φ : Series B) {d : ℕ}
    [Module.Projective B (FormalODModule.KerAlgebra φ)]
    (h : FormalODModule.HasKernelOfDegree (φ.comp (xq B q)) (d * q ^ 2)) :
    FormalODModule.HasKernelOfDegree φ d := by
  classical
  obtain ⟨hfin, hproj, hfib⟩ := h
  let α₀ : Idx q := fun _ => ⟨0, Nat.pos_of_ne_zero hq⟩
  have hcard : Fintype.card (Idx q) = q ^ 2 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  refine ⟨?_, inferInstance, fun κ _ f => ?_⟩
  · haveI : Module.Finite B (Idx q → FormalODModule.KerAlgebra φ) := Module.Finite.equiv (kerEquiv hq φ)
    exact Module.Finite.of_surjective
      (LinearMap.proj (R := B) (φ := fun _ : Idx q => FormalODModule.KerAlgebra φ) α₀) (fun x => ⟨fun _ => x, rfl⟩)
  · have e := hfib κ f
    rw [map_comp_xq φ f hq, (kerEquiv hq (φ.map f)).finrank_eq] at e
    by_cases hK : Module.Finite κ (FormalODModule.KerAlgebra (φ.map f))
    · rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul, hcard, mul_comm] at e
      exact Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero hq) 2) e
    · have hK' : ¬ Module.Finite κ (Idx q → FormalODModule.KerAlgebra (φ.map f)) := by
        intro hfin'
        apply hK
        exact Module.Finite.of_surjective (LinearMap.proj (R := κ) (φ := fun _ : Idx q => FormalODModule.KerAlgebra (φ.map f)) α₀)
          (fun x => ⟨fun _ => x, rfl⟩)
      rw [Module.finrank_of_not_finite hK'] at e
      have hd : d = 0 := by
        rcases mul_eq_zero.mp e.symm with h | h
        · exact h
        · exact absurd h (pow_ne_zero 2 hq)
      rw [Module.finrank_of_not_finite hK, hd]

end Unfrob

section FieldHelpers

variable {κ : Type u} [Field κ]

theorem hasKernelOfDegree_map_field {κ' : Type u} [Field κ'] (f : κ →+* κ') (φ : Series κ) {d : ℕ} (hd : d ≠ 0)
    (h : FormalODModule.HasKernelOfDegree φ d) : FormalODModule.HasKernelOfDegree (φ.map f) d := by
  refine ⟨?_, inferInstance, fun κ'' _ g => ?_⟩
  · have e := h.2.2 κ' f
    have hpos : 0 < Module.finrank κ' (FormalODModule.KerAlgebra (φ.map f)) := by
      rw [e]; exact Nat.pos_of_ne_zero hd
    exact Module.finite_of_finrank_pos hpos
  · rw [Series.map_map]
    exact h.2.2 κ'' (g.comp f)

theorem hasKernelOfDegree_id : FormalODModule.HasKernelOfDegree (Series.id κ) 1 := by
  have key : ∀ (L : Type u) [Field L], Module.Finite L (FormalODModule.KerAlgebra (Series.id L)) ∧
      Module.finrank L (FormalODModule.KerAlgebra (Series.id L)) = 1 := by
    intro L _
    have hI : Ideal.span (Set.range (Series.id L)) =
        RingHom.ker (constantCoeff : MvPowerSeries (Fin 2) L →+* L) :=
      MvPowerSeries.span_range_X_eq_ker_constantCoeff 2
    have hsurj : Function.Surjective (constantCoeff : MvPowerSeries (Fin 2) L →+* L) :=
      fun x => ⟨MvPowerSeries.C x, MvPowerSeries.constantCoeff_C _⟩
    let e0 : FormalODModule.KerAlgebra (Series.id L) ≃+* L :=
      (Ideal.quotEquivOfEq hI).trans (RingHom.quotientKerEquivOfSurjective hsurj)
    have he0 : ∀ c : L, e0 (algebraMap L (FormalODModule.KerAlgebra (Series.id L)) c) = c := by
      intro c
      show e0 (Ideal.Quotient.mk _ (MvPowerSeries.C c)) = c
      simp only [e0, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk,
        MvPowerSeries.constantCoeff_C]
    let e : FormalODModule.KerAlgebra (Series.id L) ≃ₐ[L] L := AlgEquiv.ofRingEquiv (f := e0) he0
    exact ⟨Module.Finite.equiv e.toLinearEquiv.symm, by rw [e.toLinearEquiv.finrank_eq, Module.finrank_self]⟩
  refine ⟨(key κ).1, inferInstance, fun κ' _ f => ?_⟩
  rw [Series.map_id]
  exact (key κ').2

end FieldHelpers

section VOne

variable (p : ℕ) [Fact p.Prime] {κ : Type u} [Field κ] [CharP κ p]

theorem hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero

def α₀ : Idx p := fun _ => ⟨0, (Fact.out : p.Prime).pos⟩

variable {p}

theorem exists_not_dvd_emb (α : Idx p) (hα : α ≠ α₀ p) (m : Fin 2 →₀ ℕ) : ∃ j, ¬ p ∣ emb α m j := by
  by_contra hcon
  push Not at hcon
  apply hα
  funext j
  apply Fin.ext
  have hj := hcon j
  rw [emb_apply] at hj
  have hj' : p ∣ (α j : ℕ) := (Nat.dvd_add_left (dvd_mul_right p (m j))).mp hj
  have hlt := (α j).isLt
  show (α j : ℕ) = 0
  exact Nat.eq_zero_of_dvd_of_lt hj' hlt

theorem decim_one (α : Idx p) : decim (hp0 p) (1 : MvPowerSeries (Fin 2) κ) α = if α = α₀ p then 1 else 0 := by
  classical
  ext m
  rw [coeff_decim, MvPowerSeries.coeff_one]
  by_cases hα : α = α₀ p
  · subst hα
    rw [if_pos rfl, MvPowerSeries.coeff_one]
    have : emb (α₀ p) m = 0 ↔ m = 0 := by
      constructor
      · intro h; ext i
        have := DFunLike.congr_fun h i
        simp only [emb_apply, α₀, zero_add, Finsupp.coe_zero, Pi.zero_apply, mul_eq_zero] at this
        rcases this with h1 | h1
        · exact absurd h1 (hp0 p)
        · exact h1
      · rintro rfl; ext i; simp [emb_apply, α₀]
    by_cases hm : m = 0
    · rw [if_pos (this.2 hm), if_pos hm]
    · rw [if_neg (fun h => hm (this.1 h)), if_neg hm]
  · rw [if_neg hα, if_neg]
    · rfl
    · intro h
      obtain ⟨j, hj⟩ := exists_not_dvd_emb α hα m
      apply hj
      rw [h]
      exact dvd_zero _

theorem theta_decim_of_vanish (f : MvPowerSeries (Fin 2) κ)
    (hf : ∀ α, α ≠ α₀ p → decim (hp0 p) f α = 0) :
    theta (q := p) (decim (hp0 p) f (α₀ p)) = f := by
  classical
  apply (decim (hp0 p)).injective
  funext β
  have h1 : decim (hp0 p) (theta (q := p) (decim (hp0 p) f (α₀ p))) β =
      decim (hp0 p) f (α₀ p) * decim (hp0 p) 1 β := by
    rw [← decim_theta_mul (hp0 p), mul_one]
  rw [h1, decim_one]
  by_cases hβ : β = α₀ p
  · rw [if_pos hβ, mul_one, hβ]
  · rw [if_neg hβ, mul_zero, hf β hβ]

variable (p)

def vOne (Φ : FormalODModule p κ) : Series κ := fun i => decim (hp0 p) (Φ.act (p : Zp2 p) i) (α₀ p)

theorem coeff_act_p_eq_zero (Φ : FormalODModule p κ) (i : Fin 2) (m : Fin 2 →₀ ℕ) (hm : ∃ j, ¬ p ∣ m j) :
    coeff m (Φ.act (p : Zp2 p) i) = 0 := by
  have h0 : ∀ i, constantCoeff (Φ.act (p : Zp2 p) i) = 0 := (Φ.isLawHom_act _).1
  have h1 : MvFormalGroup.linearPart (Φ.act (p : Zp2 p)) = 0 := by
    rw [FormalODModule.act_natCast, MvFormalGroup.linearPart_nthSeries]
    rw [nsmul_eq_mul, show ((p : ℕ) : Matrix (Fin 2) (Fin 2) κ) = 0 from ?_, zero_mul]
    ext a b
    rw [Matrix.natCast_apply, Matrix.zero_apply]
    split_ifs
    · exact CharP.cast_eq_zero κ p
    · exact Nat.cast_zero
  exact MvFormalGroup.coeff_eq_zero_of_linearPart_eq_zero_of_subst_eq_charP p Φ.F Φ.F (Φ.act (p : Zp2 p)) h0 h1
    (Φ.isLawHom_act _).2 i m hm

theorem theta_vOne (Φ : FormalODModule p κ) (i : Fin 2) : theta (q := p) (vOne p Φ i) = Φ.act (p : Zp2 p) i := by
  apply theta_decim_of_vanish
  intro α hα
  ext m
  rw [coeff_decim, MvPowerSeries.coeff_zero]
  exact coeff_act_p_eq_zero p Φ i _ (exists_not_dvd_emb α hα m)

theorem vOne_comp_xq (Φ : FormalODModule p κ) : (vOne p Φ).comp (xq κ p) = Φ.act (p : Zp2 p) := by
  funext i
  exact theta_vOne p Φ i

theorem constantCoeff_vOne (Φ : FormalODModule p κ) (i : Fin 2) : constantCoeff (vOne p Φ i) = 0 := by
  have h1 : coeff (p • (0 : Fin 2 →₀ ℕ)) (thetaG p (vOne p Φ i)) = coeff 0 (vOne p Φ i) :=
    coeff_smul_thetaG (hp0 p) _ _
  have h2 : thetaG p (vOne p Φ i) = Φ.act (p : Zp2 p) i := theta_vOne p Φ i
  rw [smul_zero, h2, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, (Φ.isLawHom_act _).1 i] at h1
  exact h1.symm

theorem hasSubst_XL : HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) :=
  hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _

theorem hasSubst_XR : HasSubst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) :=
  hasSubst_of_constantCoeff_zero fun l => MvPowerSeries.constantCoeff_X _

theorem thetaG_map_frobenius {σ : Type} [Fintype σ] [DecidableEq σ] (f : MvPowerSeries σ κ) :
    thetaG p (MvPowerSeries.map (frobenius κ p) f) = f ^ p := by
  have h := pow_eq_thetaG_map p 1 f
  rw [pow_one, iterateFrobenius_one] at h
  exact h.symm

theorem isLawHom_vOne (Φ : FormalODModule p κ) :
    IsLawHom (Φ.F.map (frobenius κ p)) Φ.F (vOne p Φ) := by
  classical
  have hp := hp0 p
  set V := vOne p Φ with hVdef
  have hV0 : ∀ i, constantCoeff (V i) = 0 := constantCoeff_vOne p Φ
  have hSV : HasSubst V := hasSubst_of_constantCoeff_zero hV0
  refine ⟨hV0, fun i => ?_⟩

  let F : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) κ := Φ.F.toPowerSeries
  let T : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) κ := xqG (Fin 2 ⊕ Fin 2) κ p
  have hT : HasSubst T := hasSubst_xqG hp
  have hF : HasSubst F := Φ.F.hasSubst_toPowerSeries
  have hF' : HasSubst (Φ.F.map (frobenius κ p)).toPowerSeries := (Φ.F.map (frobenius κ p)).hasSubst_toPowerSeries
  have hxq : HasSubst (xq κ p) := hasSubst_xq hp
  let P : Series κ := Φ.act (p : Zp2 p)
  have hP0 : ∀ i, constantCoeff (P i) = 0 := (Φ.isLawHom_act _).1

  let E : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) κ :=
    Sum.elim (fun j => subst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) (V j))
      (fun j => subst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) (V j))
  let EP : Fin 2 ⊕ Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) κ :=
    Sum.elim (fun j => subst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) (P j))
      (fun j => subst (fun l : Fin 2 => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) κ)) (P j))
  have hE : HasSubst E := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact MvPowerSeries.constantCoeff_subst_eq_zero hasSubst_XL (fun l => MvPowerSeries.constantCoeff_X _) (hV0 j)
    · exact MvPowerSeries.constantCoeff_subst_eq_zero hasSubst_XR (fun l => MvPowerSeries.constantCoeff_X _) (hV0 j)
  show subst (Φ.F.map (frobenius κ p)).toPowerSeries (V i) = subst E (F i)
  apply thetaG_injective (σ := Fin 2 ⊕ Fin 2) hp

  have hL : thetaG p (subst (Φ.F.map (frobenius κ p)).toPowerSeries (V i)) = subst EP (F i) := by
    unfold thetaG
    rw [MvPowerSeries.subst_comp_subst_apply hF' hT]
    have h1 : (fun j => subst T ((Φ.F.map (frobenius κ p)).toPowerSeries j)) = fun j => F j ^ p := by
      funext j
      exact thetaG_map_frobenius p (F j)
    have h2 : (fun j => F j ^ p) = fun j => subst F (xq κ p j) := by
      funext j
      rw [xq, MvPowerSeries.subst_pow hF, MvPowerSeries.subst_X hF]
    rw [h1, h2, ← MvPowerSeries.subst_comp_subst_apply hxq hF]
    have h3 : subst (xq κ p) (V i) = P i := theta_vOne p Φ i
    rw [h3]
    exact (Φ.isLawHom_act _).2 i

  have hR : thetaG p (subst E (F i)) = subst EP (F i) := by
    unfold thetaG
    rw [MvPowerSeries.subst_comp_subst_apply hE hT]
    congr 1
    funext s
    rcases s with j | j
    · show subst T (subst _ (V j)) = subst _ (Φ.act (p : Zp2 p) j)
      rw [MvPowerSeries.subst_comp_subst_apply hasSubst_XL hT, ← theta_vOne p Φ j, theta,
        MvPowerSeries.subst_comp_subst_apply hxq hasSubst_XL]
      congr 1
      funext l
      rw [MvPowerSeries.subst_X hT, xq, MvPowerSeries.subst_pow hasSubst_XL, MvPowerSeries.subst_X hasSubst_XL]
      rfl
    · show subst T (subst _ (V j)) = subst _ (Φ.act (p : Zp2 p) j)
      rw [MvPowerSeries.subst_comp_subst_apply hasSubst_XR hT, ← theta_vOne p Φ j, theta,
        MvPowerSeries.subst_comp_subst_apply hxq hasSubst_XR]
      congr 1
      funext l
      rw [MvPowerSeries.subst_X hT, xq, MvPowerSeries.subst_pow hasSubst_XR, MvPowerSeries.subst_X hasSubst_XR]
      rfl
  rw [hL, hR]

theorem comp_xq_injective {φ ψ : Series κ} (h : φ.comp (xq κ p) = ψ.comp (xq κ p)) : φ = ψ := by
  funext i
  exact thetaG_injective (σ := Fin 2) (hp0 p) (congrFun h i)

theorem map_frobenius_comp_xq (φ : Series κ) (hφ : ∀ i, constantCoeff (φ i) = 0) :
    (φ.map (frobenius κ p)).comp (xq κ p) = (xq κ p).comp φ := by
  funext i
  show subst (xq κ p) (MvPowerSeries.map (frobenius κ p) (φ i)) = subst φ (xq κ p i)
  rw [xq, MvPowerSeries.subst_pow (hasSubst_of_constantCoeff_zero hφ),
    MvPowerSeries.subst_X (hasSubst_of_constantCoeff_zero hφ)]
  exact thetaG_map_frobenius p (φ i)

theorem isODHom_vOne (Φ : FormalODModule p κ) :
    FormalODModule.IsODHom (Φ.map (frobenius κ p)) Φ (vOne p Φ) := by
  have hp := hp0 p
  set V := vOne p Φ with hVdef
  have hV0 : ∀ i, constantCoeff (V i) = 0 := constantCoeff_vOne p Φ
  have hxq0 : ∀ i, constantCoeff (xq κ p i) = 0 := constantCoeff_xq hp
  have hact0 : ∀ (a : Zp2 p) i, constantCoeff (Φ.act a i) = 0 := fun a => (Φ.isLawHom_act a).1
  have hVF : V.comp (xq κ p) = Φ.act (p : Zp2 p) := vOne_comp_xq p Φ
  refine ⟨isLawHom_vOne p Φ, fun a => ?_, ?_⟩
  · apply comp_xq_injective (p := p)
    show (V.comp ((Φ.act a).map (frobenius κ p))).comp (xq κ p) = ((Φ.act a).comp V).comp (xq κ p)
    have hm0 : ∀ i, constantCoeff (((Φ.act a).map (frobenius κ p)) i) = 0 := fun i => by
      show constantCoeff (MvPowerSeries.map _ (Φ.act a i)) = 0
      rw [MvPowerSeries.constantCoeff_map, hact0, map_zero]
    rw [Series.comp_assoc _ _ _ hm0 hxq0, map_frobenius_comp_xq p (Φ.act a) (hact0 a),
      ← Series.comp_assoc _ _ _ hxq0 (hact0 a), hVF, ← Φ.act_mul, mul_comm, Φ.act_mul, ← hVF,
      Series.comp_assoc _ _ _ hV0 hxq0]
  · apply comp_xq_injective (p := p)
    show (V.comp (Φ.varpi.map (frobenius κ p))).comp (xq κ p) = (Φ.varpi.comp V).comp (xq κ p)
    have hw0 : ∀ i, constantCoeff (Φ.varpi i) = 0 := Φ.isLawHom_varpi.1
    have hm0 : ∀ i, constantCoeff ((Φ.varpi.map (frobenius κ p)) i) = 0 := fun i => by
      show constantCoeff (MvPowerSeries.map _ (Φ.varpi i)) = 0
      rw [MvPowerSeries.constantCoeff_map, hw0, map_zero]
    have hpw : (Φ.act (p : Zp2 p)).comp Φ.varpi = Φ.varpi.comp (Φ.act (p : Zp2 p)) := by
      rw [Φ.varpi_comp_act, map_natCast]
    rw [Series.comp_assoc _ _ _ hm0 hxq0, map_frobenius_comp_xq p Φ.varpi hw0,
      ← Series.comp_assoc _ _ _ hxq0 hw0, hVF, hpw, ← hVF, Series.comp_assoc _ _ _ hV0 hxq0]

theorem vOne_spec (Φ : FormalODModule p κ) (hΦ4 : Φ.HasHeight 4) :
    FormalODModule.IsODHom (Φ.map (frobenius κ p)) Φ (vOne p Φ) ∧
      (vOne p Φ).comp (xq κ p) = Φ.act (p : Zp2 p) ∧
      FormalODModule.HasKernelOfDegree (vOne p Φ) (p ^ 2) := by
  refine ⟨isODHom_vOne p Φ, vOne_comp_xq p Φ, ?_⟩
  apply hasKernelOfDegree_of_comp_xq (hp0 p)
  rw [vOne_comp_xq, ← pow_add]
  exact hΦ4

end VOne

section Main

variable (p : ℕ) [Fact p.Prime] {κ : Type u} [Field κ] [CharP κ p]

theorem xq_pow_succ (m : ℕ) : xq κ (p ^ (m + 1)) = (xq κ p).comp (xq κ (p ^ m)) := by
  funext i
  show (MvPowerSeries.X i : MvPowerSeries (Fin 2) κ) ^ (p ^ (m + 1)) = subst (xq κ (p ^ m)) ((MvPowerSeries.X i) ^ p)
  have h : HasSubst (xq κ (p ^ m)) := hasSubst_xq (pow_ne_zero _ (hp0 p))
  rw [MvPowerSeries.subst_pow h, MvPowerSeries.subst_X h, xq, ← pow_mul, pow_succ]

theorem iterateFrobenius_succ (m : ℕ) :
    iterateFrobenius κ p (m + 1) = (iterateFrobenius κ p m).comp (frobenius κ p) := by
  ext x
  rw [RingHom.comp_apply, ← iterateFrobenius_one, ← iterateFrobenius_add_apply]

theorem main (Φ : FormalODModule p κ) (hΦ4 : Φ.HasHeight 4) (m : ℕ) :
    ∃ V : Series κ,
      FormalODModule.IsODHom (Φ.map (iterateFrobenius κ p m)) Φ V ∧
      V.comp (xq κ (p ^ m)) = Φ.act ((p : Zp2 p) ^ m) ∧
      FormalODModule.HasKernelOfDegree V (p ^ (2 * m)) := by
  induction m with
  | zero =>
    refine ⟨Series.id κ, ?_, ?_, ?_⟩
    · rw [iterateFrobenius_zero, FormalODModule.map_id]
      exact FormalODModule.IsODHom.id Φ
    · rw [pow_zero, pow_zero, Φ.act_one]
      have : xq κ 1 = Series.id κ := by funext i; exact pow_one _
      rw [this, Series.comp_id]
    · rw [mul_zero, pow_zero]
      exact hasKernelOfDegree_id
  | succ m ih =>
    obtain ⟨Vm, hVm, hVmF, hVmdeg⟩ := ih
    obtain ⟨hV1, hV1F, hV1deg⟩ := vOne_spec p Φ hΦ4
    have hp := hp0 p
    let W : Series κ := (vOne p Φ).map (iterateFrobenius κ p m)
    have hV10 : ∀ i, constantCoeff (vOne p Φ i) = 0 := constantCoeff_vOne p Φ
    have hW0 : ∀ i, constantCoeff (W i) = 0 := fun i => by
      show constantCoeff (MvPowerSeries.map _ (vOne p Φ i)) = 0
      rw [MvPowerSeries.constantCoeff_map, hV10, map_zero]
    have hVm0 : ∀ i, constantCoeff (Vm i) = 0 := hVm.constantCoeff
    refine ⟨Vm.comp W, ?_, ?_, ?_⟩
    ·
      have hW : FormalODModule.IsODHom ((Φ.map (frobenius κ p)).map (iterateFrobenius κ p m))
          (Φ.map (iterateFrobenius κ p m)) W := hV1.map _
      rw [FormalODModule.map_map, ← iterateFrobenius_succ] at hW
      exact hVm.comp hW
    ·
      have hxq0 : ∀ i, constantCoeff (xq κ (p ^ m) i) = 0 := constantCoeff_xq (pow_ne_zero _ hp)
      have hxq0' : ∀ i, constantCoeff (xq κ (p ^ (m + 1)) i) = 0 := constantCoeff_xq (pow_ne_zero _ hp)
      have hWF : W.comp (xq κ p) = (Φ.map (iterateFrobenius κ p m)).act (p : Zp2 p) := by
        show ((vOne p Φ).map (iterateFrobenius κ p m)).comp (xq κ p) = _
        rw [← map_comp_xq _ _ hp, hV1F]
        rfl
      have hact0 : ∀ i, constantCoeff ((Φ.map (iterateFrobenius κ p m)).act (p : Zp2 p) i) = 0 :=
        ((Φ.map (iterateFrobenius κ p m)).isLawHom_act _).1
      rw [Series.comp_assoc _ _ _ hW0 hxq0', xq_pow_succ, ← Series.comp_assoc _ _ _ (constantCoeff_xq hp) hxq0,
        hWF, ← Series.comp_assoc _ _ _ hact0 hxq0, hVm.2.1, Series.comp_assoc _ _ _ hVm0 hxq0, hVmF,
        ← Φ.act_mul, ← pow_succ']
    ·
      have hWdeg : FormalODModule.HasKernelOfDegree W (p ^ 2) :=
        hasKernelOfDegree_map_field _ _ (pow_ne_zero 2 hp) hV1deg
      have h := CerednikDrinfeld.FormalODModule.HasKernelOfDegree.comp_map_of_field (RingHom.id κ) hVmdeg hW0 hWdeg
      rw [Series.map_ringHom_id] at h
      have e : p ^ (2 * m) * p ^ 2 = p ^ (2 * (m + 1)) := by ring
      rw [e] at h
      exact h

end Main

end R4Versch
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_map_iterateFrobenius_comp_X_pow_eq_act_pow.R4Versch"

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal in
theorem solution
    {p : ℕ} [Fact p.Prime] {κ : Type u} [Field κ] [CharP κ p]
    (Φ : FormalODModule p κ) (hΦ4 : Φ.HasHeight 4) (m : ℕ) :
    ∃ V : Series κ,
      FormalODModule.IsODHom (Φ.map (iterateFrobenius κ p m)) Φ V ∧
      V.comp (fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) κ) ^ (p ^ m)) =
        Φ.act ((p : Zp2 p) ^ m) ∧
      FormalODModule.HasKernelOfDegree V (p ^ (2 * m)) :=
  R4Versch.main p Φ hΦ4 m

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_map_iterateFrobenius_comp_X_pow_eq_act_pow.R4Versch"

end S_CerednikDrinfeld_FormalODModule_exists_isODHom_map_iterateFrobenius_comp_X_pow_eq_act_pow
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isODHom_map_iterateFrobenius_comp_X_pow_eq_act_pow (solution)
