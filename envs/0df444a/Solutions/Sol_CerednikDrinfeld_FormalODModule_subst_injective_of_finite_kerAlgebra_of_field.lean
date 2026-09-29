-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.subst_injective_of_finite_kerAlgebra_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/abf14e75-ea91-5d51-b8aa-ac1e3972b457

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_field

set_option autoImplicit false

universe u

open MvPowerSeries CerednikDrinfeld CerednikDrinfeld.SpecialFormal

noncomputable section

open MvPowerSeries
open scoped Classical

namespace SubstInj

section general
variable {σ : Type*} {R : Type*} [CommRing R]

def J (σ : Type*) (R : Type*) [CommRing R] (n : ℕ) : Ideal (MvPowerSeries σ R) where
  carrier := {f | (n : ℕ∞) ≤ f.order}
  add_mem' := by
    intro f g hf hg
    exact le_trans (le_min hf hg) min_order_le_add
  zero_mem' := by simp [order_zero]
  smul_mem' := by
    intro c f hf
    simp only [smul_eq_mul, Set.mem_setOf_eq]
    exact le_trans hf (le_trans le_add_self le_order_mul)

theorem mem_J {n : ℕ} {f : MvPowerSeries σ R} :
    f ∈ J σ R n ↔ ∀ d : σ →₀ ℕ, d.degree < n → coeff d f = 0 := by
  constructor
  · intro hf d hd
    apply coeff_of_lt_order
    exact lt_of_lt_of_le (by exact_mod_cast hd) hf
  · intro h
    exact nat_le_order h

theorem J_zero : J σ R 0 = ⊤ := by
  ext f; simp [mem_J]

theorem J_antitone {m n : ℕ} (h : m ≤ n) : J σ R n ≤ J σ R m := by
  intro f hf
  show (m : ℕ∞) ≤ f.order
  exact le_trans (by exact_mod_cast h) (show (n : ℕ∞) ≤ f.order from hf)

theorem J_mul_le (a b : ℕ) : J σ R a * J σ R b ≤ J σ R (a + b) := by
  rw [Ideal.mul_le]
  intro f hf g hg
  show ((a + b : ℕ) : ℕ∞) ≤ (f * g).order
  push_cast
  exact le_trans (add_le_add hf hg) le_order_mul

theorem J_pow_le (a n : ℕ) : J σ R a ^ n ≤ J σ R (n * a) := by
  induction n with
  | zero => simp [J_zero]
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact le_trans (Ideal.mul_mono ih le_rfl) (J_mul_le _ _)

theorem mem_J_one_iff {f : MvPowerSeries σ R} : f ∈ J σ R 1 ↔ constantCoeff f = 0 := by
  show ((1 : ℕ) : ℕ∞) ≤ f.order ↔ _
  rw [Nat.cast_one]
  exact one_le_order_iff_constCoeff_eq_zero

theorem J_one_ne_top [Nontrivial R] : J σ R 1 ≠ ⊤ := by
  intro h
  have : (1 : MvPowerSeries σ R) ∈ J σ R 1 := h ▸ Submodule.mem_top
  rw [mem_J_one_iff] at this
  simp at this

theorem monomial_mem_J [DecidableEq σ] (d : σ →₀ ℕ) (a : R) : monomial d a ∈ J σ R d.degree := by
  rw [mem_J]
  intro e he
  rw [coeff_monomial]
  split_ifs with h
  · subst h; exact absurd he (lt_irrefl _)
  · rfl

end general

section two
variable {R : Type*} [CommRing R]

local notation "A" => MvPowerSeries (Fin 2) R

def pw (φ : Fin 2 → A) (β : Fin 2 →₀ ℕ) : A := φ 0 ^ β 0 * φ 1 ^ β 1

theorem pw_add (φ : Fin 2 → A) (β γ : Fin 2 →₀ ℕ) : pw φ (β + γ) = pw φ β * pw φ γ := by
  simp only [pw, Finsupp.add_apply, pow_add]; ring

theorem pw_zero (φ : Fin 2 → A) : pw φ 0 = 1 := by simp [pw]

theorem pw_single (φ : Fin 2 → A) (i : Fin 2) : pw φ (Finsupp.single i 1) = φ i := by
  fin_cases i <;> simp [pw]

theorem degree_fin_two (β : Fin 2 →₀ ℕ) : β.degree = β 0 + β 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

theorem pw_mem_J {φ : Fin 2 → A} (hφ : ∀ i, φ i ∈ J (Fin 2) R 1) (β : Fin 2 →₀ ℕ) :
    pw φ β ∈ J (Fin 2) R β.degree := by
  rw [degree_fin_two]
  have h0 : φ 0 ^ β 0 ∈ J (Fin 2) R (β 0) := by
    have := Ideal.pow_mem_pow (hφ 0) (β 0)
    exact J_pow_le 1 (β 0) |>.trans (by simp) this
  have h1 : φ 1 ^ β 1 ∈ J (Fin 2) R (β 1) := by
    have := Ideal.pow_mem_pow (hφ 1) (β 1)
    exact J_pow_le 1 (β 1) |>.trans (by simp) this
  exact J_mul_le _ _ (Ideal.mul_mem_mul h0 h1)

theorem prod_eq_pw (φ : Fin 2 → A) (β : Fin 2 →₀ ℕ) :
    (β.prod fun i k => φ i ^ k) = pw φ β := by
  rw [Finsupp.prod_of_support_subset β (Finset.subset_univ _) (fun i k => φ i ^ k) (fun i _ => pow_zero _)]
  simp [pw, Fin.prod_univ_two]

theorem subst_monomial_eq (φ : Fin 2 → A) (hφ : HasSubst φ) (β : Fin 2 →₀ ℕ) (a : R) :
    subst φ (monomial β a) = C a * pw φ β := by
  rw [subst_monomial hφ, prod_eq_pw]; rfl

def XI : Ideal A := Ideal.span {X 0, X 1}

theorem XI_le_J_one : (XI : Ideal A) ≤ J (Fin 2) R 1 := by
  rw [XI, Ideal.span_le]
  rintro f (rfl | rfl) <;> simp [SetLike.mem_coe, mem_J_one_iff]

theorem J_succ_le_XI_mul (n : ℕ) : J (Fin 2) R (n + 1) ≤ XI * J (Fin 2) R n := by
  intro f hf
  rw [mem_J] at hf
  let g₀ : A := fun α => coeff (α + Finsupp.single 0 1) f
  let g₁ : A := fun α => if α 0 = 0 then coeff (α + Finsupp.single 1 1) f else 0
  have hg₀ : g₀ ∈ J (Fin 2) R n := by
    rw [mem_J]; intro d hd
    show coeff (d + Finsupp.single 0 1) f = 0
    apply hf; simp [degree_fin_two] at hd ⊢; omega
  have hg₁ : g₁ ∈ J (Fin 2) R n := by
    rw [mem_J]; intro d hd
    show (if d 0 = 0 then coeff (d + Finsupp.single 1 1) f else 0) = 0
    split_ifs with h
    · apply hf; simp [degree_fin_two] at hd ⊢; omega
    · rfl
  have hdec : f = X 0 * g₀ + X 1 * g₁ := by
    ext d
    rw [map_add, X, X, coeff_monomial_mul, coeff_monomial_mul]
    by_cases h0 : d 0 = 0
    · by_cases h1 : d 1 = 0
      · have hd : d = 0 := by ext i; fin_cases i <;> simp [h0, h1]
        subst hd
        have := hf 0 (by simp)
        simp [this]
      · have hle : Finsupp.single (1 : Fin 2) 1 ≤ d := by
          intro i; fin_cases i <;> simp; omega
        have hnle : ¬ Finsupp.single (0 : Fin 2) 1 ≤ d := by
          intro h; have := h 0; simp at this; omega
        rw [if_neg hnle, if_pos hle, zero_add, one_mul]
        show coeff d f = if (d - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 = 0 then coeff (d - Finsupp.single 1 1 + Finsupp.single 1 1) f else 0
        rw [if_pos (by simp [h0]), tsub_add_cancel_of_le hle]
    · have hle : Finsupp.single (0 : Fin 2) 1 ≤ d := by
        intro i; fin_cases i <;> simp; omega
      rw [if_pos hle, one_mul]
      have e1 : coeff (d - Finsupp.single 0 1) g₀ = coeff d f := by
        show coeff (d - Finsupp.single 0 1 + Finsupp.single 0 1) f = coeff d f
        rw [tsub_add_cancel_of_le hle]
      rw [e1]
      by_cases hle1 : Finsupp.single (1 : Fin 2) 1 ≤ d
      · rw [if_pos hle1, one_mul]
        have e2 : coeff (d - Finsupp.single 1 1) g₁ = 0 := by
          show (if (d - Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 = 0 then coeff (d - Finsupp.single 1 1 + Finsupp.single 1 1) f else 0) = 0
          rw [if_neg]; simp [h0]
        rw [e2, add_zero]
      · rw [if_neg hle1, add_zero]
  rw [hdec]
  exact Ideal.add_mem _ (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hg₀)
    (Ideal.mul_mem_mul (Ideal.subset_span (by simp)) hg₁)

theorem J_le_XI_pow (n : ℕ) : J (Fin 2) R n ≤ XI ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ']
    exact le_trans (J_succ_le_XI_mul n) (Ideal.mul_mono_right ih)

end two

section fieldcase
variable {κ : Type*} [Field κ]

local notation "𝔸" => MvPowerSeries (Fin 2) κ

theorem I_le_J_one {φ : Fin 2 → 𝔸} (hφ : ∀ i, constantCoeff (φ i) = 0) :
    Ideal.span (Set.range φ) ≤ J (Fin 2) κ 1 := by
  rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact mem_J_one_iff.mpr (hφ i)

theorem exists_J_le_I {φ : Fin 2 → 𝔸} (hφ : ∀ i, constantCoeff (φ i) = 0)
    (hfin : Module.Finite κ (𝔸 ⧸ Ideal.span (Set.range φ))) :
    ∃ r, J (Fin 2) κ r ≤ Ideal.span (Set.range φ) := by
  set I : Ideal 𝔸 := Ideal.span (Set.range φ) with hIdef
  have hIJ : I ≤ J (Fin 2) κ 1 := I_le_J_one hφ
  have hJtop : J (Fin 2) κ 1 ≠ ⊤ := J_one_ne_top
  have hItop : I ≠ ⊤ := fun h => hJtop (top_le_iff.mp (h ▸ hIJ))
  haveI : Nontrivial (𝔸 ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (𝔸 ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsArtinianRing (𝔸 ⧸ I) := IsArtinianRing.of_finite κ (𝔸 ⧸ I)
  obtain ⟨r, hr⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := 𝔸 ⧸ I)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hr
  have hmap : Ideal.map (Ideal.Quotient.mk I) (J (Fin 2) κ 1) ≤ IsLocalRing.maximalIdeal _ := by
    apply IsLocalRing.le_maximalIdeal
    intro htop
    have h1 : (1 : 𝔸 ⧸ I) ∈ Ideal.map (Ideal.Quotient.mk I) (J (Fin 2) κ 1) := htop ▸ Submodule.mem_top
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at h1
    obtain ⟨x, hx, hx1⟩ := h1
    have hx1' : x - 1 ∈ I := by rw [← Ideal.Quotient.eq, hx1, map_one]
    have : (1 : 𝔸) ∈ J (Fin 2) κ 1 := by
      have := (J (Fin 2) κ 1).sub_mem hx (hIJ hx1')
      rwa [sub_sub_cancel] at this
    exact hJtop (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  have hpow : Ideal.map (Ideal.Quotient.mk I) (J (Fin 2) κ 1 ^ r) = ⊥ := by
    rw [Ideal.map_pow, eq_bot_iff]
    have := Ideal.pow_right_mono hmap r
    rw [hr] at this
    simpa using this
  rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker] at hpow
  exact ⟨r, le_trans (J_le_XI_pow r) (le_trans (Ideal.pow_right_mono XI_le_J_one r) hpow)⟩

def toF (p : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 p.1 + Finsupp.single 1 p.2

@[scoped simp] theorem toF_zero (p : ℕ × ℕ) : toF p 0 = p.1 := by simp [toF]
@[scoped simp] theorem toF_one (p : ℕ × ℕ) : toF p 1 = p.2 := by simp [toF]

theorem toF_eta (β : Fin 2 →₀ ℕ) : toF (β 0, β 1) = β := by
  ext i; fin_cases i <;> simp

theorem toF_injective : Function.Injective toF := by
  intro p q h
  have h0 := congrArg (fun β : Fin 2 →₀ ℕ => β 0) h
  have h1 := congrArg (fun β : Fin 2 →₀ ℕ => β 1) h
  simp only [toF_zero, toF_one] at h0 h1
  exact Prod.ext h0 h1

theorem degree_toF (p : ℕ × ℕ) : (toF p).degree = p.1 + p.2 := by
  simp [degree_fin_two]

def degLt (n : ℕ) : Finset (Fin 2 →₀ ℕ) :=
  ((Finset.range n ×ˢ Finset.range n).filter (fun p => p.1 + p.2 < n)).image toF

theorem mem_degLt {n : ℕ} {β : Fin 2 →₀ ℕ} : β ∈ degLt n ↔ β.degree < n := by
  constructor
  · intro h
    rw [degLt, Finset.mem_image] at h
    obtain ⟨p, hp, rfl⟩ := h
    rw [Finset.mem_filter] at hp
    rw [degree_toF]; exact hp.2
  · intro h
    rw [degLt, Finset.mem_image]
    refine ⟨(β 0, β 1), ?_, toF_eta β⟩
    rw [degree_fin_two] at h
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    omega

def box (r : ℕ) : Finset (Fin 2 →₀ ℕ) := (Finset.range r ×ˢ Finset.range r).image toF

theorem mem_box {r : ℕ} {β : Fin 2 →₀ ℕ} : β ∈ box r ↔ β 0 < r ∧ β 1 < r := by
  constructor
  · intro h
    rw [box, Finset.mem_image] at h
    obtain ⟨p, hp, rfl⟩ := h
    simpa using hp
  · intro h
    rw [box, Finset.mem_image]
    exact ⟨(β 0, β 1), by simpa using h, toF_eta β⟩

theorem card_box (r : ℕ) : (box r).card = r * r := by
  rw [box, Finset.card_image_of_injective _ toF_injective]; simp

theorem mem_box_of_degree_lt {r : ℕ} {β : Fin 2 →₀ ℕ} (h : β.degree < r) : β ∈ box r := by
  rw [mem_box]; rw [degree_fin_two] at h; omega

def gen (φ : Fin 2 → 𝔸) (p : (Fin 2 →₀ ℕ) × (Fin 2 →₀ ℕ)) : 𝔸 := pw φ p.1 * monomial p.2 1

def W (φ : Fin 2 → 𝔸) (S : Finset (Fin 2 →₀ ℕ)) (n r : ℕ) : Submodule κ 𝔸 :=
  Submodule.span κ (Set.range (fun p : ↥(S ×ˢ box r) => gen φ p.1)) ⊔
    (J (Fin 2) κ n).restrictScalars κ

theorem gen_mem_W (φ : Fin 2 → 𝔸) {S : Finset (Fin 2 →₀ ℕ)} {n r : ℕ} {β α : Fin 2 →₀ ℕ} (hβ : β ∈ S) (hα : α ∈ box r) :
    pw φ β * monomial α (1 : κ) ∈ W φ S n r := by
  apply Submodule.mem_sup_left
  apply Submodule.subset_span
  exact ⟨⟨(β, α), Finset.mem_product.mpr ⟨hβ, hα⟩⟩, rfl⟩

theorem J_mem_W (φ : Fin 2 → 𝔸) {S : Finset (Fin 2 →₀ ℕ)} {n r : ℕ} {f : 𝔸} (hf : f ∈ J (Fin 2) κ n) : f ∈ W φ S n r :=
  Submodule.mem_sup_right hf

theorem phi_mul_mem_W (φ : Fin 2 → 𝔸) {n r : ℕ} (hφJ : ∀ i, φ i ∈ J (Fin 2) κ 1) (i : Fin 2) {u : 𝔸}
    (hu : u ∈ W φ (degLt n) n r) : φ i * u ∈ W φ (degLt (n + 1)) (n + 1) r := by
  have key : W φ (degLt n) n r ≤ (W φ (degLt (n + 1)) (n + 1) r).comap (LinearMap.mulLeft κ (φ i)) := by
    apply sup_le
    · rw [Submodule.span_le]
      rintro x ⟨⟨⟨β, α⟩, hp⟩, rfl⟩
      rw [Finset.mem_product] at hp
      show φ i * (pw φ β * monomial α (1 : κ)) ∈ W φ (degLt (n + 1)) (n + 1) r
      have : φ i * (pw φ β * monomial α (1 : κ)) = pw φ (β + Finsupp.single i 1) * monomial α 1 := by
        rw [pw_add, pw_single]; ring
      rw [this]
      apply gen_mem_W
      · have hβn : β.degree < n := mem_degLt.mp hp.1
        rw [mem_degLt, map_add, Finsupp.degree_single]
        omega
      · exact hp.2
    · intro f hf
      show φ i * f ∈ W φ (degLt (n + 1)) (n + 1) r
      apply J_mem_W
      rw [add_comm]
      exact J_mul_le 1 n (Ideal.mul_mem_mul (hφJ i) hf)
  exact key hu

theorem W_degLt_eq_top (φ : Fin 2 → 𝔸) (hφJ : ∀ i, φ i ∈ J (Fin 2) κ 1) {r : ℕ}
    (hJI : J (Fin 2) κ r ≤ Ideal.span (Set.range φ)) : ∀ n, W φ (degLt n) n r = ⊤
  | 0 => by
    rw [eq_top_iff]
    intro f _
    exact J_mem_W φ (by rw [J_zero]; trivial)
  | n + 1 => by
    have ih := W_degLt_eq_top φ hφJ hJI n
    rw [eq_top_iff]
    intro f _
    set t : 𝔸 := ∑ α ∈ box r, monomial α (coeff α f) with ht
    have hft : f - t ∈ J (Fin 2) κ r := by
      rw [mem_J]
      intro d hd
      rw [map_sub, sub_eq_zero, ht, map_sum]
      simp only [coeff_monomial]
      rw [Finset.sum_ite_eq (box r) d (fun α => coeff α f), if_pos (mem_box_of_degree_lt hd)]
    have hI := hJI hft
    rw [Ideal.mem_span_range_iff_exists_fun] at hI
    obtain ⟨c, hc⟩ := hI
    have hf : f = t + ∑ i, φ i * c i := by
      have : ∑ i, φ i * c i = f - t := by
        rw [← hc]; exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      rw [this]; ring
    rw [hf]
    refine Submodule.add_mem _ ?_ (Submodule.sum_mem _ fun i _ => phi_mul_mem_W φ hφJ i (by rw [ih]; trivial))
    refine Submodule.sum_mem _ fun α hα => ?_
    have : monomial α (coeff α f) = coeff α f • (pw φ 0 * monomial α (1 : κ)) := by
      rw [pw_zero, one_mul, ← (monomial α).map_smul, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (gen_mem_W φ (mem_degLt.mpr (by simp)) hα)

theorem subst_mem_J_of_mem_J (φ : Fin 2 → 𝔸) (hφ0 : ∀ i, constantCoeff (φ i) = 0) {n : ℕ} {G : 𝔸}
    (hG : G ∈ J (Fin 2) κ n) : subst φ G ∈ J (Fin 2) κ n := by
  have hs := hasSubst_of_constantCoeff_zero hφ0
  have h1 : G ∈ XI ^ n := J_le_XI_pow n hG
  have h2 : subst φ G ∈ Ideal.map (substAlgHom hs : 𝔸 →ₐ[κ] 𝔸) (XI ^ n) := by
    rw [← coe_substAlgHom hs]
    exact Ideal.mem_map_of_mem _ h1
  rw [Ideal.map_pow] at h2
  have h3 : Ideal.map (substAlgHom hs : 𝔸 →ₐ[κ] 𝔸) XI ≤ J (Fin 2) κ 1 := by
    rw [XI, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with rfl | rfl <;>
    · show (substAlgHom hs) (X _) ∈ J (Fin 2) κ 1
      rw [coe_substAlgHom, subst_X hs]
      exact mem_J_one_iff.mpr (hφ0 _)
  have := Ideal.pow_right_mono h3 n h2
  exact (J_pow_le 1 n).trans (by simp) this

theorem rel (φ : Fin 2 → 𝔸) (hφ0 : ∀ i, constantCoeff (φ i) = 0) (F : 𝔸) (hF : subst φ F = 0) (n : ℕ) :
    (∑ β ∈ degLt n, C (coeff β F) * pw φ β) ∈ J (Fin 2) κ n := by
  have hs := hasSubst_of_constantCoeff_zero hφ0
  set F₁ : 𝔸 := ∑ β ∈ degLt n, monomial β (coeff β F) with hF₁
  have hF₂ : F - F₁ ∈ J (Fin 2) κ n := by
    rw [mem_J]
    intro d hd
    rw [map_sub, sub_eq_zero, hF₁, map_sum]
    simp only [coeff_monomial]
    rw [Finset.sum_ite_eq (degLt n) d (fun α => coeff α F), if_pos (mem_degLt.mpr hd)]
  have hsum : subst φ F₁ = ∑ β ∈ degLt n, C (coeff β F) * pw φ β := by
    rw [hF₁, ← coe_substAlgHom hs, map_sum]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [coe_substAlgHom, subst_monomial_eq φ hs]
  have : subst φ F = subst φ F₁ + subst φ (F - F₁) := by
    rw [← coe_substAlgHom hs, ← map_add, add_sub_cancel]
  rw [hF, hsum] at this
  have : ∑ β ∈ degLt n, C (coeff β F) * pw φ β = - subst φ (F - F₁) := by
    rw [eq_neg_iff_add_eq_zero, ← this]
  rw [this]
  exact Submodule.neg_mem _ (subst_mem_J_of_mem_J φ hφ0 hF₂)

def lexo : MonomialOrder (Fin 2) := MonomialOrder.lex

theorem toSyn_add_lt_of_lt {a b : Fin 2 →₀ ℕ} (h : lexo.toSyn a < lexo.toSyn b) (c : Fin 2 →₀ ℕ) :
    lexo.toSyn (a + c) < lexo.toSyn (b + c) := by
  rw [map_add, map_add]
  gcongr

def G (β₀ : Fin 2 →₀ ℕ) (n : ℕ) : Finset (Fin 2 →₀ ℕ) := (degLt n).filter (fun β => ¬ β₀ ≤ β)

theorem elim (φ : Fin 2 → 𝔸) (hφJ : ∀ i, φ i ∈ J (Fin 2) κ 1) (F : 𝔸) (β₀ : Fin 2 →₀ ℕ) (hβ₀ : coeff β₀ F ≠ 0)
    (hmin : ∀ β, coeff β F ≠ 0 → ¬ lexo.toSyn β < lexo.toSyn β₀)
    (hrel : ∀ n, (∑ β ∈ degLt n, C (coeff β F) * pw φ β) ∈ J (Fin 2) κ n)
    (n r : ℕ) : ∀ β ∈ degLt n, ∀ α ∈ box r, pw φ β * monomial α (1 : κ) ∈ W φ (G β₀ n) n r := by
  suffices key : ∀ k, ∀ β ∈ degLt n,
      ((degLt n).filter (fun x => lexo.toSyn β < lexo.toSyn x)).card = k →
        ∀ α ∈ box r, pw φ β * monomial α (1 : κ) ∈ W φ (G β₀ n) n r from
    fun β hβ α hα => key _ β hβ rfl α hα
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro β hβ hk α hα
  by_cases hle : β₀ ≤ β
  swap
  · exact gen_mem_W φ (Finset.mem_filter.mpr ⟨hβ, hle⟩) hα

  set γ := β - β₀ with hγ
  have hβγ : β₀ + γ = β := add_tsub_cancel_of_le hle
  have hβ₀n : β₀ ∈ degLt n := by
    rw [mem_degLt] at hβ ⊢
    exact lt_of_le_of_lt (Finsupp.degree_mono hle) hβ
  set c₀ := coeff β₀ F with hc₀
  set u : 𝔸 := C c₀⁻¹ * (pw φ γ * monomial α 1) with hu
  have hJ : (∑ β' ∈ degLt n, C (coeff β' F) * pw φ β') * u ∈ J (Fin 2) κ n :=
    Ideal.mul_mem_right _ _ (hrel n)
  rw [Finset.sum_mul, ← Finset.add_sum_erase _ _ hβ₀n] at hJ
  have e0 : C (coeff β₀ F) * pw φ β₀ * u = pw φ β * monomial α 1 := by
    rw [hu, ← hc₀]
    have hcc : C c₀ * C c₀⁻¹ = (1 : 𝔸) := by
      rw [← map_mul, mul_inv_cancel₀ hβ₀, map_one]
    calc C c₀ * pw φ β₀ * (C c₀⁻¹ * (pw φ γ * monomial α 1))
        = (C c₀ * C c₀⁻¹) * (pw φ β₀ * pw φ γ) * monomial α 1 := by ring
      _ = pw φ β * monomial α 1 := by rw [hcc, one_mul, ← pw_add, hβγ]
  rw [e0] at hJ

  have expr : pw φ β * monomial α (1 : κ) =
      (pw φ β * monomial α 1 + ∑ β' ∈ (degLt n).erase β₀, C (coeff β' F) * pw φ β' * u) -
        ∑ β' ∈ (degLt n).erase β₀, C (coeff β' F) * pw φ β' * u := by ring
  rw [expr]
  refine Submodule.sub_mem _ (J_mem_W φ hJ) (Submodule.sum_mem _ fun β' hβ' => ?_)
  rw [Finset.mem_erase] at hβ'
  by_cases hc : coeff β' F = 0
  · rw [hc, map_zero, zero_mul, zero_mul]; exact Submodule.zero_mem _

  have hlt : lexo.toSyn β₀ < lexo.toSyn β' := by
    rcases lt_or_ge (lexo.toSyn β₀) (lexo.toSyn β') with h | h
    · exact h
    · exfalso
      rcases eq_or_lt_of_le h with h' | h'
      · exact hβ'.1 (lexo.toSyn.injective h').symm.symm
      · exact hmin β' hc h'
  have hterm : C (coeff β' F) * pw φ β' * u = (coeff β' F * c₀⁻¹) • (pw φ (β' + γ) * monomial α 1) := by
    rw [hu, smul_eq_C_mul, map_mul, pw_add]; ring
  rw [hterm]
  refine Submodule.smul_mem _ _ ?_
  have hlt2 : lexo.toSyn β < lexo.toSyn (β' + γ) := by
    rw [← hβγ]; exact toSyn_add_lt_of_lt hlt γ
  by_cases hdeg : (β' + γ).degree < n
  ·
    have hmem : β' + γ ∈ degLt n := mem_degLt.mpr hdeg
    refine ih _ ?_ (β' + γ) hmem rfl α hα
    rw [← hk]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [Finset.mem_filter] at hx ⊢
      exact ⟨hx.1, lt_trans hlt2 hx.2⟩
    · intro heq
      have : β' + γ ∈ (degLt n).filter (fun x => lexo.toSyn (β' + γ) < lexo.toSyn x) := by
        rw [heq, Finset.mem_filter]; exact ⟨hmem, hlt2⟩
      rw [Finset.mem_filter] at this
      exact lt_irrefl _ this.2
  ·
    push Not at hdeg
    apply J_mem_W
    apply Ideal.mul_mem_right
    exact J_antitone hdeg (pw_mem_J hφJ (β' + γ))

theorem W_G_eq_top (φ : Fin 2 → 𝔸) (hφ0 : ∀ i, constantCoeff (φ i) = 0) {r : ℕ}
    (hJI : J (Fin 2) κ r ≤ Ideal.span (Set.range φ)) (F : 𝔸) (β₀ : Fin 2 →₀ ℕ)
    (hβ₀ : coeff β₀ F ≠ 0) (hmin : ∀ β, coeff β F ≠ 0 → ¬ lexo.toSyn β < lexo.toSyn β₀)
    (hF : subst φ F = 0) (n : ℕ) : W φ (G β₀ n) n r = ⊤ := by
  have hφJ : ∀ i, φ i ∈ J (Fin 2) κ 1 := fun i => mem_J_one_iff.mpr (hφ0 i)
  rw [eq_top_iff, ← W_degLt_eq_top φ hφJ hJI n]
  apply sup_le _ le_sup_right
  rw [Submodule.span_le]
  rintro _ ⟨⟨⟨β, α⟩, hp⟩, rfl⟩
  rw [Finset.mem_product] at hp
  exact elim φ hφJ F β₀ hβ₀ hmin (rel φ hφ0 F hF) n r β hp.1 α hp.2

theorem card_G_le (β₀ : Fin 2 →₀ ℕ) (n : ℕ) : (G β₀ n).card ≤ (β₀ 0 + β₀ 1) * n := by
  classical
  set a := β₀ 0
  set b := β₀ 1
  have hsub : G β₀ n ⊆ ((Finset.range a ×ˢ Finset.range n) ∪ (Finset.range n ×ˢ Finset.range b)).image toF := by
    intro β hβ
    rw [G, Finset.mem_filter, mem_degLt, degree_fin_two, Finsupp.le_def] at hβ
    rw [Finset.mem_image]
    refine ⟨(β 0, β 1), ?_, toF_eta β⟩
    have : β 0 < a ∨ β 1 < b := by
      by_contra h
      push Not at h
      exact hβ.2 (fun i => by fin_cases i <;> simp [a, b] at h ⊢ <;> omega)
    simp only [Finset.mem_union, Finset.mem_product, Finset.mem_range]
    omega
  calc (G β₀ n).card ≤ (((Finset.range a ×ˢ Finset.range n) ∪ (Finset.range n ×ˢ Finset.range b)).image toF).card :=
        Finset.card_le_card hsub
    _ ≤ ((Finset.range a ×ˢ Finset.range n) ∪ (Finset.range n ×ˢ Finset.range b)).card := Finset.card_image_le
    _ ≤ (Finset.range a ×ˢ Finset.range n).card + (Finset.range n ×ˢ Finset.range b).card := Finset.card_union_le _ _
    _ = (β₀ 0 + β₀ 1) * n := by simp [a, b]; ring

def window (n' : ℕ) : 𝔸 →ₗ[κ] (Fin n' × Fin n' → κ) :=
  LinearMap.pi fun p => coeff (toF (p.1.val, p.2.val))

theorem window_surjective (n' : ℕ) : Function.Surjective (window (κ := κ) n') := by
  intro v
  let f : 𝔸 := fun d => if h : d 0 < n' ∧ d 1 < n' then v (⟨d 0, h.1⟩, ⟨d 1, h.2⟩) else 0
  refine ⟨f, ?_⟩
  funext p
  show coeff (toF (p.1.val, p.2.val)) f = v p
  show (if h : (toF (p.1.val, p.2.val)) 0 < n' ∧ (toF (p.1.val, p.2.val)) 1 < n' then
      v (⟨(toF (p.1.val, p.2.val)) 0, h.1⟩, ⟨(toF (p.1.val, p.2.val)) 1, h.2⟩) else 0) = v p
  simp only [toF_zero, toF_one]
  rw [dif_pos ⟨p.1.isLt, p.2.isLt⟩]

theorem J_le_ker_window (n' : ℕ) :
    (J (Fin 2) κ (2 * n')).restrictScalars κ ≤ LinearMap.ker (window (κ := κ) n') := by
  intro f hf
  rw [LinearMap.mem_ker]
  funext p
  show coeff (toF (p.1.val, p.2.val)) f = 0
  rw [Submodule.restrictScalars_mem, mem_J] at hf
  apply hf
  rw [degree_toF]
  have := p.1.isLt; have := p.2.isLt
  omega

theorem field_case (φ : Fin 2 → 𝔸) (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (hfin : Module.Finite κ (𝔸 ⧸ Ideal.span (Set.range φ))) (F : 𝔸) (hF : subst φ F = 0) : F = 0 := by
  by_contra hne
  obtain ⟨r, hr⟩ := exists_J_le_I hφ0 hfin

  have hS : {β : Fin 2 →₀ ℕ | coeff β F ≠ 0}.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    apply hne
    ext β
    have : β ∉ {β : Fin 2 →₀ ℕ | coeff β F ≠ 0} := by rw [h]; exact Set.notMem_empty _
    simpa using this
  have hwf : WellFounded (fun a b : Fin 2 →₀ ℕ => lexo.toSyn a < lexo.toSyn b) :=
    InvImage.wf _ lexo.wf.wf
  set β₀ := hwf.min _ hS with hβ₀def
  have hβ₀ : coeff β₀ F ≠ 0 := hwf.min_mem _ hS
  have hmin : ∀ β, coeff β F ≠ 0 → ¬ lexo.toSyn β < lexo.toSyn β₀ :=
    fun β hβ => hwf.not_lt_min _ hβ

  set m := β₀ 0 + β₀ 1 with hm
  set n' := 2 * m * (r * r) + 1 with hn'
  set n := 2 * n' with hn
  have htop := W_G_eq_top φ hφ0 hr F β₀ hβ₀ hmin hF n

  set Jn : Submodule κ 𝔸 := (J (Fin 2) κ n).restrictScalars κ with hJn
  have hspan : Submodule.span κ (Set.range (fun p : ↥(G β₀ n ×ˢ box r) => Jn.mkQ (gen φ p.1))) = ⊤ := by
    have : (fun p : ↥(G β₀ n ×ˢ box r) => Jn.mkQ (gen φ p.1)) = Jn.mkQ ∘ (fun p => gen φ p.1) := rfl
    rw [this, Set.range_comp, ← Submodule.map_span, Submodule.map_mkQ_eq_top, sup_comm]
    exact htop
  haveI hQfin : Module.Finite κ (𝔸 ⧸ Jn) := by
    rw [Module.finite_def, Submodule.fg_def]
    exact ⟨_, Set.finite_range _, hspan⟩

  have hup : Module.finrank κ (𝔸 ⧸ Jn) ≤ (G β₀ n ×ˢ box r).card := by
    rw [← finrank_top, ← hspan]
    exact (finrank_range_le_card _).trans (by simp [Fintype.card_coe])

  have hlow : n' * n' ≤ Module.finrank κ (𝔸 ⧸ Jn) := by
    have hker : Jn ≤ LinearMap.ker (window n') := J_le_ker_window n'
    have hL : LinearMap.range (Jn.liftQ (window n') hker) = ⊤ := by
      rw [Submodule.range_liftQ, LinearMap.range_eq_top]; exact window_surjective n'
    have := LinearMap.finrank_range_le (Jn.liftQ (window n') hker)
    rw [hL, finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin] at this
    exact this

  have hG := card_G_le β₀ n
  have h1 : n' * n' ≤ m * n * (r * r) := by
    calc n' * n' ≤ (G β₀ n ×ˢ box r).card := hlow.trans hup
      _ = (G β₀ n).card * (r * r) := by rw [Finset.card_product, card_box]
      _ ≤ m * n * (r * r) := Nat.mul_le_mul_right _ hG
  have e : m * n * (r * r) = (2 * m * (r * r)) * n' := by rw [hn]; ring
  rw [e] at h1
  have h2 : n' ≤ 2 * m * (r * r) := Nat.le_of_mul_le_mul_right h1 (by rw [hn']; omega)
  rw [hn'] at h2
  omega

end fieldcase

end SubstInj
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_field.SubstInj"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_field.SubstInj"

theorem solution
    {κ : Type u} [Field κ] (φ : Series κ) (hφ0 : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0)
    (hφ : Module.Finite κ (FormalODModule.KerAlgebra φ))
    (f g : MvPowerSeries (Fin 2) κ) (h : MvPowerSeries.subst φ f = MvPowerSeries.subst φ g) : f = g := by
  have hs := MvPowerSeries.hasSubst_of_constantCoeff_zero hφ0
  have h0 : MvPowerSeries.subst φ (f - g) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hs, map_sub, MvPowerSeries.coe_substAlgHom, h, sub_self]
  exact sub_eq_zero.mp (SubstInj.field_case φ hφ0 hφ (f - g) h0)

end S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_field
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_subst_injective_of_finite_kerAlgebra_of_field (solution)
