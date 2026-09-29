-- Prove2me | solution 1 for DrinfeldCurve.LocalChart.exists_ringHom_forall_apply_eq_mk_C_of_apply_eq_mk_C_of_forall_pow_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/7d735e1c-45d8-55ea-b875-d6708bd5ebba

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Theorems.Thm_MvPowerSeries_isNoetherianRing_fin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DrinfeldCurve_LocalChart_exists_ringHom_forall_apply_eq_mk_C_of_apply_eq_mk_C_of_forall_pow_pow_eq

set_option autoImplicit false

open IsLocalRing

namespace ConstRigidAux

open MvPowerSeries

section degree

variable {W : Type*} [CommRing W]

abbrev tdeg (e : Fin 2 →₀ ℕ) : ℕ := e 0 + e 1

lemma tdeg_add (e₁ e₂ : Fin 2 →₀ ℕ) : tdeg (e₁ + e₂) = tdeg e₁ + tdeg e₂ := by
  simp only [tdeg, Finsupp.add_apply]; omega

lemma tdeg_eq_zero_iff (e : Fin 2 →₀ ℕ) : tdeg e = 0 ↔ e = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i <;> simp only [tdeg] at h <;> simp <;> omega
  · rintro rfl; simp [tdeg]

noncomputable abbrev 𝔫 (W : Type*) [CommRing W] : Ideal (MvPowerSeries (Fin 2) W) :=
  Ideal.span {(X 0 : MvPowerSeries (Fin 2) W), X 1}

lemma coeff_zero_of_mem_𝔫 {φ : MvPowerSeries (Fin 2) W} (hφ : φ ∈ 𝔫 W) :
    coeff (0 : Fin 2 →₀ ℕ) φ = 0 := by
  rw [Ideal.mem_span_pair] at hφ
  obtain ⟨a, b, rfl⟩ := hφ
  classical
  simp [coeff_zero_eq_constantCoeff_apply, constantCoeff_X]

lemma coeff_eq_zero_of_mem_pow (n : ℕ) {φ : MvPowerSeries (Fin 2) W} (hφ : φ ∈ 𝔫 W ^ n)
    (e : Fin 2 →₀ ℕ) (he : tdeg e < n) : coeff e φ = 0 := by
  classical
  induction n generalizing φ e with
  | zero => omega
  | succ n ih =>
    rw [pow_succ] at hφ
    refine Submodule.mul_induction_on hφ ?_ ?_
    · intro a ha b hb
      rw [coeff_mul]
      apply Finset.sum_eq_zero
      rintro ⟨e₁, e₂⟩ h12
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at h12
      by_cases h1 : tdeg e₁ < n
      · rw [ih ha e₁ h1, zero_mul]
      · have : tdeg e₂ = 0 := by
          have := tdeg_add e₁ e₂; rw [h12] at this; omega
        rw [(tdeg_eq_zero_iff e₂).mp this, coeff_zero_of_mem_𝔫 hb, mul_zero]
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]

lemma constantCoeff_eq_zero_of_mem_pow {n : ℕ} (hn : 0 < n) {φ : MvPowerSeries (Fin 2) W}
    (hφ : φ ∈ 𝔫 W ^ n) : constantCoeff φ = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact coeff_eq_zero_of_mem_pow n hφ 0 (by simp [tdeg]; exact hn)

end degree

section drinfeld

variable (q : ℕ) [Fact q.Prime] {W : Type} [CommRing W]

lemma constantCoeff_drinfeldForm : constantCoeff (DrinfeldCurve.LocalChart.drinfeldForm q W) = 0 := by
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  simp [DrinfeldCurve.LocalChart.drinfeldForm, constantCoeff_X, hq]

lemma coeff_drinfeldForm_key :
    coeff (Finsupp.single 0 1 + Finsupp.single 1 q) (DrinfeldCurve.LocalChart.drinfeldForm q W) = 1 := by
  classical
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  have h1 : (X 0 : MvPowerSeries (Fin 2) W) * X 1 ^ q =
      monomial (Finsupp.single 0 1 + Finsupp.single 1 q) 1 := by
    rw [X_def, X_pow_eq, monomial_mul_monomial, one_mul]
  have h2 : (X 0 : MvPowerSeries (Fin 2) W) ^ q * X 1 =
      monomial (Finsupp.single 0 q + Finsupp.single 1 1) 1 := by
    rw [X_pow_eq, X_def, monomial_mul_monomial, one_mul]
  have hne : (Finsupp.single 0 q + Finsupp.single 1 1 : Fin 2 →₀ ℕ) ≠
      Finsupp.single 0 1 + Finsupp.single 1 q := by
    intro h
    have := congrArg (fun e : Fin 2 →₀ ℕ => e 0) h
    simp at this
    omega
  rw [DrinfeldCurve.LocalChart.drinfeldForm, h1, h2, map_sub, coeff_monomial_same,
    coeff_monomial_ne hne.symm, sub_zero]

variable {q}

lemma constantCoeff_eq_zero_of_sub_drinfeldForm_mem {f : MvPowerSeries (Fin 2) W}
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈ 𝔫 W ^ (q + 2)) :
    constantCoeff f = 0 := by
  have h := constantCoeff_eq_zero_of_mem_pow (by omega) hf
  rw [map_sub, constantCoeff_drinfeldForm, sub_zero] at h
  exact h

lemma coeff_key_eq_one_of_sub_drinfeldForm_mem {f : MvPowerSeries (Fin 2) W}
    (hf : f - DrinfeldCurve.LocalChart.drinfeldForm q W ∈ 𝔫 W ^ (q + 2)) :
    coeff (Finsupp.single 0 1 + Finsupp.single 1 q) f = 1 := by
  have h := coeff_eq_zero_of_mem_pow (q + 2) hf (Finsupp.single 0 1 + Finsupp.single 1 q)
    (by simp [tdeg]; omega)
  rw [map_sub, coeff_drinfeldForm_key, sub_eq_zero] at h
  exact h

end drinfeld

end ConstRigidAux

namespace ConstRigidAux

open MvPowerSeries

section chart

variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  (π : W) (hπ : maximalIdeal W = Ideal.span {π})
  (g : MvPowerSeries (Fin 2) W)

lemma isUnit_mk_iff (hg : constantCoeff g ∈ maximalIdeal W) (φ : MvPowerSeries (Fin 2) W) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {g}) φ) ↔ IsUnit (constantCoeff φ) := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := h.exists_right_inv
    obtain ⟨ψ, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← (Ideal.Quotient.mk (Ideal.span {g})).map_one, Ideal.Quotient.eq,
      Ideal.mem_span_singleton] at hy
    obtain ⟨h, hh⟩ := hy
    have hc := congrArg constantCoeff hh
    simp only [map_sub, map_mul, map_one] at hc

    have hmem : constantCoeff φ * constantCoeff ψ - 1 ∈ maximalIdeal W := by
      rw [hc]; exact Ideal.mul_mem_right _ _ hg
    by_contra hφ
    have : constantCoeff φ * constantCoeff ψ ∈ maximalIdeal W :=
      Ideal.mul_mem_right _ _ ((mem_maximalIdeal _).mpr hφ)
    have h1 : (1 : W) ∈ maximalIdeal W := by
      have := Ideal.sub_mem _ this hmem
      rwa [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal W).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)
  · intro h
    exact (isUnit_iff_constantCoeff.mpr h).map _

lemma span_ne_top (hg : constantCoeff g ∈ maximalIdeal W) : Ideal.span {g} ≠ ⊤ := by
  intro h
  have : IsUnit g := Ideal.span_singleton_eq_top.mp h
  have := isUnit_constantCoeff g this
  exact (mem_maximalIdeal _).mp hg this

lemma isLocalRing_quotient (hg : constantCoeff g ∈ maximalIdeal W) :
    IsLocalRing (MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}) :=
  haveI : Nontrivial (MvPowerSeries (Fin 2) W ⧸ Ideal.span {g}) :=
    Ideal.Quotient.nontrivial_iff.mpr (span_ne_top g hg)
  IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {g})) Ideal.Quotient.mk_surjective

end chart

end ConstRigidAux

namespace ConstRigidAux

open MvPowerSeries

section dvr

variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]

lemma eq_zero_of_forall_pow_dvd {π : W} (hπ : Irreducible π) {a : W} (h : ∀ n : ℕ, π ^ n ∣ a) :
    a = 0 := by
  by_contra ha
  have hfin : IsDiscreteValuationRing.addVal W a ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hfin
  have := (IsDiscreteValuationRing.addVal_le_iff_dvd).mpr (h (m + 1))
  rw [IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hπ, ← hm,
    nsmul_eq_mul, mul_one] at this
  norm_cast at this
  omega

lemma exists_eq_C_mul_of_map_residue_eq_zero {π : W} (hπ : maximalIdeal W = Ideal.span {π})
    {φ : MvPowerSeries (Fin 2) W} (h : MvPowerSeries.map (residue W) φ = 0) :
    ∃ φ' : MvPowerSeries (Fin 2) W, φ = C π * φ' := by
  have hc : ∀ e : Fin 2 →₀ ℕ, ∃ c : W, coeff e φ = π * c := by
    intro e
    have h1 : residue W (coeff e φ) = 0 := by
      rw [← coeff_map, h]; simp
    rw [residue_eq_zero_iff, hπ, Ideal.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, hc⟩
  refine ⟨fun e => (hc e).choose, ?_⟩
  ext e
  rw [coeff_C_mul, (hc e).choose_spec]
  rfl

lemma map_residue_C_eq_zero_of_mem {c : W} (hc : c ∈ maximalIdeal W) :
    MvPowerSeries.map (residue W) (C c : MvPowerSeries (Fin 2) W) = 0 := by
  rw [map_C, (residue_eq_zero_iff c).mpr hc, map_zero]

end dvr

section purity

variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
  (π : W) (hπ : maximalIdeal W = Ideal.span {π})
  (c : W) (hc : c ∈ maximalIdeal W)
  (f u v : MvPowerSeries (Fin 2) W)
  (hf0 : constantCoeff f = 0) (hfred : MvPowerSeries.map (residue W) f ≠ 0) (hu : IsUnit u)

include hπ hc hf0 hfred hu

lemma pow_dvd_of_C_eq (n : ℕ) :
    ∀ (a : W) (s h : MvPowerSeries (Fin 2) W), C a = C π ^ n * s + (C c * v - f * u) * h →
      π ^ n ∣ a := by
  have hπirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  have hπ0 : (C π : MvPowerSeries (Fin 2) W) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    rw [constantCoeff_C, map_zero] at this
    exact hπirr.ne_zero this
  induction n with
  | zero => intro a _ _ _; exact ⟨a, by simp⟩
  | succ n ih =>
    intro a s h heq

    have hred := congrArg (MvPowerSeries.map (residue W)) heq
    have hπmem : π ∈ maximalIdeal W := by rw [hπ]; exact Ideal.mem_span_singleton_self π
    simp only [map_add, map_mul, map_sub, map_pow] at hred
    rw [map_residue_C_eq_zero_of_mem hπmem, map_residue_C_eq_zero_of_mem hc, map_C,
      zero_pow (Nat.succ_ne_zero n), zero_mul, zero_add, zero_mul, zero_sub, neg_mul] at hred

    have ha0 : residue W a = 0 := by
      have := congrArg constantCoeff hred
      rw [constantCoeff_C] at this
      rw [this, map_neg, map_mul, map_mul, constantCoeff_map, hf0, map_zero, zero_mul, zero_mul,
        neg_zero]
    have hh0 : MvPowerSeries.map (residue W) h = 0 := by
      rw [ha0, map_zero, eq_comm, neg_eq_zero, mul_eq_zero] at hred
      rcases hred with hfu | hh
      · exfalso
        rcases mul_eq_zero.mp hfu with hf | hu0
        · exact hfred hf
        · exact (hu.map (MvPowerSeries.map (residue W))).ne_zero hu0
      · exact hh
    obtain ⟨a', rfl⟩ : ∃ a', a = π * a' := by
      have : a ∈ Ideal.span {π} := by rw [← hπ]; exact (residue_eq_zero_iff a).mp ha0
      exact Ideal.mem_span_singleton'.mp this |>.imp fun _ h => by rw [mul_comm]; exact h.symm
    obtain ⟨h', rfl⟩ := exists_eq_C_mul_of_map_residue_eq_zero hπ hh0

    have heq' : C a' = C π ^ n * s + (C c * v - f * u) * h' := by
      apply mul_left_cancel₀ hπ0
      rw [← map_mul, heq]
      ring
    obtain ⟨b, hb⟩ := ih a' s h' heq'
    exact ⟨b, by rw [hb]; ring⟩

lemma eq_zero_of_C_mem (a : W) (h : (C a : MvPowerSeries (Fin 2) W) ∈ Ideal.span {C c * v - f * u}) :
    a = 0 := by
  have hπirr : Irreducible π := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mpr hπ
  rw [Ideal.mem_span_singleton'] at h
  obtain ⟨k, hk⟩ := h
  apply eq_zero_of_forall_pow_dvd hπirr
  intro n
  exact pow_dvd_of_C_eq π hπ c hc f u v hf0 hfred hu n a 0 k (by rw [← hk]; ring)

end purity

end ConstRigidAux

namespace ConstRigidAux

open MvPowerSeries

section localfacts

lemma isUnit_natCast_of_not_dvd {R : Type*} [CommRing R] [IsLocalRing R] {q : ℕ} (hq : q.Prime)
    (hqR : (q : R) ∈ maximalIdeal R) {N : ℕ} (hN : ¬ q ∣ N) : IsUnit (N : R) := by
  have hcop : IsCoprime (q : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.mpr (hq.coprime_iff_not_dvd.mpr hN)
  have hcopR : IsCoprime (q : R) (N : R) := by
    have := hcop.map (Int.castRingHom R)
    simpa using this
  by_contra hNu
  obtain ⟨a, b, hab⟩ := hcopR
  have : (1 : R) ∈ maximalIdeal R := by
    rw [← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hqR)
      (Ideal.mul_mem_left _ _ ((mem_maximalIdeal _).mpr hNu))
  exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

lemma eq_one_of_pow_eq_one_of_sub_mem {R : Type*} [CommRing R] [IsLocalRing R] {N : ℕ}
    (hN : IsUnit (N : R)) {z : R} (hz : z ^ N = 1) (hz1 : z - 1 ∈ maximalIdeal R) : z = 1 := by
  have hgeom := geom_sum_mul z N
  rw [hz, sub_self] at hgeom

  have hsum : (∑ i ∈ Finset.range N, z ^ i) - (N : R) ∈ maximalIdeal R := by
    have : (∑ i ∈ Finset.range N, z ^ i) - (N : R) = ∑ i ∈ Finset.range N, (z ^ i - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    have h := geom_sum_mul z i
    rw [← h]
    exact Ideal.mul_mem_left _ _ hz1
  have hunit : IsUnit (∑ i ∈ Finset.range N, z ^ i) := by
    by_contra hnu
    have h1 := Ideal.sub_mem _ ((mem_maximalIdeal _).mpr hnu) hsum
    rw [sub_sub_cancel] at h1
    exact (mem_maximalIdeal _).mp h1 hN
  have := hunit.mul_right_eq_zero.mp hgeom
  rwa [sub_eq_zero] at this

end localfacts

section main

variable (q : ℕ) [Fact q.Prime]
  (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁] [IsAdicComplete (maximalIdeal W₁) W₁]
  (π₁ : W₁) (hπ₁ : maximalIdeal W₁ = Ideal.span {π₁})
  (halg : ∀ x : ResidueField W₁, ∃ n : ℕ, 1 ≤ n ∧ x ^ (q ^ n) = x)
  {W₂ : Type} [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [IsAdicComplete (maximalIdeal W₂) W₂]
  (π₂ : W₂) (hπ₂ : maximalIdeal W₂ = Ideal.span {π₂}) (hq₂ : (q : W₂) ∈ maximalIdeal W₂)
  (f₂ u₂ v₂ : MvPowerSeries (Fin 2) W₂) (hu₂ : IsUnit u₂) (hv₂ : IsUnit v₂)
  (hf₂ : f₂ - DrinfeldCurve.LocalChart.drinfeldForm q W₂ ∈
    (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ (q + 2))
  (θ : W₁ →+* MvPowerSeries (Fin 2) W₂ ⧸ Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂})
  (hθ : θ π₁ = Ideal.Quotient.mk _ (MvPowerSeries.C π₂))

local notation "gg" => (MvPowerSeries.C π₂ * v₂ - f₂ * u₂ : MvPowerSeries (Fin 2) W₂)

local notation "SS" => (MvPowerSeries (Fin 2) W₂ ⧸ Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂})

local notation "mkS" => (Ideal.Quotient.mk (Ideal.span {(MvPowerSeries.C π₂ * v₂ - f₂ * u₂ : MvPowerSeries (Fin 2) W₂)}))

noncomputable def iota : W₂ →+* SS := RingHom.comp mkS MvPowerSeries.C

lemma iota_apply (a : W₂) : iota π₂ f₂ u₂ v₂ a = mkS (C a) := rfl

include hπ₂ in
lemma pi2_mem : π₂ ∈ maximalIdeal W₂ := by rw [hπ₂]; exact Ideal.mem_span_singleton_self π₂

include hf₂ in
lemma f2_constantCoeff : constantCoeff f₂ = 0 := constantCoeff_eq_zero_of_sub_drinfeldForm_mem hf₂

include hf₂ in
lemma f2_red_ne_zero : MvPowerSeries.map (residue W₂) f₂ ≠ 0 := by
  intro h
  have := congrArg (coeff (Finsupp.single 0 1 + Finsupp.single 1 q)) h
  rw [coeff_map, coeff_key_eq_one_of_sub_drinfeldForm_mem hf₂, map_one, map_zero] at this
  exact one_ne_zero this

include hπ₂ hf₂ in
lemma g_constantCoeff_mem : constantCoeff gg ∈ maximalIdeal W₂ := by
  simp only [map_sub, map_mul, constantCoeff_C, f2_constantCoeff q f₂ hf₂, zero_mul, sub_zero]
  exact Ideal.mul_mem_right _ _ (pi2_mem π₂ hπ₂)

include hπ₂ hf₂ in
lemma isUnit_iota_iff (a : W₂) : IsUnit (iota π₂ f₂ u₂ v₂ a) ↔ IsUnit a := by
  rw [iota_apply, isUnit_mk_iff gg (g_constantCoeff_mem q π₂ hπ₂ f₂ u₂ v₂ hf₂), constantCoeff_C]

include hπ₂ hf₂ hu₂ in
lemma iota_injective : Function.Injective (iota π₂ f₂ u₂ v₂) := by
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro a ha
  rw [iota_apply, Ideal.Quotient.eq_zero_iff_mem] at ha
  exact eq_zero_of_C_mem π₂ hπ₂ π₂ (pi2_mem π₂ hπ₂) f₂ u₂ v₂ (f2_constantCoeff q f₂ hf₂)
    (f2_red_ne_zero q f₂ hf₂) hu₂ a ha

include hπ₂ hf₂ hu₂ in

lemma pow_dvd_of_iota_eq (n : ℕ) (a : W₂) (s : SS) (h : iota π₂ f₂ u₂ v₂ a = iota π₂ f₂ u₂ v₂ π₂ ^ n * s) : π₂ ^ n ∣ a := by
  obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s
  rw [iota_apply, iota_apply, ← map_pow, ← map_mul, Ideal.Quotient.eq,
    Ideal.mem_span_singleton'] at h
  obtain ⟨k, hk⟩ := h
  exact pow_dvd_of_C_eq π₂ hπ₂ π₂ (pi2_mem π₂ hπ₂) f₂ u₂ v₂ (f2_constantCoeff q f₂ hf₂)
    (f2_red_ne_zero q f₂ hf₂) hu₂ n a s' k (by linear_combination (-1 : MvPowerSeries (Fin 2) W₂) * hk)

end main

end ConstRigidAux

namespace ConstRigidAux

open MvPowerSeries

section main2

variable (q : ℕ) [Fact q.Prime]
  (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁] [IsAdicComplete (maximalIdeal W₁) W₁]
  (π₁ : W₁) (hπ₁ : maximalIdeal W₁ = Ideal.span {π₁})
  (halg : ∀ x : ResidueField W₁, ∃ n : ℕ, 1 ≤ n ∧ x ^ (q ^ n) = x)
  {W₂ : Type} [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [IsAdicComplete (maximalIdeal W₂) W₂]
  (π₂ : W₂) (hπ₂ : maximalIdeal W₂ = Ideal.span {π₂}) (hq₂ : (q : W₂) ∈ maximalIdeal W₂)
  (f₂ u₂ v₂ : MvPowerSeries (Fin 2) W₂) (hu₂ : IsUnit u₂) (hv₂ : IsUnit v₂)
  (hf₂ : f₂ - DrinfeldCurve.LocalChart.drinfeldForm q W₂ ∈
    (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ (q + 2))
  (θ : W₁ →+* MvPowerSeries (Fin 2) W₂ ⧸ Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂})
  (hθ : θ π₁ = Ideal.Quotient.mk _ (MvPowerSeries.C π₂))

local notation "SS" => (MvPowerSeries (Fin 2) W₂ ⧸ Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂})
local notation "mkS" => (Ideal.Quotient.mk (Ideal.span {(MvPowerSeries.C π₂ * v₂ - f₂ * u₂ : MvPowerSeries (Fin 2) W₂)}))

include hπ₂ hf₂ in
lemma isLocalRing_S : IsLocalRing SS :=
  isLocalRing_quotient _ (g_constantCoeff_mem q π₂ hπ₂ f₂ u₂ v₂ hf₂)

include hπ₂ hf₂ in
lemma nontrivial_S : Nontrivial SS :=
  Ideal.Quotient.nontrivial_iff.mpr (span_ne_top _ (g_constantCoeff_mem q π₂ hπ₂ f₂ u₂ v₂ hf₂))

include hπ₂ hf₂ in

lemma mk_mem_maximalIdeal_iff (φ : MvPowerSeries (Fin 2) W₂) :
    letI := isLocalRing_S q π₂ hπ₂ f₂ u₂ v₂ hf₂
    mkS φ ∈ maximalIdeal SS ↔ constantCoeff φ ∈ maximalIdeal W₂ := by
  letI := isLocalRing_S q π₂ hπ₂ f₂ u₂ v₂ hf₂
  rw [mem_maximalIdeal, mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff,
    isUnit_mk_iff _ (g_constantCoeff_mem q π₂ hπ₂ f₂ u₂ v₂ hf₂)]

include hπ₂ hf₂ in
lemma iota_mem_maximalIdeal_iff (a : W₂) :
    letI := isLocalRing_S q π₂ hπ₂ f₂ u₂ v₂ hf₂
    iota π₂ f₂ u₂ v₂ a ∈ maximalIdeal SS ↔ a ∈ maximalIdeal W₂ := by
  rw [iota_apply]
  have := mk_mem_maximalIdeal_iff q π₂ hπ₂ f₂ u₂ v₂ hf₂ (C a)
  rwa [constantCoeff_C] at this

include hπ₂ hf₂ hq₂ in

lemma isUnit_natCast_S {N : ℕ} (hN : ¬ q ∣ N) : IsUnit ((N : ℕ) : SS) := by
  have h := isUnit_natCast_of_not_dvd (Fact.out : q.Prime) hq₂ hN
  have := h.map (iota π₂ f₂ u₂ v₂)
  rwa [map_natCast] at this

include hπ₂ hf₂ hq₂ hθ in

lemma q_mem_maximalIdeal_W₁ : (q : W₁) ∈ maximalIdeal W₁ := by
  letI := isLocalRing_S q π₂ hπ₂ f₂ u₂ v₂ hf₂
  by_contra h
  have hu : IsUnit (q : W₁) := not_not.mp (mt (mem_maximalIdeal _).mpr h)
  have h1 : IsUnit ((q : ℕ) : SS) := by
    have := hu.map θ
    rwa [map_natCast] at this
  have h2 : ((q : ℕ) : SS) = iota π₂ f₂ u₂ v₂ (q : W₂) := by rw [map_natCast]
  rw [h2, isUnit_iota_iff q π₂ hπ₂ f₂ u₂ v₂ hf₂] at h1
  exact (mem_maximalIdeal _).mp hq₂ h1

include hπ₂ hf₂ hq₂ hθ halg in

lemma exists_digit (w : W₁) :
    ∃ t : W₁, (t = 0 ∨ ∃ N : ℕ, 0 < N ∧ ¬ q ∣ N ∧ t ^ N = 1) ∧ w - t ∈ maximalIdeal W₁ := by
  have hqp : q.Prime := Fact.out
  obtain ⟨n, hn, hx⟩ := halg (residue W₁ w)
  by_cases hw : residue W₁ w = 0
  · exact ⟨0, Or.inl rfl, by rw [sub_zero]; exact (residue_eq_zero_iff w).mp hw⟩
  · set N : ℕ := q ^ n - 1 with hN
    have hqn : 2 ≤ q ^ n := by
      calc 2 ≤ q := hqp.two_le
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ n := Nat.pow_le_pow_right hqp.pos hn
    have hNpos : 0 < N := by omega
    have hNdvd : ¬ q ∣ N := by
      intro h
      have h1 : q ∣ q ^ n := dvd_pow_self q (by omega)
      have h2 : q ∣ q ^ n - N := Nat.dvd_sub h1 h
      have : q ^ n - N = 1 := by omega
      rw [this] at h2
      exact hqp.one_lt.ne' (Nat.dvd_one.mp h2)
    have hxN : residue W₁ w ^ N = 1 := by
      have : residue W₁ w ^ N * residue W₁ w = residue W₁ w := by
        rw [← pow_succ, hN, Nat.sub_add_cancel (by omega), hx]
      exact (mul_eq_right₀ hw).mp this

    have hNunit : IsUnit ((N : ℕ) : W₁) :=
      isUnit_natCast_of_not_dvd hqp (q_mem_maximalIdeal_W₁ q W₁ π₁ π₂ hπ₂ hq₂ f₂ u₂ v₂ hf₂ θ hθ) hNdvd
    have hwunit : IsUnit w := by
      by_contra h; exact hw ((residue_eq_zero_iff w).mpr ((mem_maximalIdeal _).mpr h))
    have hmonic : (Polynomial.X ^ N - 1 : Polynomial W₁).Monic := by
      have := Polynomial.monic_X_pow_sub_C (1 : W₁) (Nat.pos_iff_ne_zero.mp hNpos)
      rwa [map_one] at this
    have heval : (Polynomial.X ^ N - 1 : Polynomial W₁).eval w ∈ maximalIdeal W₁ := by
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
        ← residue_eq_zero_iff, map_sub, map_pow, map_one, hxN, sub_self]
    have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal W₁)
        ((Polynomial.X ^ N - 1 : Polynomial W₁).derivative.eval w)) := by
      rw [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero, Polynomial.derivative_X_pow,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
      exact ((hNunit.mul (hwunit.pow _))).map _
    obtain ⟨t, ht, htw⟩ := HenselianRing.is_henselian (I := maximalIdeal W₁)
      (Polynomial.X ^ N - 1) hmonic w heval hderiv
    refine ⟨t, Or.inr ⟨N, hNpos, hNdvd, ?_⟩, ?_⟩
    · rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_one, sub_eq_zero] at ht
      exact ht
    · have := (maximalIdeal W₁).neg_mem htw
      rwa [neg_sub] at this

include hπ₂ hf₂ hq₂ in

lemma exists_eq_iota_of_pow_eq_one {N : ℕ} (hNpos : 0 < N) (hN : ¬ q ∣ N) (ζ : SS) (hζ : ζ ^ N = 1) :
    ∃ c : W₂, ζ = iota π₂ f₂ u₂ v₂ c := by
  have hqp : q.Prime := Fact.out
  letI := isLocalRing_S q π₂ hπ₂ f₂ u₂ v₂ hf₂

  obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective ζ
  set c₀ := constantCoeff φ with hc₀
  have h0 : mkS φ - iota π₂ f₂ u₂ v₂ c₀ ∈ maximalIdeal SS := by
    rw [iota_apply, ← map_sub, mk_mem_maximalIdeal_iff q π₂ hπ₂ f₂ u₂ v₂ hf₂, map_sub,
      constantCoeff_C, hc₀, sub_self]
    exact (maximalIdeal W₂).zero_mem

  have h1 : c₀ ^ N - 1 ∈ maximalIdeal W₂ := by
    rw [← iota_mem_maximalIdeal_iff q π₂ hπ₂ f₂ u₂ v₂ hf₂, map_sub, map_pow, map_one]
    have : iota π₂ f₂ u₂ v₂ c₀ ^ N - mkS φ ^ N ∈ maximalIdeal SS := by
      rw [← Ideal.Quotient.eq, map_pow, map_pow]
      congr 1
      rw [eq_comm, Ideal.Quotient.eq]
      exact h0
    rwa [hζ] at this
  have hc₀unit : IsUnit c₀ := by
    by_contra h
    have : c₀ ^ N ∈ maximalIdeal W₂ :=
      Ideal.pow_mem_of_mem _ ((mem_maximalIdeal _).mpr h) _ hNpos
    have := Ideal.sub_mem _ this h1
    rw [sub_sub_cancel] at this
    exact (maximalIdeal.isMaximal W₂).ne_top (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)

  have hNunit : IsUnit ((N : ℕ) : W₂) := isUnit_natCast_of_not_dvd hqp hq₂ hN
  have hmonic : (Polynomial.X ^ N - 1 : Polynomial W₂).Monic := by
    have := Polynomial.monic_X_pow_sub_C (1 : W₂) (Nat.pos_iff_ne_zero.mp hNpos)
    rwa [map_one] at this
  have heval : (Polynomial.X ^ N - 1 : Polynomial W₂).eval c₀ ∈ maximalIdeal W₂ := by
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
    exact h1
  have hderiv : IsUnit (Ideal.Quotient.mk (maximalIdeal W₂)
      ((Polynomial.X ^ N - 1 : Polynomial W₂).derivative.eval c₀)) := by
    rw [Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero, Polynomial.derivative_X_pow,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    exact ((hNunit.mul (hc₀unit.pow _))).map _
  obtain ⟨c, hc, hcc₀⟩ := HenselianRing.is_henselian (I := maximalIdeal W₂)
    (Polynomial.X ^ N - 1) hmonic c₀ heval hderiv
  rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_one, sub_eq_zero] at hc
  have hcunit : IsUnit c := IsUnit.of_pow_eq_one hc (Nat.pos_iff_ne_zero.mp hNpos)
  obtain ⟨cu, rfl⟩ := hcunit
  refine ⟨cu, ?_⟩

  set z : SS := mkS φ * iota π₂ f₂ u₂ v₂ (↑cu⁻¹) with hz
  have hcuN : cu ^ N = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, hc, Units.val_one])
  have hzN : z ^ N = 1 := by
    rw [hz, mul_pow, hζ, one_mul, ← map_pow, ← Units.val_pow_eq_pow_val, inv_pow, hcuN, inv_one,
      Units.val_one, map_one]
  have hz1 : z - 1 ∈ maximalIdeal SS := by
    have hdiff : mkS φ - iota π₂ f₂ u₂ v₂ (cu : W₂) ∈ maximalIdeal SS := by
      have : mkS φ - iota π₂ f₂ u₂ v₂ (cu : W₂) =
          (mkS φ - iota π₂ f₂ u₂ v₂ c₀) + iota π₂ f₂ u₂ v₂ (c₀ - cu) := by
        rw [map_sub]; ring
      rw [this]
      refine Ideal.add_mem _ h0 ?_
      rw [iota_mem_maximalIdeal_iff q π₂ hπ₂ f₂ u₂ v₂ hf₂]
      have := (maximalIdeal W₂).neg_mem hcc₀
      rwa [neg_sub] at this
    have : z - 1 = (mkS φ - iota π₂ f₂ u₂ v₂ (cu : W₂)) * iota π₂ f₂ u₂ v₂ (↑cu⁻¹) := by
      rw [hz, sub_mul, ← map_mul, Units.mul_inv, map_one]
    rw [this]
    exact Ideal.mul_mem_right _ _ hdiff
  have hz_eq : z = 1 :=
    eq_one_of_pow_eq_one_of_sub_mem (isUnit_natCast_S q π₂ hπ₂ hq₂ f₂ u₂ v₂ hf₂ hN) hzN hz1

  have : mkS φ = z * iota π₂ f₂ u₂ v₂ (cu : W₂) := by
    rw [hz, mul_assoc, ← map_mul, Units.inv_mul, map_one, mul_one]
  rw [this, hz_eq, one_mul]

include hπ₂ hf₂ hq₂ hθ halg hπ₁ in

lemma exists_approx (n : ℕ) : ∀ w : W₁, ∃ (c : W₂) (s : SS),
    θ w = iota π₂ f₂ u₂ v₂ c + iota π₂ f₂ u₂ v₂ π₂ ^ n * s := by
  induction n with
  | zero => intro w; exact ⟨0, θ w, by simp⟩
  | succ n ih =>
    intro w
    obtain ⟨t, ht, hwt⟩ := exists_digit q W₁ π₁ halg π₂ hπ₂ hq₂ f₂ u₂ v₂ hf₂ θ hθ w

    obtain ⟨ct, hct⟩ : ∃ ct : W₂, θ t = iota π₂ f₂ u₂ v₂ ct := by
      rcases ht with rfl | ⟨N, hNpos, hN, htN⟩
      · exact ⟨0, by simp⟩
      · exact exists_eq_iota_of_pow_eq_one q π₂ hπ₂ hq₂ f₂ u₂ v₂ hf₂ hNpos hN (θ t)
          (by rw [← map_pow, htN, map_one])

    rw [hπ₁, Ideal.mem_span_singleton'] at hwt
    obtain ⟨w', hw'⟩ := hwt
    obtain ⟨c', s', hc'⟩ := ih w'
    refine ⟨ct + π₂ * c', s', ?_⟩
    have hw : w = t + w' * π₁ := by rw [hw']; ring
    have hθπ : θ π₁ = iota π₂ f₂ u₂ v₂ π₂ := by rw [hθ, iota_apply]
    rw [hw, map_add, map_mul, hct, hc', hθπ, map_add, map_mul]
    ring

include hπ₂ hf₂ hu₂ hq₂ hθ halg hπ₁ in

lemma exists_eq_iota (w : W₁) : ∃ c : W₂, θ w = iota π₂ f₂ u₂ v₂ c := by
  letI := isLocalRing_S q π₂ hπ₂ f₂ u₂ v₂ hf₂
  have hπ₂irr : Irreducible π₂ := (IsDiscreteValuationRing.irreducible_iff_uniformizer π₂).mpr hπ₂
  choose c s hcs using fun n => exists_approx q W₁ π₁ hπ₁ halg π₂ hπ₂ hq₂ f₂ u₂ v₂ hf₂ θ hθ n w

  have hmem : ∀ {m : ℕ} {x : W₂}, x ∈ (maximalIdeal W₂ ^ m • ⊤ : Submodule W₂ W₂) ↔ π₂ ^ m ∣ x := by
    intro m x
    rw [smul_eq_mul, Ideal.mul_top, hπ₂, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → c m ≡ c n [SMOD (maximalIdeal W₂ ^ m • ⊤ : Submodule W₂ W₂)] := by
    intro m n hmn
    rw [SModEq.sub_mem, hmem]
    apply pow_dvd_of_iota_eq q π₂ hπ₂ f₂ u₂ v₂ hu₂ hf₂ m (c m - c n)
      (iota π₂ f₂ u₂ v₂ π₂ ^ (n - m) * s n - s m)
    have h1 := hcs m
    have h2 := hcs n
    rw [map_sub]
    have : iota π₂ f₂ u₂ v₂ π₂ ^ n = iota π₂ f₂ u₂ v₂ π₂ ^ m * iota π₂ f₂ u₂ v₂ π₂ ^ (n - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hmn]
    rw [this] at h2
    linear_combination h2 - h1
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := maximalIdeal W₂) (M := W₂)) hcauchy
  refine ⟨L, ?_⟩

  haveI : IsNoetherianRing (MvPowerSeries (Fin 2) W₂) := MvPowerSeries.isNoetherianRing_fin W₂ 2
  haveI : IsNoetherianRing SS := inferInstance
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (R := SS) (I := maximalIdeal SS)
    (maximalIdeal.isMaximal SS).ne_top
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hbot, Ideal.mem_iInf]
  intro n
  have hdn : π₂ ^ n ∣ c n - L := by rw [← hmem, ← SModEq.sub_mem]; exact hL n
  obtain ⟨d, hd⟩ := hdn
  have : θ w - iota π₂ f₂ u₂ v₂ L = iota π₂ f₂ u₂ v₂ π₂ ^ n * (s n + iota π₂ f₂ u₂ v₂ d) := by
    have : L = c n - π₂ ^ n * d := by rw [← hd]; ring
    rw [this, hcs n, map_sub, map_mul, map_pow]
    ring
  rw [this]
  refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ n)
  rw [iota_mem_maximalIdeal_iff q π₂ hπ₂ f₂ u₂ v₂ hf₂]
  exact pi2_mem π₂ hπ₂

include hπ₂ hf₂ hu₂ hq₂ hθ halg hπ₁ in

theorem exists_ringHom :
    ∃ ρ : W₁ →+* W₂, ρ π₁ = π₂ ∧ ∀ w : W₁, θ w = iota π₂ f₂ u₂ v₂ (ρ w) := by
  have hinj := iota_injective q π₂ hπ₂ f₂ u₂ v₂ hu₂ hf₂
  choose ρ₀ hρ₀ using fun w => exists_eq_iota q W₁ π₁ hπ₁ halg π₂ hπ₂ hq₂ f₂ u₂ v₂ hu₂ hf₂ θ hθ w
  let ρ : W₁ →+* W₂ :=
    { toFun := ρ₀
      map_one' := hinj (by rw [← hρ₀, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [← hρ₀, map_mul, map_mul, hρ₀, hρ₀])
      map_zero' := hinj (by rw [← hρ₀, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [← hρ₀, map_add, map_add, hρ₀, hρ₀]) }
  refine ⟨ρ, hinj ?_, fun w => hρ₀ w⟩
  show iota π₂ f₂ u₂ v₂ (ρ₀ π₁) = iota π₂ f₂ u₂ v₂ π₂
  rw [← hρ₀, hθ, iota_apply]

end main2

end ConstRigidAux

open ConstRigidAux in
theorem solution
    (q : ℕ) [Fact q.Prime]
    (W₁ : Type) [CommRing W₁] [IsDomain W₁] [IsDiscreteValuationRing W₁] [IsAdicComplete (maximalIdeal W₁) W₁]
    (π₁ : W₁) (hπ₁ : maximalIdeal W₁ = Ideal.span {π₁})
    (halg : ∀ x : ResidueField W₁, ∃ n : ℕ, 1 ≤ n ∧ x ^ (q ^ n) = x)
    (W₂ : Type) [CommRing W₂] [IsDomain W₂] [IsDiscreteValuationRing W₂] [IsAdicComplete (maximalIdeal W₂) W₂]
    (π₂ : W₂) (hπ₂ : maximalIdeal W₂ = Ideal.span {π₂}) (hq₂ : (q : W₂) ∈ maximalIdeal W₂)
    (f₂ u₂ v₂ : MvPowerSeries (Fin 2) W₂) (hu₂ : IsUnit u₂) (hv₂ : IsUnit v₂)
    (hf₂ : f₂ - DrinfeldCurve.LocalChart.drinfeldForm q W₂ ∈
      (Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W₂), MvPowerSeries.X 1}) ^ (q + 2))
    (θ : W₁ →+* MvPowerSeries (Fin 2) W₂ ⧸ Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂})
    (hθ : θ π₁ = Ideal.Quotient.mk _ (MvPowerSeries.C π₂)) :
    ∃ ρ : W₁ →+* W₂, ρ π₁ = π₂ ∧
      ∀ w : W₁, θ w = Ideal.Quotient.mk (Ideal.span {MvPowerSeries.C π₂ * v₂ - f₂ * u₂}) (MvPowerSeries.C (ρ w)) :=
  exists_ringHom q W₁ π₁ hπ₁ halg π₂ hπ₂ hq₂ f₂ u₂ v₂ hu₂ hf₂ θ hθ

end S_DrinfeldCurve_LocalChart_exists_ringHom_forall_apply_eq_mk_C_of_apply_eq_mk_C_of_forall_pow_pow_eq
end P2MW
export P2MW.S_DrinfeldCurve_LocalChart_exists_ringHom_forall_apply_eq_mk_C_of_apply_eq_mk_C_of_forall_pow_pow_eq (solution)
