-- Prove2me | solution 1 for CerednikDrinfeld.Omega.natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/85f8a65f-66ff-5738-a213-51f4126d1f80

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Definitions.Def_CerednikDrinfeld_BruhatTitsTree
import Definitions.Def_CerednikDrinfeld_MumfordVertexType
import Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Definitions.Def_CerednikDrinfeld_MumfordQuotientNormalizer
import Definitions.Def_CerednikDrinfeld_OmegaOrdAt
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_CerednikDrinfeld_Omega_coordSub_dvd_of_apply_eq_zero
import Theorems.Thm_CerednikDrinfeld_Omega_exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero
import Mathlib.RingTheory.IntegralDomain
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_Omega_natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford

namespace P2mKcDivOrd

section Powers

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

theorem algebraMap_varpi_ne_zero : algebraMap K₀ K ϖ.ϖ ≠ 0 := fun h => by
  have := ϖ.pos
  rw [h, map_zero] at this
  exact lt_irrefl _ this

theorem varpi_ne_zero : ϖ.ϖ ≠ 0 := fun h => algebraMap_varpi_ne_zero ϖ (by rw [h, map_zero])

theorem algebraMap_varpi_ne_one : algebraMap K₀ K ϖ.ϖ ≠ 1 := fun h => by
  have := ϖ.lt_one
  rw [h, map_one] at this
  exact lt_irrefl _ this

theorem P_pow_mul_p_pow (i : ℕ) :
    (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ i * Valued.v (algebraMap K₀ K ϖ.ϖ) ^ i = 1 := by
  rw [← mul_pow, inv_mul_cancel₀ ϖ.pos.ne', one_pow]

theorem pow_succ_lt_pow (n : ℕ) :
    Valued.v (algebraMap K₀ K ϖ.ϖ) ^ (n + 1) < Valued.v (algebraMap K₀ K ϖ.ϖ) ^ n := by
  rw [pow_succ]
  exact mul_lt_of_lt_one_right (pow_pos ϖ.pos n) ϖ.lt_one

end Powers

section LocFin

variable {R₀ K₀ : Type} [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Field K₀] [Algebra R₀ K₀]
  [IsFractionRing R₀ K₀]
variable {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

theorem hfin_of_finite_residueField [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)
    (ϖ : PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ) (n : ℕ) :
    ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n := by
  classical
  set p : Γ₀ := Valued.v (algebraMap K₀ K ϖ.ϖ) with hp
  set k : ℕ := n + (n + 1) with hk
  have hmax : IsLocalRing.maximalIdeal R₀ = Ideal.span {ϖ₀} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ₀).1 hϖ₀
  haveI : Finite (R₀ ⧸ Ideal.span {ϖ₀ ^ k}) :=
    IsLocalRing.finite_quotient_iff.2 ⟨k, by rw [hmax, Ideal.span_singleton_pow]⟩
  letI : Fintype (R₀ ⧸ Ideal.span {ϖ₀ ^ k}) := Fintype.ofFinite _
  have hϖn0 : (ϖ.ϖ : K₀) ^ n ≠ 0 := pow_ne_zero n (varpi_ne_zero ϖ)
  refine ⟨Finset.univ.image fun c : R₀ ⧸ Ideal.span {ϖ₀ ^ k} => algebraMap R₀ K₀ (Quotient.out c) / ϖ.ϖ ^ n,
    fun a ha => ?_⟩
  have hint' : Valued.v (algebraMap K₀ K (ϖ.ϖ ^ n * a)) ≤ 1 := by
    rw [map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
    calc p ^ n * Valued.v (algebraMap K₀ K a) ≤ p ^ n * (p⁻¹) ^ n := mul_le_mul_right ha _
      _ = 1 := by rw [mul_comm, P_pow_mul_p_pow]
  obtain ⟨r, hr⟩ := (hR₀ _).2 hint'
  set c : R₀ ⧸ Ideal.span {ϖ₀ ^ k} := Ideal.Quotient.mk _ r with hc
  have hcs : r - Quotient.out c ∈ Ideal.span {ϖ₀ ^ k} := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  obtain ⟨r'', hr''⟩ := Ideal.mem_span_singleton.1 hcs
  refine ⟨algebraMap R₀ K₀ (Quotient.out c) / ϖ.ϖ ^ n, Finset.mem_image.2 ⟨c, Finset.mem_univ _, rfl⟩, ?_⟩
  have haeq : a = algebraMap R₀ K₀ r / ϖ.ϖ ^ n := by
    rw [eq_div_iff hϖn0, mul_comm, hr]
  have hat : a - algebraMap R₀ K₀ (Quotient.out c) / ϖ.ϖ ^ n = ϖ.ϖ ^ (n + 1) * algebraMap R₀ K₀ r'' := by
    rw [haeq, ← sub_div, ← map_sub, hr'', div_eq_iff hϖn0, map_mul, map_pow, hϖ, hk]
    ring
  have hint : Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ r'')) ≤ 1 := (hR₀ _).1 ⟨r'', rfl⟩
  rw [← map_sub, hat, map_mul, map_pow, Valuation.map_mul, Valuation.map_pow]
  calc p ^ (n + 1) * Valued.v (algebraMap K₀ K (algebraMap R₀ K₀ r''))
      ≤ p ^ (n + 1) * 1 := mul_le_mul_right hint _
    _ < p ^ n := by rw [mul_one]; exact pow_succ_lt_pow ϖ n

end LocFin

section Basic

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

local notation "Ω" => upperHalfPlane K₀ K

def ev (z : ↥Ω) : ↥(holRing ϖ) →+* K := (Pi.evalRingHom (fun _ : ↥Ω => K) z).comp (holRing ϖ).subtype

@[scoped simp] theorem ev_apply (z : ↥Ω) (F : ↥(holRing ϖ)) : ev ϖ z F = (F : ↥Ω → K) z := rfl

theorem ev_coordSub (z : ↥Ω) : ev ϖ z (coordSub ϖ z) = 0 := coordSub_apply_self ϖ z

theorem ev_algebraMap (z : ↥Ω) (c : K) : ev ϖ z (algebraMap K ↥(holRing ϖ) c) = c := rfl

theorem add_algebraMap_mem (z : ↥Ω) (t : K₀) : (z : K) + algebraMap K₀ K t ∈ Ω := by
  rw [mem_upperHalfPlane_iff]
  intro x hx
  exact (mem_upperHalfPlane_iff K₀ (z : K)).1 z.2 (x - t) (by rw [map_sub, hx, add_sub_cancel_right])

def shift (z : ↥Ω) (t : K₀) : ↥Ω := ⟨(z : K) + algebraMap K₀ K t, add_algebraMap_mem z t⟩

@[scoped simp] theorem coe_shift (z : ↥Ω) (t : K₀) : ((shift z t : ↥Ω) : K) = (z : K) + algebraMap K₀ K t := rfl

theorem coordSub_ne_zero (z : ↥Ω) : coordSub ϖ z ≠ 0 := by
  intro h
  have h1 := congrArg (fun F : ↥(holRing ϖ) => (F : ↥Ω → K) (shift z 1)) h
  simp only [coordSub_apply, coe_shift, map_one, ZeroMemClass.coe_zero, Pi.zero_apply,
    add_sub_cancel_left] at h1
  exact one_ne_zero h1

theorem coordSub_pow_ne_zero [IsDomain ↥(holRing ϖ)] (z : ↥Ω) (n : ℕ) : coordSub ϖ z ^ n ≠ 0 :=
  pow_ne_zero n (coordSub_ne_zero ϖ z)

end Basic

section Faithful

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)

local notation "Ω" => upperHalfPlane K₀ K

include ϖ in

theorem eq_one_of_forall_coe_smul_eq (τ : PGL(2, K₀)) (z : ↥Ω)
    (h : ∀ w : ↥Ω, ((τ • w : ↥Ω) : K) = (w : K)) : τ = 1 := by
  revert h
  induction τ using Matrix.ProjGenLinGroup.induction_on with
  | _ g =>
  intro h
  obtain ⟨a, ha⟩ : ∃ a : K, algebraMap K₀ K (g 0 0) = a := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : K, algebraMap K₀ K (g 0 1) = b := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : K, algebraMap K₀ K (g 1 0) = c := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : K, algebraMap K₀ K (g 1 1) = d := ⟨_, rfl⟩
  have key : ∀ w : ↥Ω, c * (w : K) * (w : K) + d * (w : K) = a * (w : K) + b := fun w => by
    have hden := moebius_denom_ne_zero_of_mem K₀ w.2 g
    have hw := h w
    rw [coe_smul_upperHalfPlane, pmoebius_mk K₀ g (w : K) hden, moebius, div_eq_iff hden, ha, hb, hc, hd] at hw
    linear_combination (-1 : K) * hw
  obtain ⟨t, ht⟩ : ∃ t : K, algebraMap K₀ K ϖ.ϖ = t := ⟨_, rfl⟩
  have ht0 : t ≠ 0 := ht ▸ algebraMap_varpi_ne_zero ϖ
  have ht1 : t - 1 ≠ 0 := sub_ne_zero.2 (ht ▸ algebraMap_varpi_ne_one ϖ)
  have k0 := key z
  have k1 := key (shift z 1)
  have k2 := key (shift z ϖ.ϖ)
  simp only [coe_shift, map_one] at k1 k2
  rw [ht] at k2
  have hct : c * t * (t - 1) = 0 := by linear_combination k2 - k0 - t * (k1 - k0)
  have hc0 : c = 0 := by
    rcases mul_eq_zero.1 hct with h' | h'
    · rcases mul_eq_zero.1 h' with h'' | h''
      · exact h''
      · exact absurd h'' ht0
    · exact absurd h' ht1
  have hda : d - a = 0 := by linear_combination k1 - k0 - (2 * (z : K) + 1) * hc0
  have hb0 : b = 0 := by linear_combination (-1 : K) * k0 + (z : K) * (z : K) * hc0 + (z : K) * hda

  have h10 : g 1 0 = 0 := (algebraMap K₀ K).injective (by rw [map_zero, hc]; exact hc0)
  have h01 : g 0 1 = 0 := (algebraMap K₀ K).injective (by rw [map_zero, hb]; exact hb0)
  have h11 : g 1 1 = g 0 0 := (algebraMap K₀ K).injective (by rw [hd, ha]; exact sub_eq_zero.1 hda)
  have h00 : g 0 0 ≠ 0 := by
    intro h0
    apply g.det_ne_zero
    rw [Matrix.det_fin_two]
    simp [h0, h10]
  have hg : g = Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.mk0 (g 0 0) h00) := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal, h10, h01, h11]
  rw [hg, Matrix.ProjGenLinGroup.mk_scalar]

end Faithful

section Cocycle

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)
variable [CompleteSpace K] [IsAlgClosed K]
variable (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
variable (hex : IsExhausted ϖ)

local notation "Ω" => upperHalfPlane K₀ K

omit [CompleteSpace K] [IsAlgClosed K] in

theorem smul_algebraMap (σ : PGL(2, K₀)) (c : K) :
    σ • algebraMap K ↥(holRing ϖ) c = algebraMap K ↥(holRing ϖ) c := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

omit [CompleteSpace K] [IsAlgClosed K] in

theorem ev_smul_of_fix {σ : PGL(2, K₀)} {z : ↥Ω} (hσ : σ • z = z) (F : ↥(holRing ϖ)) :
    ev ϖ z (σ • F) = ev ϖ z F := by
  have h' : σ⁻¹ • z = z := by rw [inv_smul_eq_iff, hσ]
  rw [ev_apply, coe_smul_holRing_apply, h', ev_apply]

include hrk hex in

theorem coordSub_dvd_smul_coordSub {σ : PGL(2, K₀)} {z : ↥Ω} (hσ : σ • z = z) :
    coordSub ϖ z ∣ σ • coordSub ϖ z := by
  refine CerednikDrinfeld.Omega.coordSub_dvd_of_apply_eq_zero K₀ K ϖ hrk hex _ _ ?_
  have h' : σ⁻¹ • z = z := by rw [inv_smul_eq_iff, hσ]
  rw [coe_smul_holRing_apply, h', coordSub_apply_self]

def J (z : ↥Ω) (σ : PGL(2, K₀)) : ↥(holRing ϖ) := by
  classical
  exact if hσ : σ • z = z then (coordSub_dvd_smul_coordSub ϖ hrk hex hσ).choose else 1

theorem J_spec {z : ↥Ω} {σ : PGL(2, K₀)} (hσ : σ • z = z) :
    σ • coordSub ϖ z = coordSub ϖ z * J ϖ hrk hex z σ := by
  classical
  unfold J
  rw [dif_pos hσ]
  exact (coordSub_dvd_smul_coordSub ϖ hrk hex hσ).choose_spec

variable [IsDomain ↥(holRing ϖ)]

theorem J_unique {z : ↥Ω} {σ : PGL(2, K₀)} (hσ : σ • z = z) {A : ↥(holRing ϖ)}
    (hA : σ • coordSub ϖ z = coordSub ϖ z * A) : J ϖ hrk hex z σ = A :=
  mul_left_cancel₀ (coordSub_ne_zero ϖ z) ((J_spec ϖ hrk hex hσ).symm.trans hA)

theorem J_one (z : ↥Ω) : J ϖ hrk hex z 1 = 1 :=
  J_unique ϖ hrk hex (one_smul _ z) (by rw [one_smul, mul_one])

theorem J_mul {z : ↥Ω} {σ τ : PGL(2, K₀)} (hσ : σ • z = z) (hτ : τ • z = z) :
    J ϖ hrk hex z (σ * τ) = J ϖ hrk hex z σ * σ • J ϖ hrk hex z τ := by
  refine J_unique ϖ hrk hex (by rw [mul_smul, hτ, hσ]) ?_
  rw [mul_smul, J_spec ϖ hrk hex hτ, smul_mul', J_spec ϖ hrk hex hσ, mul_assoc]

def zeta (z : ↥Ω) (σ : PGL(2, K₀)) : K := ev ϖ z (J ϖ hrk hex z σ)

theorem zeta_one (z : ↥Ω) : zeta ϖ hrk hex z 1 = 1 := by
  rw [zeta, J_one, map_one]

theorem zeta_mul {z : ↥Ω} {σ τ : PGL(2, K₀)} (hσ : σ • z = z) (hτ : τ • z = z) :
    zeta ϖ hrk hex z (σ * τ) = zeta ϖ hrk hex z σ * zeta ϖ hrk hex z τ := by
  rw [zeta, J_mul ϖ hrk hex hσ hτ, map_mul, ev_smul_of_fix ϖ hσ]
  rfl

theorem zeta_ne_zero {z : ↥Ω} {σ : PGL(2, K₀)} (hσ : σ • z = z) : zeta ϖ hrk hex z σ ≠ 0 := by
  have hσ' : σ⁻¹ • z = z := by rw [inv_smul_eq_iff, hσ]
  intro h0
  have h1 := zeta_mul ϖ hrk hex hσ hσ'
  rw [mul_inv_cancel, zeta_one, h0, zero_mul] at h1
  exact one_ne_zero h1

theorem smul_coordSub_pow_mul {z : ↥Ω} {σ : PGL(2, K₀)} (hσ : σ • z = z) (n : ℕ) (F₁ : ↥(holRing ϖ)) :
    σ • (coordSub ϖ z ^ n * F₁) = coordSub ϖ z ^ n * (J ϖ hrk hex z σ ^ n * σ • F₁) := by
  rw [smul_mul', smul_pow', J_spec ϖ hrk hex hσ, mul_pow, mul_assoc]

theorem zeta_pow_eq_zeta_pow {z : ↥Ω} {σ : PGL(2, K₀)} (hσ : σ • z = z)
    {g h g₁ h₁ : ↥(holRing ϖ)} {a b : ℕ}
    (hg : g = coordSub ϖ z ^ a * g₁) (hh : h = coordSub ϖ z ^ b * h₁)
    (hg₁ : (g₁ : ↥Ω → K) z ≠ 0) (hh₁ : (h₁ : ↥Ω → K) z ≠ 0)
    (hinv : (σ • g) * h = g * (σ • h)) :
    zeta ϖ hrk hex z σ ^ a = zeta ϖ hrk hex z σ ^ b := by
  have e1 : (σ • g) * h = coordSub ϖ z ^ (a + b) * (J ϖ hrk hex z σ ^ a * σ • g₁ * h₁) := by
    rw [hg, smul_coordSub_pow_mul ϖ hrk hex hσ, hh]; ring
  have e2 : g * (σ • h) = coordSub ϖ z ^ (a + b) * (g₁ * (J ϖ hrk hex z σ ^ b * σ • h₁)) := by
    rw [hh, smul_coordSub_pow_mul ϖ hrk hex hσ, hg]; ring
  rw [e1, e2] at hinv
  have hcanc := mul_left_cancel₀ (coordSub_pow_ne_zero ϖ z (a + b)) hinv
  have hev := congrArg (ev ϖ z) hcanc
  simp only [map_mul, map_pow, ev_smul_of_fix ϖ hσ] at hev

  have key : (ev ϖ z (J ϖ hrk hex z σ) ^ a - ev ϖ z (J ϖ hrk hex z σ) ^ b) * (ev ϖ z g₁ * ev ϖ z h₁) = 0 := by
    linear_combination hev
  show ev ϖ z (J ϖ hrk hex z σ) ^ a = ev ϖ z (J ϖ hrk hex z σ) ^ b
  rcases mul_eq_zero.1 key with h0 | h0
  · exact sub_eq_zero.1 h0
  · exact absurd h0 (mul_ne_zero hg₁ hh₁)

omit [CompleteSpace K] [IsAlgClosed K] [IsDomain ↥(holRing ϖ)] in

theorem iterate_expansion {z : ↥Ω} {σ : PGL(2, K₀)} (c : K) (k : ℕ) (E : ↥(holRing ϖ))
    (hA : σ • coordSub ϖ z =
      coordSub ϖ z + algebraMap K ↥(holRing ϖ) c * coordSub ϖ z ^ (k + 2) + coordSub ϖ z ^ (k + 3) * E)
    (j : ℕ) :
    ∃ R : ↥(holRing ϖ), σ ^ j • coordSub ϖ z =
      coordSub ϖ z + algebraMap K ↥(holRing ϖ) ((j : K) * c) * coordSub ϖ z ^ (k + 2) +
        coordSub ϖ z ^ (k + 3) * R := by
  induction j with
  | zero => exact ⟨0, by simp⟩
  | succ j ih =>
    obtain ⟨R, hR⟩ := ih
    have hAM : σ • coordSub ϖ z = coordSub ϖ z * (1 + coordSub ϖ z *
        (algebraMap K ↥(holRing ϖ) c * coordSub ϖ z ^ k + coordSub ϖ z ^ (k + 1) * E)) := by
      rw [hA]; ring
    obtain ⟨P, hP⟩ := sub_dvd_pow_sub_pow (1 + coordSub ϖ z *
        (algebraMap K ↥(holRing ϖ) c * coordSub ϖ z ^ k + coordSub ϖ z ^ (k + 1) * E)) 1 (k + 2)
    rw [one_pow, add_sub_cancel_left] at hP
    have hPk : (1 + coordSub ϖ z *
        (algebraMap K ↥(holRing ϖ) c * coordSub ϖ z ^ k + coordSub ϖ z ^ (k + 1) * E)) ^ (k + 2) =
        1 + coordSub ϖ z * (algebraMap K ↥(holRing ϖ) c * coordSub ϖ z ^ k + coordSub ϖ z ^ (k + 1) * E) * P := by
      rw [← hP]; ring
    refine ⟨E + algebraMap K ↥(holRing ϖ) ((j : K) * c) *
        ((algebraMap K ↥(holRing ϖ) c * coordSub ϖ z ^ k + coordSub ϖ z ^ (k + 1) * E) * P) +
      (1 + coordSub ϖ z * (algebraMap K ↥(holRing ϖ) c * coordSub ϖ z ^ k + coordSub ϖ z ^ (k + 1) * E)) ^ (k + 3) *
        σ • R, ?_⟩
    rw [pow_succ', mul_smul, hR, smul_add, smul_add, smul_mul', smul_mul', smul_pow', smul_pow',
      smul_algebraMap ϖ, hAM, mul_pow, mul_pow, hPk, Nat.cast_succ]
    simp only [map_add, map_mul, map_one, map_natCast]
    generalize (1 + coordSub ϖ z *
        (algebraMap K ↥(holRing ϖ) c * coordSub ϖ z ^ k + coordSub ϖ z ^ (k + 1) * E)) ^ (k + 3) = W
    ring

include hrk hex in

theorem eq_one_of_zeta_eq_one
    (hlf : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    {z : ↥Ω} {σ : PGL(2, K₀)} (hσ : σ • z = z) {m : ℕ} (hm : σ ^ m = 1) (hmK : (m : K) ≠ 0)
    (hζ : zeta ϖ hrk hex z σ = 1) : σ = 1 := by
  classical
  by_cases hfix : σ • coordSub ϖ z = coordSub ϖ z
  ·
    have h1 : σ⁻¹ = 1 := by
      refine eq_one_of_forall_coe_smul_eq ϖ σ⁻¹ z fun w => ?_
      have := congrArg (fun F : ↥(holRing ϖ) => (F : ↥Ω → K) w) hfix
      simp only [coe_smul_holRing_apply, coordSub_apply] at this
      exact sub_left_injective this
    exact inv_eq_one.1 h1
  · exfalso
    obtain ⟨D, hD⟩ : ∃ D : ↥(holRing ϖ), D = σ • coordSub ϖ z - coordSub ϖ z := ⟨_, rfl⟩
    have hD0 : D ≠ 0 := by rw [hD]; exact sub_ne_zero.2 hfix
    have hσD : σ • coordSub ϖ z = coordSub ϖ z + D := by rw [hD]; ring
    have hDz : (D : ↥Ω → K) z = 0 := by
      show ev ϖ z D = 0
      rw [hD, map_sub, ev_smul_of_fix ϖ hσ, sub_self]
    obtain ⟨D₁, hD₁, hD₁z⟩ :=
      CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hlf D hD0 z
    obtain ⟨k, hk⟩ : ∃ k : ℕ, ordAt ϖ D z = k := ⟨_, rfl⟩
    rw [hk] at hD₁

    have hk0 : k ≠ 0 := by
      intro h0
      rw [h0, pow_zero, one_mul] at hD₁
      rw [hD₁] at hDz
      exact hD₁z hDz
    obtain ⟨k₁, rfl⟩ : ∃ k₁, k = k₁ + 1 := ⟨k - 1, by omega⟩

    have hJ : J ϖ hrk hex z σ = 1 + coordSub ϖ z ^ k₁ * D₁ := by
      refine J_unique ϖ hrk hex hσ ?_
      rw [hσD, hD₁]; ring
    have hk1 : k₁ ≠ 0 := by
      intro h0
      have hz1 : zeta ϖ hrk hex z σ = 1 + ev ϖ z D₁ := by
        rw [zeta, hJ, h0, pow_zero, one_mul, map_add, map_one]
      rw [hζ] at hz1
      have : ev ϖ z D₁ = 0 := by linear_combination (-1 : K) * hz1
      exact hD₁z this
    obtain ⟨k₂, rfl⟩ : ∃ k₂, k₁ = k₂ + 1 := ⟨k₁ - 1, by omega⟩

    obtain ⟨c, hc⟩ : ∃ c : K, (D₁ : ↥Ω → K) z = c := ⟨_, rfl⟩
    have hc0 : c ≠ 0 := by rw [← hc]; exact hD₁z
    have hcz : ((D₁ - algebraMap K ↥(holRing ϖ) c : ↥(holRing ϖ)) : ↥Ω → K) z = 0 := by
      show ev ϖ z (D₁ - algebraMap K ↥(holRing ϖ) c) = 0
      rw [map_sub, ev_algebraMap, ev_apply, hc, sub_self]
    obtain ⟨E, hE⟩ := CerednikDrinfeld.Omega.coordSub_dvd_of_apply_eq_zero K₀ K ϖ hrk hex _ z hcz
    have hD₁E : D₁ = algebraMap K ↥(holRing ϖ) c + coordSub ϖ z * E := by
      rw [← hE]; ring
    have hA : σ • coordSub ϖ z = coordSub ϖ z + algebraMap K ↥(holRing ϖ) c * coordSub ϖ z ^ (k₂ + 2) +
        coordSub ϖ z ^ (k₂ + 3) * E := by
      rw [hσD, hD₁, hD₁E]; ring
    obtain ⟨R, hR⟩ := iterate_expansion ϖ c k₂ E hA m
    rw [hm, one_smul] at hR
    have h0 : coordSub ϖ z ^ (k₂ + 2) * (algebraMap K ↥(holRing ϖ) ((m : K) * c) + coordSub ϖ z * R) = 0 := by
      linear_combination (-1 : ↥(holRing ϖ)) * hR
    rcases mul_eq_zero.1 h0 with h' | h'
    · exact coordSub_pow_ne_zero ϖ z _ h'
    · have hev := congrArg (ev ϖ z) h'
      rw [map_add, ev_algebraMap, map_mul, ev_coordSub, zero_mul, add_zero, map_zero] at hev
      rcases mul_eq_zero.1 hev with h'' | h''
      · exact hmK h''
      · exact hc0 h''

end Cocycle

section Stab

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)
variable [CompleteSpace K] [IsAlgClosed K]
variable (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)
variable (hex : IsExhausted ϖ)
variable [IsDomain ↥(holRing ϖ)]

local notation "Ω" => upperHalfPlane K₀ K

def chi (H : Subgroup PGL(2, K₀)) (z : ↥Ω) : ↥(MulAction.stabilizer ↥H z) →* Kˣ where
  toFun σ := Units.mk0 (zeta ϖ hrk hex z ((σ : ↥H) : PGL(2, K₀)))
    (zeta_ne_zero ϖ hrk hex (MulAction.mem_stabilizer_iff.1 σ.2))
  map_one' := Units.ext (by
    simp only [Units.val_mk0, OneMemClass.coe_one, Units.val_one]
    exact zeta_one ϖ hrk hex z)
  map_mul' σ τ := Units.ext (by
    simp only [Units.val_mk0, Subgroup.coe_mul, Units.val_mul]
    exact zeta_mul ϖ hrk hex (MulAction.mem_stabilizer_iff.1 σ.2) (MulAction.mem_stabilizer_iff.1 τ.2))

theorem val_chi (H : Subgroup PGL(2, K₀)) (z : ↥Ω) (σ : ↥(MulAction.stabilizer ↥H z)) :
    ((chi ϖ hrk hex H z σ : Kˣ) : K) = zeta ϖ hrk hex z ((σ : ↥H) : PGL(2, K₀)) := rfl

theorem chi_injective
    (hlf : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (H : Subgroup PGL(2, K₀)) (z : ↥Ω)
    (htame : ((Nat.card ↥(MulAction.stabilizer ↥H z) : ℕ) : K) ≠ 0) :
    Function.Injective (chi ϖ hrk hex H z) := by
  rw [injective_iff_map_eq_one]
  intro σ hσ1
  have hσ : ((σ : ↥H) : PGL(2, K₀)) • z = z := MulAction.mem_stabilizer_iff.1 σ.2
  have hζ : zeta ϖ hrk hex z ((σ : ↥H) : PGL(2, K₀)) = 1 := by
    rw [← val_chi, hσ1, Units.val_one]

  obtain ⟨q, hq⟩ := orderOf_dvd_natCard σ
  have hmK : ((orderOf σ : ℕ) : K) ≠ 0 := by
    intro h0
    apply htame
    rw [hq, Nat.cast_mul, h0, zero_mul]
  have hm : ((σ : ↥H) : PGL(2, K₀)) ^ orderOf σ = 1 := by
    have h1 : σ ^ orderOf σ = 1 := pow_orderOf_eq_one σ
    have h2 := congrArg (fun x : ↥(MulAction.stabilizer ↥H z) => ((x : ↥H) : PGL(2, K₀))) h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  have h := eq_one_of_zeta_eq_one ϖ hrk hex hlf hσ hm hmK hζ
  apply Subtype.ext
  apply Subtype.ext
  simpa using h

include hrk hex in

theorem card_stabilizer_dvd
    (hlf : ∀ n : ℕ, ∃ T : Finset K₀, ∀ a : K₀,
      Valued.v (algebraMap K₀ K a) ≤ (Valued.v (algebraMap K₀ K ϖ.ϖ))⁻¹ ^ n →
        ∃ t ∈ T, Valued.v (algebraMap K₀ K a - algebraMap K₀ K t) < (Valued.v (algebraMap K₀ K ϖ.ϖ)) ^ n)
    (H : Subgroup PGL(2, K₀)) (z : ↥Ω)
    (htame : ((Nat.card ↥(MulAction.stabilizer ↥H z) : ℕ) : K) ≠ 0)
    (g h : ↥(holRing ϖ)) (hg : g ≠ 0) (hh : h ≠ 0)
    (hinv : ∀ σ : PGL(2, K₀), σ ∈ H → σ • z = z → (σ • g) * h = g * (σ • h)) :
    ((Nat.card ↥(MulAction.stabilizer ↥H z) : ℕ) : ℤ) ∣ (ordAt ϖ g z : ℤ) - (ordAt ϖ h z : ℤ) := by
  classical

  have hcard0 : Nat.card ↥(MulAction.stabilizer ↥H z) ≠ 0 := fun h0 => htame (by rw [h0, Nat.cast_zero])
  haveI : Finite ↥(MulAction.stabilizer ↥H z) := Nat.finite_of_card_ne_zero hcard0

  obtain ⟨g₁, hg1, hg₁z⟩ :=
    CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hlf g hg z
  obtain ⟨h₁, hh1, hh₁z⟩ :=
    CerednikDrinfeld.Omega.exists_eq_coordSub_pow_ordAt_mul_and_apply_ne_zero K₀ K hrk ϖ hex hlf h hh z

  have hinj := chi_injective ϖ hrk hex hlf H z htame
  haveI : IsCyclic ↥(MulAction.stabilizer ↥H z) :=
    isCyclic_of_injective_ringHom ((Units.coeHom K).comp (chi ϖ hrk hex H z))
      (fun a b hab => hinj (Units.ext hab))
  obtain ⟨σ₀, hσ₀⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥(MulAction.stabilizer ↥H z))
  have hσ₀z : ((σ₀ : ↥H) : PGL(2, K₀)) • z = z := MulAction.mem_stabilizer_iff.1 σ₀.2

  have hpow := zeta_pow_eq_zeta_pow ϖ hrk hex hσ₀z hg1 hh1 hg₁z hh₁z (hinv _ (σ₀ : ↥H).2 hσ₀z)
  have hu : (chi ϖ hrk hex H z σ₀) ^ (ordAt ϖ g z) = (chi ϖ hrk hex H z σ₀) ^ (ordAt ϖ h z) :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, val_chi]; exact hpow)
  have hz1 : (chi ϖ hrk hex H z σ₀) ^ ((ordAt ϖ g z : ℤ) - (ordAt ϖ h z : ℤ)) = 1 := by
    rw [zpow_sub, zpow_natCast, zpow_natCast, hu, mul_inv_cancel]
  have hord : orderOf (chi ϖ hrk hex H z σ₀) = Nat.card ↥(MulAction.stabilizer ↥H z) := by
    rw [orderOf_injective _ hinj σ₀, hσ₀]
  rw [← hord]
  exact orderOf_dvd_iff_zpow_eq_one.2 hz1

end Stab

section Frame

variable {K₀ : Type} [Field K₀] {K : Type} [Field K] [Algebra K₀ K] [DecidableEq K]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
variable (ϖ : PseudoUniformizer K₀ K)
variable {G : Type} [Group G] (ρ : G →* PGL(2, K₀))

local notation "Ω" => upperHalfPlane K₀ K
local notation "𝓞" => HolRingOf ϖ ρ
local notation "𝓚" => FractionRing (HolRingOf ϖ ρ)

def toHol : 𝓞 →+* ↥(holRing ϖ) where
  toFun F := F
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem toHol_apply (F : 𝓞) : toHol ϖ ρ F = (show ↥(holRing ϖ) from F) := rfl

theorem toHol_injective : Function.Injective (toHol ϖ ρ) := fun _ _ h => h

theorem toHol_smul (g : G) (F : 𝓞) : toHol ϖ ρ (g • F) = ρ g • toHol ϖ ρ F := rfl

theorem toHol_ne_zero {F : 𝓞} : toHol ϖ ρ F ≠ 0 ↔ F ≠ 0 :=
  (map_ne_zero_iff _ (toHol_injective ϖ ρ))

variable [IsDomain (HolRingOf ϖ ρ)]

omit [DecidableEq K] in
theorem isDomain_holRing_of (ρ' : G →* PGL(2, K₀)) [IsDomain (HolRingOf ϖ ρ')] : IsDomain ↥(holRing ϖ) :=
  (HolRingOf.isDomain_iff ϖ ρ').1 inferInstance

theorem smul_ne_zero_of_ne_zero (g : G) {a : 𝓞} (ha : a ≠ 0) : g • a ≠ 0 := fun h => by
  apply ha
  have := congrArg (fun x : 𝓞 => g⁻¹ • x) h
  simpa using this

theorem smul_mul_eq_mul_smul_of_mem (Δ : Subgroup G) (g h : 𝓞) (hh : h ∈ nonZeroDivisors 𝓞)
    (hx : Localization.mk g ⟨h, hh⟩ ∈ invariantFieldOf K G 𝓞 Δ) {γ : G} (hγ : γ ∈ Δ) :
    (γ • g) * h = g * (γ • h) := by
  have hb0 : h ≠ 0 := nonZeroDivisors.ne_zero hh
  have hinv := (mem_invariantFieldOf_iff K G 𝓞 Δ _).1 hx γ hγ
  rw [Localization.mk_eq_mk'_apply, IsFractionRing.mk'_eq_div] at hinv
  change γ • (algebraMap 𝓞 𝓚 g / algebraMap 𝓞 𝓚 h) = algebraMap 𝓞 𝓚 g / algebraMap 𝓞 𝓚 h at hinv
  rw [div_eq_mul_inv, smul_mul', smul_inv'', frac_smul_algebraMap, frac_smul_algebraMap, ← div_eq_mul_inv,
    ← div_eq_mul_inv] at hinv
  have hγb0 : γ • h ≠ 0 := smul_ne_zero_of_ne_zero ϖ ρ γ hb0
  have hne : (algebraMap 𝓞 𝓚 h) ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hh
  have hne' : (algebraMap 𝓞 𝓚 (γ • h)) ≠ 0 := fun h0 =>
    hγb0 ((IsFractionRing.injective 𝓞 𝓚) (by rw [h0, map_zero]))
  rw [div_eq_div_iff hne' hne, ← map_mul, ← map_mul] at hinv
  exact IsFractionRing.injective 𝓞 𝓚 hinv

end Frame

end P2mKcDivOrd
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving.P2mKcDivOrd"

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_Omega_natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving.P2mKcDivOrd"

open scoped MatrixGroups
open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford AlgebraicCurve

open P2mKcDivOrd in
theorem solution

    (K₀ : Type) [Field K₀] (K : Type) [Field K] [Algebra K₀ K] [DecidableEq K]
    {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
    (hrk : ∀ x y : K, Valued.v x < 1 → y ≠ 0 → ∃ n : ℕ, Valued.v x ^ n ≤ Valued.v y)

    (hval : ∀ ε : Γ₀, ε ≠ 0 → ∃ y : K, y ≠ 0 ∧ Valued.v y ≤ ε)
    [CompleteSpace K] [IsAlgClosed K]
    (R₀ : Type) [CommRing R₀] [IsDomain R₀] [IsDiscreteValuationRing R₀] [Algebra R₀ K₀] [IsFractionRing R₀ K₀]
    [Finite (IsLocalRing.ResidueField R₀)]
    (hR₀ : ∀ x : K₀, x ∈ Set.range (algebraMap R₀ K₀) ↔ Valued.v (algebraMap K₀ K x) ≤ 1)

    (ϖ : Omega.PseudoUniformizer K₀ K) (ϖ₀ : R₀) (hϖ₀ : Irreducible ϖ₀) (hϖ : algebraMap R₀ K₀ ϖ₀ = ϖ.ϖ)
    (hex : Omega.IsExhausted ϖ)

    (G : Type) [Group G] (ρ : G →* PGL(2, K₀))
    [IsDomain (Omega.HolRingOf ϖ ρ)]

    (Γ : Subgroup G) (htp : Γ.map ρ ≤ Mumford.typePreserving PGL(2, K₀) (BruhatTits.tree R₀ K₀) (LT.LatticeTree.stdVertex R₀ K₀))
    [Mumford.GraphAction ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀)]
    (hfin : ∀ d : (BruhatTits.tree R₀ K₀).Dart, Finite (MulAction.stabilizer (↥(Γ.map ρ)) d))
    [Fintype (Mumford.QuotVert ↥(Γ.map ρ) (LT.LatticeTree.Vertex R₀ K₀))]
    [Fintype (Mumford.QuotEdge ↥(Γ.map ρ) (BruhatTits.tree R₀ K₀))]
    (z : ↥(Omega.upperHalfPlane K₀ K))
    (htame : ((Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) z) : ℕ) : K) ≠ 0)
    (g h : Omega.HolRingOf ϖ ρ) (hg : g ≠ 0) (hh : h ∈ nonZeroDivisors (Omega.HolRingOf ϖ ρ))
    (hx : Localization.mk g ⟨h, hh⟩ ∈ Mumford.invariantFieldOf K G (Omega.HolRingOf ϖ ρ) Γ) :
    ((Nat.card ↥(MulAction.stabilizer ↥(Γ.map ρ) z) : ℤ) ∣
      (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from g) z : ℤ) - (Omega.ordAt ϖ (show ↥(Omega.holRing ϖ) from h) z : ℤ)) := by
  classical

  have hlf := hfin_of_finite_residueField (K := K) hR₀ ϖ ϖ₀ hϖ₀ hϖ
  haveI : IsDomain ↥(Omega.holRing ϖ) := isDomain_holRing_of ϖ ρ

  have hg' : toHol ϖ ρ g ≠ 0 := (toHol_ne_zero ϖ ρ).2 hg
  have hh' : toHol ϖ ρ h ≠ 0 := (toHol_ne_zero ϖ ρ).2 (nonZeroDivisors.ne_zero hh)

  have hinv : ∀ σ : PGL(2, K₀),
      σ ∈ Γ.map ρ →
      σ • z = z → (σ • toHol ϖ ρ g) * toHol ϖ ρ h = toHol ϖ ρ g * (σ • toHol ϖ ρ h) := by
    intro σ hσ _
    obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.1 hσ
    have hM := smul_mul_eq_mul_smul_of_mem ϖ ρ _ g h hh hx hγ
    have := congrArg (toHol ϖ ρ) hM
    simpa only [map_mul, toHol_smul] using this
  exact card_stabilizer_dvd ϖ hrk hex hlf _ z htame (toHol ϖ ρ g) (toHol ϖ ρ h) hg' hh' hinv

end S_CerednikDrinfeld_Omega_natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving
end P2MW
export P2MW.S_CerednikDrinfeld_Omega_natCast_card_stabilizer_dvd_ordAt_sub_ordAt_of_mk_mem_invariantFieldOf_of_map_le_typePreserving (solution)
