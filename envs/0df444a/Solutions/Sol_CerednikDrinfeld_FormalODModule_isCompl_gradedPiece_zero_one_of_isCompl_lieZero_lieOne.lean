-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/c70d689e-1c00-5dff-aaf4-c59e0e9ca598

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_surjective
import Theorems.Thm_MvFormalGroup_CartierModule_tangent_eq_zero_iff_exists_verschiebung_eq
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebung_iterate_add
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

noncomputable section

open MvPowerSeries MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld
open CerednikDrinfeld.FormalODModule

universe u

namespace P2mKcODGrading

variable {p : ℕ} [hp : Fact p.Prime] {B : Type u} [CommRing B]

abbrev 𝔽 (p : ℕ) [Fact p.Prime] : Type := GaloisField p 2

abbrev teich (c : 𝔽 p) : Zp2 p := WittVector.teichmuller p c

def lam (j : Zp2 p →+* B) : 𝔽 p →* B := (j : Zp2 p →* B).comp (WittVector.teichmuller p)

@[scoped simp] theorem lam_apply (j : Zp2 p →+* B) (c : 𝔽 p) : lam j c = j (teich c) := rfl

theorem lam_zero (j : Zp2 p →+* B) : lam j 0 = 0 := by
  rw [lam_apply, teich, WittVector.teichmuller_zero, map_zero]

theorem lam_pow_pow_add_two (j : Zp2 p →+* B) (c : 𝔽 p) (n : ℕ) :
    lam j c ^ p ^ (n + 2) = lam j c ^ p ^ n :=
  apply_teichmuller_pow_pow_add_two j c n

theorem lam_pow_eq_lam_pow_pow (j : Zp2 p →+* B) (c : 𝔽 p) (n : ℕ) :
    lam j (c ^ p) ^ p ^ n = lam j c ^ p ^ (n + 1) := by
  rw [map_pow, ← pow_mul, ← pow_succ']

variable (X : FormalODModule p B)

def T (c : 𝔽 p) : CartierModule p X.F →+ CartierModule p X.F :=
  endAct (X.actEnd (teich c))

theorem T_apply (c : 𝔽 p) (f : CartierModule p X.F) :
    T X c f = endAct (X.actEnd (WittVector.teichmuller p c)) f := rfl

theorem actEnd_mul (a b : Zp2 p) : X.actEnd (a * b) = X.actEnd a * X.actEnd b := by
  rw [← actRingHom_apply, map_mul]; rfl

theorem endAct_mul_apply (φ ψ : MvFormalGroup.End X.F) (f : CartierModule p X.F) :
    endAct (φ * ψ) f = endAct φ (endAct ψ f) := by
  rw [map_mul]; rfl

theorem T_mul (c c' : 𝔽 p) (f : CartierModule p X.F) : T X (c * c') f = T X c (T X c' f) := by
  rw [T_apply, map_mul, actEnd_mul, endAct_mul_apply]; rfl

theorem T_zero (f : CartierModule p X.F) : T X 0 f = 0 := by
  rw [T_apply, WittVector.teichmuller_zero, ← actRingHom_apply, map_zero, map_zero]; rfl

theorem T_one (f : CartierModule p X.F) : T X 1 f = f := by
  rw [T_apply, map_one, ← actRingHom_apply, map_one, map_one]; rfl

theorem T_homothety (c : 𝔽 p) (b : B) (f : CartierModule p X.F) :
    T X c (homothety b f) = homothety b (T X c f) :=
  endAct_homothety _ b f

theorem T_comm (c : 𝔽 p) (a : Zp2 p) (f : CartierModule p X.F) :
    T X c (endAct (X.actEnd a) f) = endAct (X.actEnd a) (T X c f) := by
  rw [T_apply, ← endAct_mul_apply, ← actEnd_mul, mul_comm, actEnd_mul, endAct_mul_apply]
  rfl

variable [CharP B p]

theorem T_verschiebung (c : 𝔽 p) (f : CartierModule p X.F) :
    T X c (verschiebung f) = verschiebung (T X c f) :=
  endAct_verschiebung _ f

omit [CharP B p] in
theorem T_frobenius (c : 𝔽 p) (f : CartierModule p X.F) :
    T X c (frobenius f) = frobenius (T X c f) :=
  endAct_frobenius _ f

omit [CharP B p] in

theorem frobenius_teich (c : 𝔽 p) : WittVector.frobenius (teich c) = teich (c ^ p) := by
  rw [teich, WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

omit [CharP B p] in

theorem T_varpi (c : 𝔽 p) (f : CartierModule p X.F) :
    T X c (endAct X.varpiEnd f) = endAct X.varpiEnd (T X (c ^ p) f) := by
  rw [T_apply, T_apply, ← endAct_mul_apply, ← endAct_mul_apply, varpiEnd_mul_actEnd,
    frobenius_teich, ← pow_mul, ← pow_two, pow_card_galoisField]

omit [CharP B p] in
theorem mem_iff (j : Zp2 p →+* B) (n : ℕ) (f : CartierModule p X.F) :
    f ∈ X.gradedPiece j n ↔ ∀ c : 𝔽 p, T X c f = homothety (lam j c ^ p ^ n) f :=
  Iff.rfl

variable (j : Zp2 p →+* B)

theorem verschiebung_mem_iff (n : ℕ) (g : CartierModule p X.F) :
    verschiebung g ∈ X.gradedPiece j (n + 1) ↔ g ∈ X.gradedPiece j n := by
  rw [mem_iff, mem_iff]
  refine forall_congr' fun c => ?_
  rw [T_verschiebung, homothety_verschiebung, ← pow_mul, ← pow_succ,
    show n + 1 + 1 = n + 2 from rfl, lam_pow_pow_add_two]
  exact ⟨fun h => verschiebung_injective h, fun h => congrArg _ h⟩

theorem iterate_verschiebung_mem {n : ℕ} {g : CartierModule p X.F} (hg : g ∈ X.gradedPiece j n)
    (m : ℕ) : (⇑(verschiebung (p := p) (Φ := X.F)))^[m] g ∈ X.gradedPiece j (n + m) := by
  induction m with
  | zero => exact hg
  | succ m ih =>
    rw [Function.iterate_succ_apply', ← add_assoc]
    exact (verschiebung_mem_iff X j _ _).mpr ih

omit [CharP B p] in
theorem frobenius_mem {n : ℕ} {f : CartierModule p X.F} (hf : f ∈ X.gradedPiece j n) :
    frobenius f ∈ X.gradedPiece j (n + 1) := by
  rw [mem_iff] at hf ⊢
  intro c
  rw [T_frobenius, hf c, frobenius_homothety, ← pow_mul, ← pow_succ]

omit [CharP B p] in
theorem varpi_mem {n : ℕ} {f : CartierModule p X.F} (hf : f ∈ X.gradedPiece j n) :
    endAct X.varpiEnd f ∈ X.gradedPiece j (n + 1) := by
  rw [mem_iff] at hf ⊢
  intro c
  rw [T_varpi, hf (c ^ p), lam_pow_eq_lam_pow_pow, endAct_homothety]

omit [CharP B p] in
theorem homothety_mem {n : ℕ} (b : B) {f : CartierModule p X.F} (hf : f ∈ X.gradedPiece j n) :
    homothety b f ∈ X.gradedPiece j n := by
  rw [mem_iff] at hf ⊢
  intro c
  rw [T_homothety, hf c, homothety_comm]

omit [CharP B p] in
theorem act_mem {n : ℕ} (a : Zp2 p) {f : CartierModule p X.F} (hf : f ∈ X.gradedPiece j n) :
    endAct (X.actEnd a) f ∈ X.gradedPiece j n := by
  rw [mem_iff] at hf ⊢
  intro c
  rw [T_comm, hf c, endAct_homothety]

scoped instance instFintypeUnitsF : Fintype (𝔽 p)ˣ := Fintype.ofFinite _

omit [CharP B p] in
theorem card_units_F : Fintype.card (𝔽 p)ˣ = p ^ 2 - 1 := by
  rw [Fintype.card_eq_nat_card, Nat.card_units, GaloisField.card p 2 two_ne_zero]

omit [CharP B p] in

theorem exists_pow_ne_one : ∃ ω : (𝔽 p)ˣ, ω ^ (p - 1) ≠ 1 := by
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := (𝔽 p)ˣ)
  refine ⟨ω, pow_ne_one_of_lt_orderOf (Nat.sub_ne_zero_of_lt hp.out.one_lt) ?_⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hω, Nat.card_units, GaloisField.card p 2 two_ne_zero]
  exact Nat.sub_lt_sub_right hp.out.one_lt.le
    (by rw [pow_two]; exact (Nat.lt_mul_iff_one_lt_left hp.out.pos).mpr hp.out.one_lt)

omit [CharP B p] in

theorem isUnit_one_sub_lam (u : (𝔽 p)ˣ) (hu : u ≠ 1) : IsUnit (1 - lam j u) := by
  have h1 : IsUnit (1 - teich (u : 𝔽 p)) := by
    refine WittVector.isUnit_of_coeff_zero_ne_zero _ ?_
    rw [← WittVector.constantCoeff_apply, map_sub, map_one, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero, sub_ne_zero, ne_comm, Ne, Units.val_eq_one]
    exact hu
  simpa using h1.map j

omit [CharP B p] in

theorem sum_eq_zero_of_isUnit (χ : (𝔽 p)ˣ →* B) (u : (𝔽 p)ˣ) (hu : IsUnit (1 - χ u)) :
    ∑ c : (𝔽 p)ˣ, χ c = 0 := by
  have h : ∑ c : (𝔽 p)ˣ, χ (u * c) = ∑ c : (𝔽 p)ˣ, χ c :=
    Fintype.sum_equiv (Equiv.mulLeft u) _ _ fun c => rfl
  simp only [map_mul, ← Finset.mul_sum] at h
  rw [← hu.mul_right_eq_zero, sub_mul, one_mul, h, sub_self]

def chi (j : Zp2 p →+* B) : (𝔽 p)ˣ →* B :=
  (lam j).comp ((Units.coeHom (𝔽 p)).comp (powMonoidHom (p - 1)))

omit [CharP B p] in
@[scoped simp] theorem chi_apply (c : (𝔽 p)ˣ) : chi j c = lam j ((c ^ (p - 1) : (𝔽 p)ˣ) : 𝔽 p) := rfl

omit [CharP B p] in
theorem sum_chi_eq_zero : ∑ c : (𝔽 p)ˣ, chi j c = 0 := by
  obtain ⟨ω, hω⟩ := exists_pow_ne_one (p := p)
  exact sum_eq_zero_of_isUnit (chi j) ω (isUnit_one_sub_lam j _ hω)

omit [CharP B p] in
theorem sum_chi_inv_eq_zero : ∑ c : (𝔽 p)ˣ, chi j c⁻¹ = 0 := by
  obtain ⟨ω, hω⟩ := exists_pow_ne_one (p := p)
  have h := sum_eq_zero_of_isUnit ((chi j).comp invMonoidHom) ω (by
    show IsUnit (1 - chi j ω⁻¹)
    rw [chi_apply, inv_pow]
    exact isUnit_one_sub_lam j _ (by rwa [Ne, inv_eq_one]))
  simpa using h

omit [CharP B p] in

theorem lam_inv_mul_lam_pow (c : (𝔽 p)ˣ) :
    lam j (c⁻¹ : (𝔽 p)ˣ) * lam j c ^ p = chi j c := by
  rw [chi_apply, ← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
  congr 2
  have hp1 : c ^ p = c * c ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le]
  rw [hp1, inv_mul_cancel_left]

omit [CharP B p] in

theorem lam_inv_pow_mul_lam (c : (𝔽 p)ˣ) :
    lam j (c⁻¹ : (𝔽 p)ˣ) ^ p * lam j c = chi j c⁻¹ := by
  rw [chi_apply, ← map_pow, ← map_mul, ← Units.val_pow_eq_pow_val, ← Units.val_mul]
  congr 2
  have hp1 : c ^ p = c * c ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp.out.one_lt.le]
  rw [inv_pow, hp1, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, inv_pow]

omit [CharP B p] in
theorem lam_inv_mul_lam (c : (𝔽 p)ˣ) : lam j (c⁻¹ : (𝔽 p)ˣ) * lam j c = 1 := by
  rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]

theorem card_units_smul (v : Fin 2 → B) : (Fintype.card (𝔽 p)ˣ) • v = -v := by
  rw [card_units_F, ← Nat.cast_smul_eq_nsmul B, Nat.cast_sub (Nat.one_le_pow _ _ hp.out.pos),
    Nat.cast_pow, CharP.cast_eq_zero B p, zero_pow two_ne_zero, zero_sub, Nat.cast_one, neg_one_smul]

omit [CharP B p] in

theorem exists_eq_teich_add (a : Zp2 p) : ∃ (c : 𝔽 p) (b : Zp2 p), a = teich c + p * b := by
  set x := a - teich (a.coeff 0) with hx
  by_cases h0 : x = 0
  · exact ⟨a.coeff 0, 0, by rw [mul_zero, add_zero]; exact (sub_eq_zero.mp h0)⟩
  obtain ⟨m, b, hb, hxb⟩ := WittVector.exists_eq_pow_p_mul x h0
  cases m with
  | zero =>
    exfalso
    apply hb
    have hx0 : x.coeff 0 = 0 := by
      rw [hx, ← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero, sub_self]
    rwa [hxb, pow_zero, one_mul] at hx0
  | succ m =>
    refine ⟨a.coeff 0, (p : Zp2 p) ^ m * b, ?_⟩
    rw [← mul_assoc, ← pow_succ', ← hxb, hx, add_sub_cancel]

def linAct : Zp2 p →+* Matrix (Fin 2) (Fin 2) B := (linearPartHom X.F).comp X.actRingHom

omit [CharP B p] in
theorem lieAct_apply (a : Zp2 p) (v : Fin 2 → B) : X.lieAct a v = (linAct X a).mulVec v := rfl

theorem linAct_teich_add (c : 𝔽 p) (b : Zp2 p) :
    linAct X (teich c + p * b) = linAct X (teich c) := by
  rw [map_add, add_eq_left, ← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul B,
    CharP.cast_eq_zero B p, zero_smul]

theorem j_teich_add (c : 𝔽 p) (b : Zp2 p) : j (teich c + p * b) = lam j c := by
  rw [map_add, map_mul, map_natCast, CharP.cast_eq_zero B p, zero_mul, add_zero, lam_apply]

theorem j_frobenius_teich_add (c : 𝔽 p) (b : Zp2 p) :
    j (WittVector.frobenius (teich c + p * b)) = lam j c ^ p := by
  rw [map_add, map_mul, map_natCast, frobenius_teich, j_teich_add, map_pow]

theorem mem_lieZero_iff (v : Fin 2 → B) :
    v ∈ X.lieZero j ↔ ∀ c : 𝔽 p, X.lieAct (teich c) v = lam j c • v := by
  constructor
  · intro hv c
    have h := (Submodule.mem_iInf _).mp hv (teich c)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero] at h
    exact h
  · intro hv
    refine (Submodule.mem_iInf _).mpr fun a => ?_
    obtain ⟨c, b, rfl⟩ := exists_eq_teich_add a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, lieAct_apply, linAct_teich_add, ← lieAct_apply, hv c, j_teich_add]

theorem mem_lieOne_iff (v : Fin 2 → B) :
    v ∈ X.lieOne j ↔ ∀ c : 𝔽 p, X.lieAct (teich c) v = lam j c ^ p • v := by
  constructor
  · intro hv c
    have h := (Submodule.mem_iInf _).mp hv (teich c)
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, frobenius_teich] at h
    rw [← map_pow]
    exact h
  · intro hv
    refine (Submodule.mem_iInf _).mpr fun a => ?_
    obtain ⟨c, b, rfl⟩ := exists_eq_teich_add a
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
      sub_eq_zero, lieAct_apply, linAct_teich_add, ← lieAct_apply, hv c, j_frobenius_teich_add]

omit [CharP B p] in
theorem tangent_T (c : 𝔽 p) (f : CartierModule p X.F) :
    tangent (T X c f) = X.lieAct (teich c) (tangent f) := by
  rw [T_apply, endAct_apply, tangent_map]
  rfl

def rho (n : ℕ) (c : (𝔽 p)ˣ) : CartierModule p X.F →+ CartierModule p X.F :=
  (homothety (lam j (c⁻¹ : (𝔽 p)ˣ) ^ p ^ n)).comp (T X c)

def E (n : ℕ) : CartierModule p X.F →+ CartierModule p X.F := ∑ c : (𝔽 p)ˣ, rho X j n c

omit [CharP B p] in
theorem rho_apply (n : ℕ) (c : (𝔽 p)ˣ) (f : CartierModule p X.F) :
    rho X j n c f = homothety (lam j (c⁻¹ : (𝔽 p)ˣ) ^ p ^ n) (T X c f) := rfl

omit [CharP B p] in
theorem E_apply (n : ℕ) (f : CartierModule p X.F) :
    E X j n f = ∑ c : (𝔽 p)ˣ, homothety (lam j (c⁻¹ : (𝔽 p)ˣ) ^ p ^ n) (T X c f) := by
  rw [E, AddMonoidHom.finsetSum_apply]
  rfl

omit [CharP B p] in
theorem rho_mul (n : ℕ) (c c' : (𝔽 p)ˣ) (f : CartierModule p X.F) :
    rho X j n (c * c') f = rho X j n c (rho X j n c' f) := by
  rw [rho_apply, rho_apply, rho_apply, mul_inv, Units.val_mul, Units.val_mul, map_mul, mul_pow,
    homothety_mul, T_mul, T_homothety]

omit [CharP B p] in

theorem rho_E (n : ℕ) (c : (𝔽 p)ˣ) (f : CartierModule p X.F) :
    rho X j n c (E X j n f) = E X j n f := by
  rw [E, AddMonoidHom.finsetSum_apply, map_sum]
  simp only [← rho_mul]
  exact Fintype.sum_equiv (Equiv.mulLeft c) _ _ fun c' => rfl

omit [CharP B p] in
theorem E_add_two (n : ℕ) (f : CartierModule p X.F) : E X j (n + 2) f = E X j n f := by
  simp only [E_apply, lam_pow_pow_add_two]

omit [CharP B p] in
theorem E_add_E_succ (m : ℕ) (f : CartierModule p X.F) :
    E X j m f + E X j (m + 1) f = E X j 0 f + E X j 1 f := by
  induction m with
  | zero => rfl
  | succ m ih => rw [show m + 1 + 1 = m + 2 from rfl, E_add_two, add_comm, ih]

omit [CharP B p] in

theorem E_mem (n : ℕ) (f : CartierModule p X.F) : E X j n f ∈ X.gradedPiece j n := by
  rw [mem_iff]
  intro c
  by_cases hc : c = 0
  · subst hc
    rw [T_zero, lam_zero, zero_pow (pow_ne_zero n hp.out.ne_zero), homothety_zero_left]
  set u : (𝔽 p)ˣ := Units.mk0 c hc with hu
  have hcu : c = (u : 𝔽 p) := (Units.val_mk0 hc).symm
  have key := congrArg (homothety (lam j (u : 𝔽 p) ^ p ^ n)) (rho_E X j n u f)
  rw [rho_apply, ← homothety_mul, ← mul_pow, ← map_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, map_one, one_pow, homothety_one] at key
  rw [hcu, key]

omit [CharP B p] in

theorem tangent_rho (n : ℕ) (c : (𝔽 p)ˣ) (f : CartierModule p X.F) (v0 v1 : Fin 2 → B)
    (hv : tangent f = v0 + v1) (h0 : ∀ c : 𝔽 p, X.lieAct (teich c) v0 = lam j c • v0)
    (h1 : ∀ c : 𝔽 p, X.lieAct (teich c) v1 = lam j c ^ p • v1) :
    tangent (rho X j n c f) =
      (lam j (c⁻¹ : (𝔽 p)ˣ) ^ p ^ n * lam j c) • v0 +
        (lam j (c⁻¹ : (𝔽 p)ˣ) ^ p ^ n * lam j c ^ p) • v1 := by
  rw [rho_apply, tangent_homothety, tangent_T, hv, map_add, h0, h1, smul_add, smul_smul, smul_smul]

theorem tangent_E_zero (f : CartierModule p X.F) (v0 v1 : Fin 2 → B)
    (hv : tangent f = v0 + v1) (h0 : ∀ c : 𝔽 p, X.lieAct (teich c) v0 = lam j c • v0)
    (h1 : ∀ c : 𝔽 p, X.lieAct (teich c) v1 = lam j c ^ p • v1) :
    tangent (E X j 0 f) = -v0 := by
  rw [E, AddMonoidHom.finsetSum_apply, map_sum]
  simp only [tangent_rho X j 0 _ f v0 v1 hv h0 h1, pow_zero, pow_one, lam_inv_mul_lam,
    lam_inv_mul_lam_pow, one_smul, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    ← Finset.sum_smul, sum_chi_eq_zero, zero_smul, add_zero]
  exact card_units_smul v0

theorem tangent_E_one (f : CartierModule p X.F) (v0 v1 : Fin 2 → B)
    (hv : tangent f = v0 + v1) (h0 : ∀ c : 𝔽 p, X.lieAct (teich c) v0 = lam j c • v0)
    (h1 : ∀ c : 𝔽 p, X.lieAct (teich c) v1 = lam j c ^ p • v1) :
    tangent (E X j 1 f) = -v1 := by
  rw [E, AddMonoidHom.finsetSum_apply, map_sum]
  have h2 : ∀ c : (𝔽 p)ˣ, lam j (c⁻¹ : (𝔽 p)ˣ) ^ p * lam j c ^ p = 1 := fun c => by
    rw [← mul_pow, lam_inv_mul_lam, one_pow]
  simp only [tangent_rho X j 1 _ f v0 v1 hv h0 h1, pow_one, lam_inv_pow_mul_lam, h2, one_smul,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.sum_smul,
    sum_chi_inv_eq_zero, zero_smul, zero_add]
  exact card_units_smul v1

theorem eq_zero_of_forall_exists (y : CartierModule p X.F)
    (hy : ∀ N : ℕ, ∃ t : CartierModule p X.F,
      y = (⇑(verschiebung (p := p) (Φ := X.F)))^[N] t) : y = 0 := by
  have hu := MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebung_iterate_add
    p X.F (fun _ => 0)
  have hsum : ∀ N : ℕ, (∑ m ∈ Finset.range N,
      (⇑(verschiebung (p := p) (Φ := X.F)))^[m] ((fun _ : ℕ => (0 : CartierModule p X.F)) m)) = 0 :=
    fun N => Finset.sum_eq_zero fun m _ => iterate_map_zero _ m
  refine hu.unique (fun N => ?_) (fun N => ⟨0, ?_⟩)
  · obtain ⟨t, ht⟩ := hy N
    exact ⟨t, by rw [hsum, zero_add]; exact ht⟩
  · rw [hsum, zero_add, iterate_map_zero]

theorem homothety_iterate_verschiebung (b : B) (N : ℕ) (t : CartierModule p X.F) :
    homothety b ((⇑(verschiebung (p := p) (Φ := X.F)))^[N] t) =
      (⇑(verschiebung (p := p) (Φ := X.F)))^[N] (homothety (b ^ p ^ N) t) := by
  induction N generalizing b with
  | zero => rw [Function.iterate_zero_apply, Function.iterate_zero_apply, pow_zero, pow_one]
  | succ N ih =>
    rw [Function.iterate_succ_apply', homothety_verschiebung, ih,
      ← Function.iterate_succ_apply' (⇑(verschiebung (p := p) (Φ := X.F))), ← pow_mul, ← pow_succ']

theorem T_iterate_verschiebung (c : 𝔽 p) (N : ℕ) (t : CartierModule p X.F) :
    T X c ((⇑(verschiebung (p := p) (Φ := X.F)))^[N] t) =
      (⇑(verschiebung (p := p) (Φ := X.F)))^[N] (T X c t) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', T_verschiebung, ih,
      ← Function.iterate_succ_apply' (⇑(verschiebung (p := p) (Φ := X.F)))]

theorem mem_of_limit {n : ℕ} (y : ℕ → CartierModule p X.F)
    (hy : ∀ m, (⇑(verschiebung (p := p) (Φ := X.F)))^[m] (y m) ∈ X.gradedPiece j n)
    (s : CartierModule p X.F)
    (hs : ∀ N : ℕ, ∃ t : CartierModule p X.F,
      s = (∑ m ∈ Finset.range N, (⇑(verschiebung (p := p) (Φ := X.F)))^[m] (y m)) +
        (⇑(verschiebung (p := p) (Φ := X.F)))^[N] t) :
    s ∈ X.gradedPiece j n := by
  rw [mem_iff]
  intro c
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_exists X _ fun N => ?_
  obtain ⟨t, ht⟩ := hs N
  refine ⟨T X c t - homothety ((lam j c ^ p ^ n) ^ p ^ N) t, ?_⟩
  have hS : T X c (∑ m ∈ Finset.range N, (⇑(verschiebung (p := p) (Φ := X.F)))^[m] (y m)) =
      homothety (lam j c ^ p ^ n)
        (∑ m ∈ Finset.range N, (⇑(verschiebung (p := p) (Φ := X.F)))^[m] (y m)) := by
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun m _ => (mem_iff X j n _).mp (hy m) c
  rw [ht, map_add, map_add, hS, add_sub_add_left_eq_sub, T_iterate_verschiebung,
    homothety_iterate_verschiebung, iterate_map_sub]

omit [CharP B p] in

theorem exists_isUnit_lam_sub : ∃ ω : (𝔽 p)ˣ, IsUnit (lam j ω - lam j ω ^ p) := by
  obtain ⟨ω, hω⟩ := exists_pow_ne_one (p := p)
  refine ⟨ω, ?_⟩
  have h1 : lam j ω - lam j ω ^ p = lam j ω * (1 - lam j ((ω ^ (p - 1) : (𝔽 p)ˣ) : 𝔽 p)) := by
    rw [mul_sub, mul_one, Units.val_pow_eq_pow_val, map_pow, ← pow_succ',
      Nat.sub_add_cancel hp.out.one_lt.le]
  rw [h1]
  exact ((Units.isUnit ω).map (lam j)).mul (isUnit_one_sub_lam j _ hω)

omit [CharP B p] in

theorem tangent_eq_zero_of_mem_mem {t : CartierModule p X.F} (h0 : t ∈ X.gradedPiece j 0)
    (h1 : t ∈ X.gradedPiece j 1) : tangent t = 0 := by
  obtain ⟨ω, hω⟩ := exists_isUnit_lam_sub (p := p) j
  have e0 := congrArg tangent ((mem_iff X j 0 t).mp h0 ω)
  have e1 := congrArg tangent ((mem_iff X j 1 t).mp h1 ω)
  rw [tangent_homothety, pow_zero, pow_one] at e0
  rw [tangent_homothety, pow_one] at e1
  have h : (lam j ω - lam j ω ^ p) • tangent t = 0 := by rw [sub_smul, ← e0, ← e1, sub_self]
  obtain ⟨u, hu⟩ := hω
  rw [← hu, ← Units.smul_def] at h
  rw [← inv_smul_smul u (tangent t), h, smul_zero]

theorem eq_zero_of_mem_mem {f : CartierModule p X.F} (h0 : f ∈ X.gradedPiece j 0)
    (h1 : f ∈ X.gradedPiece j 1) : f = 0 := by
  have key : ∀ N : ℕ, ∃ t : CartierModule p X.F,
      f = (⇑(verschiebung (p := p) (Φ := X.F)))^[N] t ∧
        t ∈ X.gradedPiece j 0 ∧ t ∈ X.gradedPiece j 1 := by
    intro N
    induction N with
    | zero => exact ⟨f, rfl, h0, h1⟩
    | succ N ih =>
      obtain ⟨t, hft, ht0, ht1⟩ := ih
      obtain ⟨g, hg⟩ :=
        (MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebung_eq p X.F t).mp
          (tangent_eq_zero_of_mem_mem X j ht0 ht1)
      have hg1 : g ∈ X.gradedPiece j 1 := by
        rw [← verschiebung_mem_iff, hg, show (1 : ℕ) + 1 = 0 + 2 from rfl, gradedPiece_add_two]
        exact ht0
      have hg0 : g ∈ X.gradedPiece j 0 := by
        rw [← verschiebung_mem_iff, hg]
        exact ht1
      exact ⟨g, by rw [hft, ← hg, Function.iterate_succ_apply], hg0, hg1⟩
  exact eq_zero_of_forall_exists X f fun N => (key N).imp fun t ht => ht.1

variable {X j}

section Sup

variable (hLie : IsCompl (X.lieZero j) (X.lieOne j))
include hLie

theorem exists_lie_decomp (v : Fin 2 → B) :
    ∃ v0 v1 : Fin 2 → B, v = v0 + v1 ∧ (∀ c : 𝔽 p, X.lieAct (teich c) v0 = lam j c • v0) ∧
      (∀ c : 𝔽 p, X.lieAct (teich c) v1 = lam j c ^ p • v1) := by
  have hv : v ∈ X.lieZero j ⊔ X.lieOne j := by rw [hLie.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨v0, hv0, v1, hv1, rfl⟩ := Submodule.mem_sup.mp hv
  exact ⟨v0, v1, rfl, (mem_lieZero_iff X j v0).mp hv0, (mem_lieOne_iff X j v1).mp hv1⟩

theorem exists_verschiebung_eq (f : CartierModule p X.F) :
    ∃ g : CartierModule p X.F, verschiebung g = f + E X j 0 f + E X j 1 f := by
  refine (MvFormalGroup.CartierModule.tangent_eq_zero_iff_exists_verschiebung_eq p X.F _).mp ?_
  obtain ⟨v0, v1, hv, h0, h1⟩ := exists_lie_decomp hLie (tangent f)
  rw [map_add, map_add, tangent_E_zero X j f v0 v1 hv h0 h1, tangent_E_one X j f v0 v1 hv h0 h1,
    hv]
  abel

def rem (f : CartierModule p X.F) : ℕ → CartierModule p X.F
  | 0 => f
  | m + 1 => Classical.choose (exists_verschiebung_eq hLie (rem f m))

theorem rem_zero (f : CartierModule p X.F) : rem hLie f 0 = f := rfl

theorem verschiebung_rem_succ (f : CartierModule p X.F) (m : ℕ) :
    verschiebung (rem hLie f (m + 1)) = rem hLie f m + E X j 0 (rem hLie f m) +
      E X j 1 (rem hLie f m) :=
  Classical.choose_spec (exists_verschiebung_eq hLie (rem hLie f m))

def y0 (f : CartierModule p X.F) (m : ℕ) : CartierModule p X.F := -E X j m (rem hLie f m)

def y1 (f : CartierModule p X.F) (m : ℕ) : CartierModule p X.F := -E X j (m + 1) (rem hLie f m)

theorem iterate_y0_mem (f : CartierModule p X.F) (m : ℕ) :
    (⇑(verschiebung (p := p) (Φ := X.F)))^[m] (y0 hLie f m) ∈ X.gradedPiece j 0 := by
  have h := iterate_verschiebung_mem X j (neg_mem (E_mem X j m (rem hLie f m))) m
  rwa [← two_mul, ← zero_add (2 * m), gradedPiece_add_two_mul] at h

theorem iterate_y1_mem (f : CartierModule p X.F) (m : ℕ) :
    (⇑(verschiebung (p := p) (Φ := X.F)))^[m] (y1 hLie f m) ∈ X.gradedPiece j 1 := by
  have h := iterate_verschiebung_mem X j (neg_mem (E_mem X j (m + 1) (rem hLie f m))) m
  rwa [show m + 1 + m = 1 + 2 * m by ring, gradedPiece_add_two_mul] at h

theorem sum_add_sum_add_iterate (f : CartierModule p X.F) (N : ℕ) :
    (∑ m ∈ Finset.range N, (⇑(verschiebung (p := p) (Φ := X.F)))^[m] (y0 hLie f m)) +
      (∑ m ∈ Finset.range N, (⇑(verschiebung (p := p) (Φ := X.F)))^[m] (y1 hLie f m)) +
        (⇑(verschiebung (p := p) (Φ := X.F)))^[N] (rem hLie f N) = f := by
  induction N with
  | zero => simp [rem_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Function.iterate_succ_apply,
      verschiebung_rem_succ]
    have hy : y0 hLie f N + y1 hLie f N =
        -(E X j 0 (rem hLie f N) + E X j 1 (rem hLie f N)) := by
      rw [y0, y1, ← neg_add, E_add_E_succ]
    have key : (⇑(verschiebung (p := p) (Φ := X.F)))^[N] (y0 hLie f N) +
        (⇑(verschiebung (p := p) (Φ := X.F)))^[N] (y1 hLie f N) +
        (⇑(verschiebung (p := p) (Φ := X.F)))^[N]
          (rem hLie f N + E X j 0 (rem hLie f N) + E X j 1 (rem hLie f N)) =
        (⇑(verschiebung (p := p) (Φ := X.F)))^[N] (rem hLie f N) := by
      rw [← iterate_map_add, ← iterate_map_add, hy]
      congr 1
      abel
    rw [← key] at ih
    refine Eq.trans ?_ ih
    abel

private theorem _root_.P2mKcODGrading.mem_sup (f : CartierModule p X.F) : f ∈ X.gradedPiece j 0 ⊔ X.gradedPiece j 1 := by
  obtain ⟨s0, hs0, -⟩ :=
    MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebung_iterate_add p X.F
      (y0 hLie f)
  obtain ⟨s1, hs1, -⟩ :=
    MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebung_iterate_add p X.F
      (y1 hLie f)
  have h0 : s0 ∈ X.gradedPiece j 0 := mem_of_limit X j (y0 hLie f) (iterate_y0_mem hLie f) s0 hs0
  have h1 : s1 ∈ X.gradedPiece j 1 := mem_of_limit X j (y1 hLie f) (iterate_y1_mem hLie f) s1 hs1
  have hf : f - s0 - s1 = 0 := by
    refine eq_zero_of_forall_exists X _ fun N => ?_
    obtain ⟨t0, ht0⟩ := hs0 N
    obtain ⟨t1, ht1⟩ := hs1 N
    refine ⟨rem hLie f N - t0 - t1, ?_⟩
    rw [iterate_map_sub, iterate_map_sub]
    conv_lhs => rw [← sum_add_sum_add_iterate hLie f N, ht0, ht1]
    abel
  rw [sub_sub, sub_eq_zero] at hf
  rw [hf]
  exact AddSubgroup.add_mem_sup h0 h1

p2m_export "P2mKcODGrading" "mem_sup"
end Sup

theorem map_tangent_zero :
    (X.gradedPiece j 0).map tangent = (X.lieZero j).toAddSubgroup := by
  ext v
  rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, mem_lieZero_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩ c
    have h := congrArg tangent ((mem_iff X j 0 f).mp hf c)
    rwa [tangent_T, tangent_homothety, pow_zero, pow_one] at h
  · intro hv
    obtain ⟨g, hg⟩ := MvFormalGroup.CartierModule.tangent_surjective p X.F v
    refine ⟨-E X j 0 g, neg_mem (E_mem X j 0 g), ?_⟩
    rw [map_neg, tangent_E_zero X j g v 0 (by rw [hg, add_zero]) hv
      (fun c => by rw [map_zero, smul_zero]), neg_neg]

theorem map_tangent_one :
    (X.gradedPiece j 1).map tangent = (X.lieOne j).toAddSubgroup := by
  ext v
  rw [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, mem_lieOne_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩ c
    have h := congrArg tangent ((mem_iff X j 1 f).mp hf c)
    rwa [tangent_T, tangent_homothety, pow_one] at h
  · intro hv
    obtain ⟨g, hg⟩ := MvFormalGroup.CartierModule.tangent_surjective p X.F v
    refine ⟨-E X j 1 g, neg_mem (E_mem X j 1 g), ?_⟩
    rw [map_neg, tangent_E_one X j g 0 v (by rw [hg, zero_add])
      (fun c => by rw [map_zero, smul_zero]) hv, neg_neg]

end P2mKcODGrading
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne.P2mKcODGrading"

open P2mKcODGrading in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [CharP B p]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B)
    (hLie : IsCompl (X.lieZero j) (X.lieOne j)) :
    IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1) ∧
    (∀ (n : ℕ) (g : MvFormalGroup.CartierModule p X.F),
        MvFormalGroup.CartierModule.verschiebung g ∈ X.gradedPiece j (n + 1) ↔
          g ∈ X.gradedPiece j n) ∧
    (∀ n, ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.frobenius f ∈ X.gradedPiece j (n + 1)) ∧
    (∀ n, ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.endAct X.varpiEnd f ∈ X.gradedPiece j (n + 1)) ∧
    (∀ (n : ℕ) (b : B), ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.homothety b f ∈ X.gradedPiece j n) ∧
    (∀ (n : ℕ) (a : CerednikDrinfeld.Zp2 p), ∀ f ∈ X.gradedPiece j n,
        MvFormalGroup.CartierModule.endAct (X.actEnd a) f ∈ X.gradedPiece j n) ∧
    (X.gradedPiece j 0).map MvFormalGroup.CartierModule.tangent = (X.lieZero j).toAddSubgroup ∧
    (X.gradedPiece j 1).map MvFormalGroup.CartierModule.tangent = (X.lieOne j).toAddSubgroup := by
  refine ⟨?_, verschiebung_mem_iff X j, fun n f hf => frobenius_mem X j hf,
    fun n f hf => varpi_mem X j hf, fun n b f hf => homothety_mem X j b hf,
    fun n a f hf => act_mem X j a hf, map_tangent_zero, map_tangent_one⟩
  refine isCompl_iff.mpr ⟨AddSubgroup.disjoint_def.mpr fun h0 h1 => eq_zero_of_mem_mem X j h0 h1,
    codisjoint_iff.mpr ((AddSubgroup.eq_top_iff' _).mpr (mem_sup hLie))⟩

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne.P2mKcODGrading"

end S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne (solution)
