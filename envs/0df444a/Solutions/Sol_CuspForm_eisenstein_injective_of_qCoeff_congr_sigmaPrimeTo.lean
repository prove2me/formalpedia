-- Prove2me | solution 1 for CuspForm.eisenstein_injective_of_qCoeff_congr_sigmaPrimeTo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/9cf22271-67df-5e6f-940a-7187550b3cd0

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_ModularCurve_HeckeProj
import Definitions.Def_ModularCurve_EisensteinTwoCoeff
import Definitions.Def_CuspForm_IntegralLattice
import Theorems.Thm_ModularFormClass_qCoeff_heckeT
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.NumberTheory.Divisors
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_eisenstein_injective_of_qCoeff_congr_sigmaPrimeTo
set_option autoImplicit false
noncomputable section
open ModularCurve

namespace S09RC

section Sigma

open Finset

variable {p : ℕ}

private abbrev pdiv (p n : ℕ) : Finset ℕ := n.divisors.filter (fun d => ¬ p ∣ d)

private theorem sigmaPrimeTo_eq (n : ℕ) : ModularCurve.sigmaPrimeTo p n = ∑ d ∈ pdiv p n, d := rfl

private theorem sigmaPrimeTo_mul_self (hp : p.Prime) {n : ℕ} (hn : n ≠ 0) :
    ModularCurve.sigmaPrimeTo p (n * p) = ModularCurve.sigmaPrimeTo p n := by
  rw [sigmaPrimeTo_eq, sigmaPrimeTo_eq]
  congr 1
  ext d
  simp only [pdiv, mem_filter, Nat.mem_divisors, ne_eq, mul_eq_zero, hn, hp.ne_zero, or_self,
    not_false_eq_true, and_true]
  constructor
  · rintro ⟨hd, hpd⟩
    exact ⟨(Nat.Coprime.dvd_of_dvd_mul_right
      ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd))) hd), hpd⟩
  · rintro ⟨hd, hpd⟩
    exact ⟨Dvd.dvd.mul_right hd p, hpd⟩

private theorem pdiv_mul (hp : p.Prime) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) {n : ℕ}
    (hn : n ≠ 0) :
    pdiv p (n * ℓ) = pdiv p n ∪ (pdiv p n).image (fun d => ℓ * d) := by
  ext d
  simp only [pdiv, mem_union, mem_image, mem_filter, Nat.mem_divisors, ne_eq, mul_eq_zero, hn,
    hℓ.ne_zero, or_self, not_false_eq_true, and_true]
  constructor
  · rintro ⟨hd, hpd⟩
    by_cases hℓd : ℓ ∣ d
    · obtain ⟨e, rfl⟩ := hℓd
      right
      refine ⟨e, ⟨?_, fun h => hpd (Dvd.dvd.mul_left h ℓ)⟩, rfl⟩
      rw [mul_comm n ℓ] at hd
      exact Nat.dvd_of_mul_dvd_mul_left hℓ.pos hd
    · left
      exact ⟨(Nat.Coprime.dvd_of_dvd_mul_right
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓd)) hd), hpd⟩
  · rintro (⟨hd, hpd⟩ | ⟨e, ⟨he, hpe⟩, rfl⟩)
    · exact ⟨Dvd.dvd.mul_right hd ℓ, hpd⟩
    · refine ⟨by rw [mul_comm n ℓ]; exact Nat.mul_dvd_mul_left ℓ he, ?_⟩
      intro h
      exact hpe ((Nat.Coprime.dvd_of_dvd_mul_left
        ((Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp))) h)

private theorem pdiv_inter_image (hp : p.Prime) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) {n : ℕ}
    (hn : n ≠ 0) :
    pdiv p n ∩ (pdiv p n).image (fun d => ℓ * d)
      = if ℓ ∣ n then (pdiv p (n / ℓ)).image (fun d => ℓ * d) else ∅ := by
  ext d
  split_ifs with hℓn
  · obtain ⟨n', rfl⟩ := hℓn
    have hn' : n' ≠ 0 := by rintro rfl; simp at hn
    rw [Nat.mul_div_cancel_left n' hℓ.pos]
    simp only [pdiv, mem_inter, mem_image, mem_filter, Nat.mem_divisors, ne_eq, mul_eq_zero,
      hℓ.ne_zero, hn', or_self, not_false_eq_true, and_true]
    constructor
    · rintro ⟨⟨hd, hpd⟩, e, ⟨-, -⟩, rfl⟩
      exact ⟨e, ⟨Nat.dvd_of_mul_dvd_mul_left hℓ.pos hd, fun h => hpd (Dvd.dvd.mul_left h ℓ)⟩, rfl⟩
    · rintro ⟨e, ⟨he, hpe⟩, rfl⟩
      refine ⟨⟨Nat.mul_dvd_mul_left ℓ he, ?_⟩, e, ⟨Dvd.dvd.mul_left he ℓ, hpe⟩, rfl⟩
      intro h
      exact hpe (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp hℓ).mpr (Ne.symm hℓp)) h)
  · simp only [pdiv, mem_inter, mem_image, mem_filter, Nat.mem_divisors, ne_eq, hn,
      not_false_eq_true, and_true, notMem_empty, iff_false, not_and, not_exists]
    rintro ⟨hd, -⟩ e ⟨-, -⟩ rfl
    exact hℓn (dvd_trans (Dvd.intro e rfl) hd)

private theorem sum_image_mul (ℓ : ℕ) (hℓ : ℓ ≠ 0) (s : Finset ℕ) :
    ∑ d ∈ s.image (fun d => ℓ * d), d = ℓ * ∑ d ∈ s, d := by
  rw [sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hℓ) h), mul_sum]

private theorem sigmaPrimeTo_mul_prime (hp : p.Prime) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    {n : ℕ} (hn : n ≠ 0) :
    ModularCurve.sigmaPrimeTo p (n * ℓ)
        + (if ℓ ∣ n then ℓ * ModularCurve.sigmaPrimeTo p (n / ℓ) else 0)
      = (1 + ℓ) * ModularCurve.sigmaPrimeTo p n := by
  have h := sum_union_inter (s₁ := pdiv p n) (s₂ := (pdiv p n).image (fun d => ℓ * d))
    (f := fun d => d)
  rw [← pdiv_mul hp hℓ hℓp hn, pdiv_inter_image hp hℓ hℓp hn, sum_image_mul ℓ hℓ.ne_zero] at h
  simp only [sigmaPrimeTo_eq]
  by_cases hℓn : ℓ ∣ n
  · rw [if_pos hℓn, sum_image_mul ℓ hℓ.ne_zero] at h
    rw [if_pos hℓn, h]; ring
  · rw [if_neg hℓn, sum_empty, add_zero] at h
    rw [if_neg hℓn, add_zero, h]; ring

end Sigma

section Forms

private theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ Subgroup.strictPeriods
      (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)) := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

private theorem qCoeff_add {N : ℕ} (g₁ g₂ : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(g₁ + g₂)) n
      = ModularFormClass.qCoeff g₁ n + ModularFormClass.qCoeff g₂ n := by
  simp only [ModularFormClass.qCoeff]
  rw [CuspForm.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods N) g₁ g₂,
    map_add]

private theorem qCoeff_zsmul {N : ℕ} (c : ℤ) (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (n : ℕ) :
    ModularFormClass.qCoeff (⇑(c • g)) n = (c : ℂ) * ModularFormClass.qCoeff g n := by
  have h : (c • g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) = (c : ℂ) • g :=
    (Int.cast_smul_eq_zsmul ℂ c g).symm
  rw [h]
  simp only [ModularFormClass.qCoeff]
  rw [CuspForm.IsGLPos.coe_smul,
    ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods N) (c : ℂ) g, map_smul,
    smul_eq_mul]

private theorem qCoeff_zero {N : ℕ} (n : ℕ) :
    ModularFormClass.qCoeff (0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) n = 0 := by
  simp only [ModularFormClass.qCoeff]
  rw [CuspForm.coe_zero, UpperHalfPlane.qExpansion_zero]
  simp

private theorem qCoeff_heckeTLin_eq {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeTLin 2 hℓ hℓN g) n
      = ModularFormClass.qCoeff g (n * ℓ)
        + if ℓ ∣ n then (ℓ : ℂ) * ModularFormClass.qCoeff g (n / ℓ) else 0 := by
  rw [CuspForm.coe_heckeTLin_apply]
  rw [ModularFormClass.qCoeff_heckeT g (one_mem_strictPeriods N) hℓ.ne_zero n]
  rw [ModularForm.coeffHeckeT_apply]
  simp only [show (2 : ℤ) - 1 = 1 by norm_num, zpow_one]

private theorem qCoeff_heckeULin_eq {N : ℕ} [NeZero N] {q : ℕ} (hq0 : q ≠ 0) (hqN : q ∣ N)
    (g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULin 2 hqN g) n
      = ModularFormClass.qCoeff g (n * q) := by
  rw [CuspForm.coe_heckeULin_apply]
  rw [ModularFormClass.qCoeff_heckeU g (one_mem_strictPeriods N) hq0 n]
  rfl

private theorem coeff_dvd_of_mem_heckeAlgebra {N : ℕ} [NeZero N] (m : ℕ)
    {t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)}
    (ht : t ∈ CuspForm.heckeAlgebra N 2 ∅) :
    ∀ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2,
      (∀ k : ℕ, k ≠ 0 → ∃ z : ℤ, (z : ℂ) = ModularFormClass.qCoeff g k ∧ (m : ℤ) ∣ z) →
      ∀ k : ℕ, k ≠ 0 → ∃ z : ℤ, (z : ℂ) = ModularFormClass.qCoeff (t g) k ∧ (m : ℤ) ∣ z := by
  change t ∈ Algebra.adjoin ℤ (CuspForm.heckeGenerators N 2 ∅) at ht
  induction ht using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with ⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩
    ·
      intro g hg k hk
      rw [qCoeff_heckeTLin_eq hℓ hℓN g k]
      by_cases hd : ℓ ∣ k
      · obtain ⟨z₁, hz₁, hv₁⟩ := hg (k * ℓ) (mul_ne_zero hk hℓ.ne_zero)
        obtain ⟨z₂, hz₂, hv₂⟩ := hg (k / ℓ) ((Nat.div_ne_zero_iff_of_dvd hd).mpr ⟨hk, hℓ.ne_zero⟩)
        refine ⟨z₁ + ℓ * z₂, ?_, dvd_add hv₁ (hv₂.mul_left ℓ)⟩
        rw [if_pos hd]
        push_cast
        rw [hz₁, hz₂]
      · obtain ⟨z₁, hz₁, hv₁⟩ := hg (k * ℓ) (mul_ne_zero hk hℓ.ne_zero)
        exact ⟨z₁, by rw [if_neg hd, add_zero]; exact hz₁, hv₁⟩
    ·
      intro g hg k hk
      rw [qCoeff_heckeULin_eq hq.ne_zero hqN g k]
      exact hg (k * q) (mul_ne_zero hk hq.ne_zero)
  | algebraMap r =>
    intro g hg k hk
    have happ : (algebraMap ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) r) g
        = r • g := by
      simp only [algebraMap_int_eq, Int.coe_castRingHom, Module.End.intCast_apply]
    rw [happ]
    obtain ⟨z, hz, hv⟩ := hg k hk
    refine ⟨r * z, ?_, hv.mul_left r⟩
    rw [qCoeff_zsmul]
    push_cast
    rw [hz]
  | add x y hx hy ihx ihy =>
    intro g hg k hk
    obtain ⟨z₁, hz₁, hv₁⟩ := ihx g hg k hk
    obtain ⟨z₂, hz₂, hv₂⟩ := ihy g hg k hk
    refine ⟨z₁ + z₂, ?_, dvd_add hv₁ hv₂⟩
    rw [LinearMap.add_apply, qCoeff_add]
    push_cast
    rw [hz₁, hz₂]
  | mul x y hx hy ihx ihy =>
    intro g hg k hk
    rw [Module.End.mul_apply]
    exact ihx (y g) (ihy g hg) k hk

end Forms

section Main

variable (p m : ℕ) [Fact p.Prime] (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2)

private def divIdeal : Ideal (CuspForm.heckeAlgebra p 2 ∅) where
  carrier := {x | ∀ n : ℕ, n ≠ 0 → ∃ z : ℤ,
    (z : ℂ) = ModularFormClass.qCoeff
      ((x : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f) n ∧ (m : ℤ) ∣ z}
  add_mem' := by
    intro a b ha hb n hn
    obtain ⟨z₁, hz₁, hv₁⟩ := ha n hn
    obtain ⟨z₂, hz₂, hv₂⟩ := hb n hn
    refine ⟨z₁ + z₂, ?_, dvd_add hv₁ hv₂⟩
    rw [Subalgebra.coe_add, LinearMap.add_apply, qCoeff_add]
    push_cast
    rw [hz₁, hz₂]
  zero_mem' := by
    intro n hn
    refine ⟨0, ?_, dvd_zero _⟩
    rw [Subalgebra.coe_zero, LinearMap.zero_apply, qCoeff_zero]
    exact Int.cast_zero
  smul_mem' := by
    intro c x hx n hn
    rw [smul_eq_mul, Subalgebra.coe_mul, Module.End.mul_apply]
    exact coeff_dvd_of_mem_heckeAlgebra m c.2 _ hx n hn

private theorem mem_divIdeal {x : CuspForm.heckeAlgebra p 2 ∅} :
    x ∈ divIdeal p m f ↔ ∀ n : ℕ, n ≠ 0 → ∃ z : ℤ,
      (z : ℂ) = ModularFormClass.qCoeff
        ((x : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f) n ∧ (m : ℤ) ∣ z :=
  Iff.rfl

private theorem heckeProj_master (af : ℕ → ℤ)
    (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n)
    (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1)
    (x : HeckeAlg) :
    ∀ n : ℕ, n ≠ 0 → ∃ z : ℤ,
      (z : ℂ) = ModularFormClass.qCoeff
        ((heckeProj p x : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f) n ∧
      (m : ℤ) ∣ z - MvPolynomial.aeval (eisensteinSystem p) x * (sigmaPrimeTo p n : ℤ) * af 1 := by
  induction x using MvPolynomial.induction_on with
  | C c =>
    intro n hn
    refine ⟨c * af n, ?_, ?_⟩
    · have h₁ : ((heckeProj p (MvPolynomial.C c) : CuspForm.heckeAlgebra p 2 ∅) :
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f = c • f := by
        rw [heckeProj_C]
        rw [show ((algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c :
              CuspForm.heckeAlgebra p 2 ∅) :
            Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2))
          = algebraMap ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) c from rfl]
        simp only [algebraMap_int_eq, Int.coe_castRingHom, Module.End.intCast_apply]
      rw [h₁, qCoeff_zsmul]
      push_cast
      rw [haf n]
    · simp only [MvPolynomial.aeval_C]
      simp only [eq_intCast, Int.cast_id]
      obtain ⟨w, hw⟩ := hcongr n hn
      exact ⟨c * w, by linear_combination c * hw⟩
  | add q r ihq ihr =>
    intro n hn
    obtain ⟨z₁, hz₁, hv₁⟩ := ihq n hn
    obtain ⟨z₂, hz₂, hv₂⟩ := ihr n hn
    refine ⟨z₁ + z₂, ?_, ?_⟩
    · rw [map_add (heckeProj p), Subalgebra.coe_add, LinearMap.add_apply, qCoeff_add]
      push_cast
      rw [hz₁, hz₂]
    · rw [map_add (MvPolynomial.aeval (eisensteinSystem p))]
      obtain ⟨w₁, hw₁⟩ := hv₁
      obtain ⟨w₂, hw₂⟩ := hv₂
      exact ⟨w₁ + w₂, by linear_combination hw₁ + hw₂⟩
  | mul_X x ℓ ih =>
    intro n hn
    rw [map_mul (heckeProj p) x (MvPolynomial.X ℓ),
      mul_comm (heckeProj p x) (heckeProj p (MvPolynomial.X ℓ)), Subalgebra.coe_mul,
      Module.End.mul_apply, map_mul (MvPolynomial.aeval (eisensteinSystem p)) x
        (MvPolynomial.X ℓ),
      show (MvPolynomial.X ℓ : HeckeAlg) = heckeGen ℓ from rfl, aeval_heckeGen]
    by_cases hdvd : (ℓ : ℕ) ∣ p
    ·
      have hℓp : (ℓ : ℕ) = p := (Nat.prime_dvd_prime_iff_eq ℓ.2 (Fact.out : p.Prime)).mp hdvd
      rw [heckeProj_heckeGen_of_dvd ℓ hdvd, CuspForm.heckeAlgebra.coe_U,
        eisensteinSystem_of_dvd hdvd, qCoeff_heckeULin_eq ℓ.2.ne_zero hdvd]
      obtain ⟨z₁, hz₁, hv₁⟩ := ih (n * ℓ) (mul_ne_zero hn ℓ.2.ne_zero)
      refine ⟨z₁, hz₁, ?_⟩
      obtain ⟨w₁, hw₁⟩ := hv₁
      have hσ : (sigmaPrimeTo p (n * (ℓ : ℕ)) : ℤ) = (sigmaPrimeTo p n : ℤ) := by
        rw [hℓp]
        exact_mod_cast sigmaPrimeTo_mul_self (Fact.out : p.Prime) hn
      exact ⟨w₁, by linear_combination hw₁
        + (MvPolynomial.aeval (eisensteinSystem p) x * af 1) * hσ⟩
    ·
      have hℓp : (ℓ : ℕ) ≠ p := fun h => hdvd (h ▸ dvd_refl p)
      rw [heckeProj_heckeGen_of_not_dvd ℓ hdvd, CuspForm.heckeAlgebra.coe_T,
        eisensteinSystem_of_not_dvd hdvd, qCoeff_heckeTLin_eq ℓ.2 hdvd]
      by_cases hd : (ℓ : ℕ) ∣ n
      · rw [if_pos hd]
        obtain ⟨z₁, hz₁, hv₁⟩ := ih (n * ℓ) (mul_ne_zero hn ℓ.2.ne_zero)
        obtain ⟨z₂, hz₂, hv₂⟩ := ih (n / ℓ) ((Nat.div_ne_zero_iff_of_dvd hd).mpr
          ⟨hn, ℓ.2.ne_zero⟩)
        refine ⟨z₁ + (ℓ : ℕ) * z₂, ?_, ?_⟩
        · push_cast
          rw [hz₁, hz₂]
        · obtain ⟨w₁, hw₁⟩ := hv₁
          obtain ⟨w₂, hw₂⟩ := hv₂
          have hσ : (sigmaPrimeTo p (n * (ℓ : ℕ)) : ℤ)
                + (ℓ : ℕ) * (sigmaPrimeTo p (n / (ℓ : ℕ)) : ℤ)
              = (1 + (ℓ : ℕ)) * (sigmaPrimeTo p n : ℤ) := by
            have h2 := sigmaPrimeTo_mul_prime (Fact.out : p.Prime) ℓ.2 hℓp hn
            rw [if_pos hd] at h2
            exact_mod_cast h2
          exact ⟨w₁ + (ℓ : ℕ) * w₂, by linear_combination hw₁ + ((ℓ : ℕ) : ℤ) * hw₂
            + (MvPolynomial.aeval (eisensteinSystem p) x * af 1) * hσ⟩
      · rw [if_neg hd, add_zero]
        obtain ⟨z₁, hz₁, hv₁⟩ := ih (n * ℓ) (mul_ne_zero hn ℓ.2.ne_zero)
        refine ⟨z₁, hz₁, ?_⟩
        obtain ⟨w₁, hw₁⟩ := hv₁
        have hσ : (sigmaPrimeTo p (n * (ℓ : ℕ)) : ℤ) = (1 + (ℓ : ℕ)) * (sigmaPrimeTo p n : ℤ) := by
          have h2 := sigmaPrimeTo_mul_prime (Fact.out : p.Prime) ℓ.2 hℓp hn
          rw [if_neg hd, add_zero] at h2
          exact_mod_cast h2
        exact ⟨w₁, by linear_combination hw₁
          + (MvPolynomial.aeval (eisensteinSystem p) x * af 1) * hσ⟩

end Main

end S09RC

namespace CuspForm p2m_export "CuspForm" "IsGLPos.coe_smul coe_zero zero_apply ext coe_smul add_apply coe_add heckeGenerators heckeAlgebra heckeAlgebra.coe_T heckeAlgebra.coe_U heckeTLin heckeULin coe_heckeTLin_apply coe_heckeULin_apply qIntegralSet" end CuspForm
p2m_open_scoped "CuspForm" in

private theorem CuspForm.eisenstein_injective_of_qCoeff_congr_sigmaPrimeTo (p m : ℕ) [Fact p.Prime]
    (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2)
    (hf : f ∈ CuspForm.qIntegralSet p) (af : ℕ → ℤ)
    (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n)
    (h1 : IsCoprime (af 1) (m : ℤ))
    (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1) :
    ∀ c : ℤ, algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c ∈
      Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔
        Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)} → (m : ℤ) ∣ c := by
  have _hm := hm
  have _hf := hf

  have hm_mem : ((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅) ∈ S09RC.divIdeal p m f := by
    rw [S09RC.mem_divIdeal]
    intro n hn
    refine ⟨m * af n, ?_, dvd_mul_right (m : ℤ) (af n)⟩
    have h₁ : (((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅) :
        Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f = (m : ℕ) • f := by
      rw [show (((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅) :
            Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2))
          = ((m : ℕ) : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) from rfl,
        Module.End.natCast_apply]
    rw [h₁, ← natCast_zsmul, S09RC.qCoeff_zsmul]
    push_cast
    rw [haf n]

  have hsub : Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔
      Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)} ≤ S09RC.divIdeal p m f := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hx0 : MvPolynomial.aeval (eisensteinSystem p) x = 0 := by
        have hx' : x ∈ eigenIdeal (eisensteinSystem p) := hx
        exact (mem_eigenIdeal_iff (eisensteinSystem p) x).mp hx'
      rw [Ideal.mem_comap, S09RC.mem_divIdeal]
      intro n hn
      obtain ⟨z, hz, hv⟩ := S09RC.heckeProj_master p m f af haf hcongr x n hn
      refine ⟨z, hz, ?_⟩
      rwa [hx0, zero_mul, zero_mul, sub_zero] at hv
    · rw [Ideal.span_le]
      simp only [Set.singleton_subset_iff, SetLike.mem_coe]
      exact hm_mem
  intro c hc
  have hmem := hsub hc
  rw [S09RC.mem_divIdeal] at hmem
  obtain ⟨z, hz, hv⟩ := hmem 1 one_ne_zero
  have h₁ : ((algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c : CuspForm.heckeAlgebra p 2 ∅) :
      Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) f = c • f := by
    rw [show ((algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c : CuspForm.heckeAlgebra p 2 ∅) :
          Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2))
        = algebraMap ℤ (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 p) 2)) c from rfl]
    simp only [algebraMap_int_eq, Int.coe_castRingHom, Module.End.intCast_apply]
  rw [h₁, S09RC.qCoeff_zsmul, ← haf 1] at hz
  have hz' : z = c * af 1 := by exact_mod_cast hz
  rw [hz'] at hv
  exact h1.symm.dvd_of_dvd_mul_right hv

end

open ModularCurve in
theorem solution : ∀ (p m : ℕ) [Fact p.Prime] (hm : 2 ≤ m) (f : CuspForm (CongruenceSubgroup.Gamma0 p) 2) (hf : f ∈ CuspForm.qIntegralSet p) (af : ℕ → ℤ) (haf : ∀ n : ℕ, (af n : ℂ) = ModularFormClass.qCoeff f n) (h1 : IsCoprime (af 1) (m : ℤ)) (hcongr : ∀ n : ℕ, n ≠ 0 → (m : ℤ) ∣ af n - (sigmaPrimeTo p n : ℤ) * af 1), ∀ c : ℤ, algebraMap ℤ (CuspForm.heckeAlgebra p 2 ∅) c ∈ Ideal.map (heckeProj p) (eisensteinIdeal p) ⊔ Ideal.span {((m : ℕ) : CuspForm.heckeAlgebra p 2 ∅)} → (m : ℤ) ∣ c :=
  @CuspForm.eisenstein_injective_of_qCoeff_congr_sigmaPrimeTo

end S_CuspForm_eisenstein_injective_of_qCoeff_congr_sigmaPrimeTo
end P2MW
export P2MW.S_CuspForm_eisenstein_injective_of_qCoeff_congr_sigmaPrimeTo (solution)
