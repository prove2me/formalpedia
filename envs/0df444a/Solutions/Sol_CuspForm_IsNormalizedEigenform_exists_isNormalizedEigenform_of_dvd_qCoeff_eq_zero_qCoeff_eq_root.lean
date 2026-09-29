-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/09305ffb-1cec-52b4-ae27-3344c0f62ece

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite
import Mathlib.Data.Nat.Factorization.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

namespace K1C3Oldform

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

theorem isNormalizedEigenform_stab {M' q : ℕ} [NeZero M'] [NeZero (M' * q)]
    {g' : CuspForm (CongruenceSubgroup.Gamma0 M') 2} (hg' : g'.IsNormalizedEigenform)
    (hq : q.Prime) (hqM' : ¬ q ∣ M') (α : ℂ)
    (hα : α ^ 2 - ModularFormClass.qCoeff g' q * α + q = 0)
    (g : CuspForm (CongruenceSubgroup.Gamma0 (M' * q)) 2)
    (hb : ∀ n : ℕ, ModularFormClass.qCoeff g n = ModularFormClass.qCoeff g' n -
      (ModularFormClass.qCoeff g' q - α) *
        (if q ∣ n then ModularFormClass.qCoeff g' (n / q) else 0)) :
    g.IsNormalizedEigenform ∧ ModularFormClass.qCoeff g q = α := by
  set a : ℕ → ℂ := fun n => ModularFormClass.qCoeff g' n with ha
  set β : ℂ := ModularFormClass.qCoeff g' q - α with hβ
  have hprod : α * β = q := by rw [hβ]; linear_combination (-1 : ℂ) * hα
  have ha1 : a 1 = 1 := hg'.qCoeff_one
  have hbq : ModularFormClass.qCoeff g q = α := by
    rw [hb, if_pos (dvd_refl q), Nat.div_self hq.pos]
    change a q - (a q - α) * a 1 = α
    rw [ha1, mul_one, sub_sub_cancel]
  have hpow_div : ∀ j : ℕ, q ^ (j + 1) / q = q ^ j := fun j => by
    rw [pow_succ, Nat.mul_div_cancel _ hq.pos]
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hbq⟩
  · rw [hb, if_neg hq.not_dvd_one, mul_zero, sub_zero, hg'.qCoeff_one]
  · intro m n hmn
    rw [hb, hb m, hb n]
    by_cases hm : q ∣ m
    · have hn : ¬ q ∣ n := fun hn =>
        hq.not_dvd_one (hmn ▸ Nat.dvd_gcd hm hn)
      have hdiv : m * n / q = m / q * n := (Nat.div_mul_right_comm hm n).symm
      have hcop : (m / q).Coprime n := hmn.coprime_dvd_left (Nat.div_dvd_of_dvd hm)
      rw [if_pos (dvd_mul_of_dvd_left hm n), if_pos hm, if_neg hn, hdiv,
        hg'.qCoeff_mul_of_coprime m n hmn, hg'.qCoeff_mul_of_coprime (m / q) n hcop]
      ring
    by_cases hn : q ∣ n
    · have hdiv : m * n / q = m * (n / q) := Nat.mul_div_assoc m hn
      have hcop : m.Coprime (n / q) := hmn.coprime_dvd_right (Nat.div_dvd_of_dvd hn)
      rw [if_pos (dvd_mul_of_dvd_right hn m), if_neg hm, if_pos hn, hdiv,
        hg'.qCoeff_mul_of_coprime m n hmn, hg'.qCoeff_mul_of_coprime m (n / q) hcop]
      ring
    rw [if_neg (fun h => (hq.dvd_mul.mp h).elim hm hn), if_neg hm, if_neg hn,
      hg'.qCoeff_mul_of_coprime m n hmn]
    ring
  · intro p r hp hpL
    have hpq : p ≠ q := fun h => hpL (h ▸ dvd_mul_left q M')
    have hpM' : ¬ p ∣ M' := fun h => hpL (dvd_mul_of_dvd_left h q)
    have hnd : ∀ i : ℕ, ¬ q ∣ p ^ i := fun i h =>
      hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)).symm
    rw [hb, hb, hb, hb, if_neg (hnd _), if_neg (hnd _), if_neg (hnd _),
      if_neg (by simpa using hnd 1)]
    simp only [mul_zero, sub_zero]
    exact hg'.qCoeff_prime_pow_of_not_dvd p r hp hpM'
  · intro p r hp hpL
    by_cases hpq : p = q
    · subst hpq
      rw [hbq, hb, hb, if_pos (dvd_pow_self p (Nat.succ_ne_zero _)),
        if_pos (dvd_pow_self p (Nat.succ_ne_zero _)), hpow_div, hpow_div]
      have hrec := hg'.qCoeff_prime_pow_of_not_dvd p r hp hqM'
      change a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - p * a (p ^ r) at hrec
      change a (p ^ (r + 2)) - (a p - α) * a (p ^ (r + 1)) =
        α * (a (p ^ (r + 1)) - (a p - α) * a (p ^ r))
      have hprod' : α * (a p - α) = p := hprod
      linear_combination hrec + a (p ^ r) * hprod'
    · have hpM' : p ∣ M' := by
        rcases hp.dvd_mul.mp hpL with h | h
        · exact h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp h) hpq
      have hnd : ∀ i : ℕ, ¬ q ∣ p ^ i := fun i h =>
        hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)).symm
      rw [hb, hb, hb, if_neg (hnd _), if_neg (hnd _), if_neg (by simpa using hnd 1)]
      simp only [mul_zero, sub_zero]
      exact hg'.qCoeff_prime_pow_of_dvd p r hp hpM'

theorem step_stab {M' L q : ℕ} [NeZero M'] [NeZero L]
    {g' : CuspForm (CongruenceSubgroup.Gamma0 M') 2} (hg' : g'.IsNormalizedEigenform)
    (hq : q.Prime) (hqM' : ¬ q ∣ M') (hL : M' * q = L) (α : ℂ)
    (hα : α ^ 2 - ModularFormClass.qCoeff g' q * α + q = 0) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 L) 2, g.IsNormalizedEigenform ∧
      (∀ r : ℕ, r.Prime → r ≠ q → ModularFormClass.qCoeff g r = ModularFormClass.qCoeff g' r) ∧
      ModularFormClass.qCoeff g q = α := by
  subst hL
  have h1 : 1 * M' ∣ M' * q := ⟨q, by ring⟩
  have hq1 : q * M' ∣ M' * q := ⟨1, by ring⟩
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne_zero
  set β : ℂ := ModularFormClass.qCoeff g' q - α with hβ
  set g : CuspForm (CongruenceSubgroup.Gamma0 (M' * q)) 2 :=
    FreyPackage.ModMCarrier.rescaleLin h1 2 g' -
      (β / q) • FreyPackage.ModMCarrier.rescaleLin hq1 2 g' with hgdef
  have hb : ∀ n : ℕ, ModularFormClass.qCoeff g n = ModularFormClass.qCoeff g' n -
      (ModularFormClass.qCoeff g' q - α) *
        (if q ∣ n then ModularFormClass.qCoeff g' (n / q) else 0) := by
    intro n
    rw [hgdef, qCoeff_sub_smul, qCoeff_rescaleLin_one, qCoeff_rescaleLin hq1 hq.ne_zero]
    split_ifs
    · rw [← hβ]; field_simp
    · simp
  obtain ⟨hg, hgq⟩ := isNormalizedEigenform_stab hg' hq hqM' α hα g hb
  refine ⟨g, hg, fun r hr hrq => ?_, hgq⟩
  rw [hb, if_neg (fun h => hrq ((Nat.prime_dvd_prime_iff_eq hq hr).mp h).symm), mul_zero, sub_zero]

theorem step_depl {M' L q : ℕ} [NeZero M'] [NeZero L]
    {g' : CuspForm (CongruenceSubgroup.Gamma0 M') 2} (hg' : g'.IsNormalizedEigenform)
    (hq : q.Prime) (e : ℕ) (he : 1 ≤ e) (he2 : ¬ q ∣ M' → 2 ≤ e) (hL : M' * q ^ e = L) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 L) 2, g.IsNormalizedEigenform ∧
      (∀ r : ℕ, r.Prime → r ≠ q → ModularFormClass.qCoeff g r = ModularFormClass.qCoeff g' r) ∧
      ModularFormClass.qCoeff g q = 0 := by
  subst hL
  obtain ⟨g, hg, hcoeff⟩ :=
    hg'.exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite hq e he he2
  refine ⟨g, hg, fun r hr hrq => ?_, ?_⟩
  · rw [hcoeff, if_neg (fun h => hrq ((Nat.prime_dvd_prime_iff_eq hq hr).mp h).symm)]
  · rw [hcoeff, if_pos (dvd_refl q)]

def Concl (M N : ℕ) [NeZero M] [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (α : ℕ → ℂ) : Prop :=
  ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g.IsNormalizedEigenform ∧
    (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff f ℓ) ∧
    (∀ q : ℕ, q.Prime → q ∣ N → N.factorization q = M.factorization q →
      ModularFormClass.qCoeff g q = ModularFormClass.qCoeff f q) ∧
    (∀ q : ℕ, q.Prime → q ∣ N → ¬ q ∣ M → ¬ q ^ 2 ∣ N →
      ModularFormClass.qCoeff g q = α q) ∧
    (∀ q : ℕ, q.Prime → q ^ 2 ∣ N → M.factorization q < N.factorization q →
      ModularFormClass.qCoeff g q = 0)

theorem main (N : ℕ) : ∀ (M : ℕ) [NeZero M] [NeZero N] (_hMN : M ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (_hf : f.IsNormalizedEigenform)
    (α : ℕ → ℂ)
    (_hα : ∀ q : ℕ, q.Prime → q ∣ N → ¬ q ∣ M → ¬ q ^ 2 ∣ N →
      α q ^ 2 - ModularFormClass.qCoeff f q * α q + q = 0),
    Concl M N f α := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro M _ _ hMN f hf α hα
  have hN0 : N ≠ 0 := NeZero.ne N
  have hM0 : M ≠ 0 := NeZero.ne M
  by_cases hex : ∃ q : ℕ, q.Prime ∧ M.factorization q < N.factorization q
  swap
  ·
    have hle : N.factorization ≤ M.factorization := by
      intro q
      by_cases hq : q.Prime
      · exact not_lt.mp fun h => hex ⟨q, hq, h⟩
      · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
    have hNM : N ∣ M := (Nat.factorization_le_iff_dvd hN0 hM0).mp hle
    obtain rfl : M = N := Nat.dvd_antisymm hMN hNM
    exact ⟨f, hf, fun _ _ _ => rfl, fun _ _ _ _ => rfl,
      fun q _ hqN hqM _ => absurd hqN hqM, fun q _ _ hlt => absurd hlt (lt_irrefl _)⟩
  obtain ⟨q, hq, hlt⟩ := hex

  set e : ℕ := N.factorization q - M.factorization q with he
  have he1 : 1 ≤ e := by omega
  have heN : e ≤ N.factorization q := by omega
  have hqeN : q ^ e ∣ N := (hq.pow_dvd_iff_le_factorization hN0).mpr heN
  set N' : ℕ := N / q ^ e with hN'
  have hN'e : N' * q ^ e = N := Nat.div_mul_cancel hqeN
  have hqe0 : q ^ e ≠ 0 := pow_ne_zero _ hq.ne_zero
  have hN'0 : N' ≠ 0 := by
    intro h; apply hN0; rw [← hN'e, h, zero_mul]
  haveI : NeZero N' := ⟨hN'0⟩
  have hN'N : N' ∣ N := ⟨q ^ e, hN'e.symm⟩

  have hfac' : N'.factorization = N.factorization - e • q.factorization := by
    rw [hN', Nat.factorization_div hqeN, Nat.factorization_pow]
  have hfacq : N'.factorization q = M.factorization q := by
    rw [hfac', Finsupp.tsub_apply, Finsupp.smul_apply, hq.factorization_self, smul_eq_mul, mul_one]
    omega
  have hfacr : ∀ r : ℕ, r ≠ q → N'.factorization r = N.factorization r := by
    intro r hrq
    rw [hfac', Finsupp.tsub_apply, Finsupp.smul_apply, hq.factorization, Finsupp.single_apply,
      if_neg hrq.symm, smul_zero, tsub_zero]
  have hMN' : M ∣ N' := by
    rw [← Nat.factorization_le_iff_dvd hM0 hN'0]
    intro r
    by_cases hrq : r = q
    · rw [hrq, hfacq]
    · rw [hfacr r hrq]; exact (Nat.factorization_le_iff_dvd hM0 hN0).mpr hMN r
  have hlt' : N' < N := by
    have h2 : 2 ≤ q ^ e := by
      calc 2 ≤ q := hq.two_le
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ e := Nat.pow_le_pow_right hq.pos he1
    have : N' * 2 ≤ N' * q ^ e := Nat.mul_le_mul_left _ h2
    omega

  have hdvd_iff : ∀ r : ℕ, r.Prime → r ≠ q → ∀ k : ℕ, (r ^ k ∣ N' ↔ r ^ k ∣ N) := by
    intro r hr hrq k
    rw [hr.pow_dvd_iff_le_factorization hN'0, hr.pow_dvd_iff_le_factorization hN0, hfacr r hrq]
  have hdvd1_iff : ∀ r : ℕ, r.Prime → r ≠ q → (r ∣ N' ↔ r ∣ N) := by
    intro r hr hrq; simpa using hdvd_iff r hr hrq 1
  have hqN'_iff : q ∣ N' ↔ q ∣ M := by
    rw [hq.dvd_iff_one_le_factorization hN'0, hq.dvd_iff_one_le_factorization hM0, hfacq]

  have hα' : ∀ r : ℕ, r.Prime → r ∣ N' → ¬ r ∣ M → ¬ r ^ 2 ∣ N' →
      α r ^ 2 - ModularFormClass.qCoeff f r * α r + r = 0 := by
    intro r hr hrN' hrM hr2
    have hrq : r ≠ q := by
      rintro rfl; exact hrM (hqN'_iff.mp hrN')
    exact hα r hr (hrN'.trans hN'N) hrM (fun h => hr2 ((hdvd_iff r hr hrq 2).mpr h))
  obtain ⟨g', hg', C1', C2', C3', C4'⟩ := ih N' hlt' M hMN' f hf α hα'
  have hqN : q ∣ N := (hq.dvd_iff_one_le_factorization hN0).mpr (by omega)
  by_cases hA : M.factorization q = 0 ∧ N.factorization q = 1
  ·
    have he_one : e = 1 := by omega
    have hqM : ¬ q ∣ M := by
      rw [hq.dvd_iff_one_le_factorization hM0]; omega
    have hqN' : ¬ q ∣ N' := fun h => hqM (hqN'_iff.mp h)
    have hq2N : ¬ q ^ 2 ∣ N := by
      rw [hq.pow_dvd_iff_le_factorization hN0]; omega
    have hL : N' * q = N := by rw [← hN'e, he_one, pow_one]
    have hαq : α q ^ 2 - ModularFormClass.qCoeff g' q * α q + q = 0 := by
      rw [C1' q hq hqN']; exact hα q hq hqN hqM hq2N
    obtain ⟨g, hg, hsame, hgq⟩ := step_stab hg' hq hqN' hL (α q) hαq
    refine ⟨g, hg, ?_, ?_, ?_, ?_⟩
    · intro ℓ hℓ hℓN
      have hℓq : ℓ ≠ q := by rintro rfl; exact hℓN hqN
      rw [hsame ℓ hℓ hℓq]
      exact C1' ℓ hℓ (fun h => hℓN (h.trans hN'N))
    · intro r hr hrN hfr
      have hrq : r ≠ q := by rintro rfl; omega
      rw [hsame r hr hrq]
      exact C2' r hr ((hdvd1_iff r hr hrq).mpr hrN) ((hfacr r hrq).trans hfr)
    · intro r hr hrN hrM hr2
      by_cases hrq : r = q
      · subst hrq; exact hgq
      · rw [hsame r hr hrq]
        exact C3' r hr ((hdvd1_iff r hr hrq).mpr hrN) hrM
          (fun h => hr2 ((hdvd_iff r hr hrq 2).mp h))
    · intro r hr hr2 hfr
      have hrq : r ≠ q := by
        rintro rfl
        rw [hr.pow_dvd_iff_le_factorization hN0] at hr2
        omega
      rw [hsame r hr hrq]
      exact C4' r hr ((hdvd_iff r hr hrq 2).mpr hr2) ((hfacr r hrq).symm ▸ hfr)
  ·
    have he2 : ¬ q ∣ N' → 2 ≤ e := by
      intro hqN'
      have hM0q : M.factorization q = 0 := by
        have := mt hqN'_iff.mpr hqN'
        rw [hq.dvd_iff_one_le_factorization hM0] at this
        omega
      by_contra h
      exact hA ⟨hM0q, by omega⟩
    obtain ⟨g, hg, hsame, hgq⟩ := step_depl hg' hq e he1 he2 hN'e
    refine ⟨g, hg, ?_, ?_, ?_, ?_⟩
    · intro ℓ hℓ hℓN
      have hℓq : ℓ ≠ q := by rintro rfl; exact hℓN hqN
      rw [hsame ℓ hℓ hℓq]
      exact C1' ℓ hℓ (fun h => hℓN (h.trans hN'N))
    · intro r hr hrN hfr
      have hrq : r ≠ q := by rintro rfl; omega
      rw [hsame r hr hrq]
      exact C2' r hr ((hdvd1_iff r hr hrq).mpr hrN) ((hfacr r hrq).trans hfr)
    · intro r hr hrN hrM hr2
      have hrq : r ≠ q := by
        rintro rfl
        apply hA
        rw [hr.dvd_iff_one_le_factorization hM0] at hrM
        rw [hr.pow_dvd_iff_le_factorization hN0] at hr2
        rw [hr.dvd_iff_one_le_factorization hN0] at hrN
        constructor <;> omega
      rw [hsame r hr hrq]
      exact C3' r hr ((hdvd1_iff r hr hrq).mpr hrN) hrM
        (fun h => hr2 ((hdvd_iff r hr hrq 2).mp h))
    · intro r hr hr2 hfr
      by_cases hrq : r = q
      · subst hrq; exact hgq
      · rw [hsame r hr hrq]
        exact C4' r hr ((hdvd_iff r hr hrq 2).mpr hr2) ((hfacr r hrq).symm ▸ hfr)

end K1C3Oldform

theorem solution
    {M N : ℕ} [NeZero M] [NeZero N] (hMN : M ∣ N)
    {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f.IsNormalizedEigenform)
    (α : ℕ → ℂ)
    (hα : ∀ q : ℕ, q.Prime → q ∣ N → ¬ q ∣ M → ¬ q ^ 2 ∣ N →
      α q ^ 2 - ModularFormClass.qCoeff f q * α q + q = 0) :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 N) 2, g.IsNormalizedEigenform ∧
      (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ModularFormClass.qCoeff g ℓ = ModularFormClass.qCoeff f ℓ) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → N.factorization q = M.factorization q →
        ModularFormClass.qCoeff g q = ModularFormClass.qCoeff f q) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → ¬ q ∣ M → ¬ q ^ 2 ∣ N →
        ModularFormClass.qCoeff g q = α q) ∧
      (∀ q : ℕ, q.Prime → q ^ 2 ∣ N → M.factorization q < N.factorization q →
        ModularFormClass.qCoeff g q = 0) :=
  K1C3Oldform.main N M hMN f hf α hα

end

end S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_of_dvd_qCoeff_eq_zero_qCoeff_eq_root (solution)
