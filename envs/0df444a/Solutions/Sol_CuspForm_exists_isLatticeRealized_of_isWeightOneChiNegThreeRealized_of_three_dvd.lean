-- Prove2me | solution 1 for CuspForm.exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c191444d-81a4-5970-8b21-59fe35dc0329

import Mathlib
import Definitions.Def_LanglandsTunnell_WeightOneRealizationCarriers
import Definitions.Def_ModularForm_HeckeOperator
import Theorems.Thm_EisensteinWeightOne_e1Chi3IsModular
import Theorems.Thm_EisensteinWeightOne_chiNegThree_mul
import Theorems.Thm_EisensteinWeightOne_coeff_e1Chi3
import Theorems.Thm_CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd
p2m_attr_erase "instance" "Ihara.instGroupIharaAmalgam"
p2m_attr_erase "simp" "Ihara.wConj_coe Ihara.wConj_symm_coe Ihara.coe_iota1 Ihara.coe_iota1SL Ihara.iota1Mat_apply_one_zero Ihara.iota1Mat_apply_zero_zero Ihara.iota1Mat_apply_zero_one Ihara.iota1Mat_apply_one_one Ihara.coe_iota0 Ihara.iharaEdge_one Ihara.pairFamily_zero Ihara.iharaEdge_zero Ihara.pairFamily_one Ihara.coe_amalgamToGamma0Away Ihara.coe_vertexZero Ihara.coe_slToAway"

set_option autoImplicit false
set_option maxHeartbeats 3200000

open CongruenceSubgroup ModularForm EisensteinWeightOne UpperHalfPlane
p2m_open "FLT.ExplicitLift CuspForm ModularForm.CuspForm Zsqrtd Complex"
open scoped ModularForm UpperHalfPlane MatrixGroups

noncomputable section

namespace WeightTwoCongruenceLiftThree

section FormalHecke

variable {R : Type*} [CommRing R]

def ppow (e c : ℕ → R) (p : ℕ) : ℕ → R
  | 0 => 1
  | 1 => c p
  | k + 2 => c p * ppow e c p (k + 1) - e p * ppow e c p k

def ext (e c : ℕ → R) (n : ℕ) : R :=
  if n = 0 then 0 else n.factorization.prod fun p k => ppow e c p k

variable (e c : ℕ → R)

theorem ext_zero : ext e c 0 = 0 := by simp [ext]

theorem ext_one : ext e c 1 = 1 := by simp [ext, Nat.factorization_one]

theorem ext_pow {p : ℕ} (hp : p.Prime) (k : ℕ) : ext e c (p ^ k) = ppow e c p k := by
  have hne : p ^ k ≠ 0 := pow_ne_zero k hp.pos.ne'
  unfold ext
  rw [if_neg hne, hp.factorization_pow]
  exact Finsupp.prod_single_index (by simp [ppow])

theorem ext_prime {p : ℕ} (hp : p.Prime) : ext e c p = c p := by
  have h := ext_pow e c hp 1
  rw [pow_one] at h
  rw [h]
  simp [ppow]

theorem ext_mul_coprime {m n : ℕ} (h : m.Coprime n) :
    ext e c (m * n) = ext e c m * ext e c n := by
  rcases eq_or_ne m 0 with rfl | hm
  · obtain rfl : n = 1 := by simpa using h
    simp [ext]
  rcases eq_or_ne n 0 with rfl | hn
  · obtain rfl : m = 1 := by simpa using h
    simp [ext]
  · have hd : Disjoint m.factorization.support n.factorization.support := by
      rw [Nat.support_factorization, Nat.support_factorization]
      exact Nat.Coprime.disjoint_primeFactors h
    unfold ext
    rw [if_neg (Nat.mul_ne_zero hm hn), if_neg hm, if_neg hn,
      Nat.factorization_mul hm hn, Finsupp.prod_add_index_of_disjoint hd]

theorem ext_prime_pow_succ_succ {p : ℕ} (hp : p.Prime) (r : ℕ) :
    ext e c (p ^ (r + 2)) = ext e c p * ext e c (p ^ (r + 1)) - e p * ext e c (p ^ r) := by
  rw [ext_prime e c hp, ext_pow e c hp, ext_pow e c hp, ext_pow e c hp]
  simp [ppow]

theorem ext_isEigensystem : FormalHecke.IsEigensystem e (ext e c) := by
  refine ⟨ext_one e c, fun ℓ hℓ n => ?_⟩
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [ext_zero]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 ℓ hℓ.ne_one
  have hcop : ∀ s : ℕ, (ℓ ^ s).Coprime m :=
    fun s => Nat.Coprime.pow_left s ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hm)
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · rw [pow_zero, one_mul, if_neg hm, mul_zero, add_zero,
      ext_mul_coprime e c ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hm), ext_prime e c hℓ]
  · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    have hdvd : ℓ ∣ ℓ ^ (s + 1) * m := Dvd.dvd.mul_right (dvd_pow_self ℓ s.succ_ne_zero) m
    have hdiv : ℓ ^ (s + 1) * m / ℓ = ℓ ^ s * m := by
      rw [pow_succ' ℓ s, mul_assoc, Nat.mul_div_cancel_left _ hℓ.pos]
    have hassoc : ℓ * (ℓ ^ (s + 1) * m) = ℓ ^ (s + 2) * m := by
      rw [← mul_assoc, ← pow_succ']
    rw [if_pos hdvd, hdiv, hassoc, ext_mul_coprime e c (hcop (s + 2)),
      ext_mul_coprime e c (hcop (s + 1)), ext_mul_coprime e c (hcop s),
      ext_prime_pow_succ_succ e c hℓ, ext_prime e c hℓ]
    ring

theorem map_ppow {S : Type*} [CommRing S] (f : R →+* S) (p : ℕ) :
    ∀ k, f (ppow e c p k) = ppow (fun ℓ => f (e ℓ)) (fun ℓ => f (c ℓ)) p k
  | 0 => by simp [ppow]
  | 1 => by simp [ppow]
  | k + 2 => by
    simp only [ppow, map_sub, map_mul, map_ppow f p (k + 1), map_ppow f p k]

theorem map_ext {S : Type*} [CommRing S] (f : R →+* S) (n : ℕ) :
    f (ext e c n) = ext (fun ℓ => f (e ℓ)) (fun ℓ => f (c ℓ)) n := by
  unfold ext
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [if_neg hn, if_neg hn, map_finsuppProd]
    exact Finsupp.prod_congr fun p _ => map_ppow e c f p (n.factorization p)

variable {e c}

theorem isEigensystem_prime_pow {a : ℕ → R} (h : FormalHecke.IsEigensystem e a) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (r : ℕ) : a (ℓ ^ (r + 2)) = a ℓ * a (ℓ ^ (r + 1)) - e ℓ * a (ℓ ^ r) := by
  have key := h.2 ℓ hℓ (ℓ ^ (r + 1))
  have hdiv : ℓ ^ (r + 1) / ℓ = ℓ ^ r := by
    rw [pow_succ' ℓ r, Nat.mul_div_cancel_left _ hℓ.pos]
  rw [if_pos (dvd_pow_self ℓ (Nat.succ_ne_zero r)), hdiv, ← pow_succ'] at key
  linear_combination key

theorem isEigensystem_mul_coprime {a : ℕ → R} (h : FormalHecke.IsEigensystem e a) :
    ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n := by
  obtain ⟨h1, H⟩ := h
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IH =>
    intro n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · rw [Nat.coprime_zero_left] at hmn
      subst hmn
      simp [h1]
    rcases eq_or_ne m 1 with rfl | hm1
    · simp [h1]
    obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hm1
    obtain ⟨m₁, rfl⟩ := hdvd
    have hm₁0 : m₁ ≠ 0 := by rintro rfl; simp at hm0
    have hm₁_lt : m₁ < ℓ * m₁ :=
      (Nat.lt_mul_iff_one_lt_left (Nat.pos_of_ne_zero hm₁0)).mpr hℓ.one_lt
    have hcop_m₁n : m₁.Coprime n := Nat.Coprime.coprime_dvd_left (dvd_mul_left m₁ ℓ) hmn
    have hcop_ℓn : ℓ.Coprime n := Nat.Coprime.coprime_dvd_left (dvd_mul_right ℓ m₁) hmn
    have hℓn : ¬ ℓ ∣ n := (Nat.Prime.coprime_iff_not_dvd hℓ).mp hcop_ℓn
    by_cases hℓm₁ : ℓ ∣ m₁
    · obtain ⟨m₂, rfl⟩ := hℓm₁
      have hm₂0 : m₂ ≠ 0 := by rintro rfl; simp at hm₁0
      have hm₂_lt : m₂ < ℓ * (ℓ * m₂) :=
        lt_of_le_of_lt (Nat.le_mul_of_pos_left m₂ hℓ.pos) hm₁_lt
      have hcop_m₂n : m₂.Coprime n :=
        Nat.Coprime.coprime_dvd_left (dvd_mul_left m₂ ℓ) hcop_m₁n
      have key₁ := H ℓ hℓ (ℓ * m₂ * n)
      have key₂ := H ℓ hℓ (ℓ * m₂)
      rw [if_pos ⟨m₂ * n, by ring⟩, show ℓ * m₂ * n / ℓ = m₂ * n by
            rw [mul_assoc, Nat.mul_div_cancel_left _ hℓ.pos]] at key₁
      rw [if_pos ⟨m₂, rfl⟩, Nat.mul_div_cancel_left _ hℓ.pos] at key₂
      rw [IH _ hm₁_lt n hcop_m₁n, IH _ hm₂_lt n hcop_m₂n] at key₁
      have : ℓ * (ℓ * m₂) * n = ℓ * (ℓ * m₂ * n) := by ring
      rw [this]
      linear_combination key₁ - a n * key₂
    · have hℓm₁n : ¬ ℓ ∣ m₁ * n := fun hd => ((Nat.Prime.dvd_mul hℓ).mp hd).elim hℓm₁ hℓn
      have key₁ := H ℓ hℓ (m₁ * n)
      have key₂ := H ℓ hℓ m₁
      rw [if_neg hℓm₁n, mul_zero, add_zero] at key₁
      rw [if_neg hℓm₁, mul_zero, add_zero] at key₂
      rw [IH _ hm₁_lt n hcop_m₁n] at key₁
      have : ℓ * m₁ * n = ℓ * (m₁ * n) := by ring
      rw [this]
      linear_combination key₁ - a n * key₂

theorem eq_ext_of_isEigensystem {a : ℕ → R} (h : FormalHecke.IsEigensystem e a) (h0 : a 0 = 0)
    (n : ℕ) : a n = ext e a n := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => rw [h0, ext_zero]
  | one => rw [h.1, ext_one]
  | prime_pow p k hp hk =>

    suffices ∀ j, a (p ^ j) = ext e a (p ^ j) from this k
    intro j
    induction j using Nat.strong_induction_on with
    | _ j IH =>
      match j with
      | 0 => rw [pow_zero, h.1, ext_one]
      | 1 => rw [pow_one, ext_prime e a hp]
      | r + 2 =>
        rw [isEigensystem_prime_pow h hp r, ext_prime_pow_succ_succ e a hp r,
          ext_prime e a hp, IH (r + 1) (by omega), IH r (by omega)]
  | coprime m n hm hn hmn ihm ihn =>
    rw [isEigensystem_mul_coprime h m n hmn, ext_mul_coprime e a hmn, ihm, ihn]

theorem isEigensystem_map {S : Type*} [CommRing S] (f : R →+* S) {a : ℕ → R}
    (h : FormalHecke.IsEigensystem e a) :
    FormalHecke.IsEigensystem (fun ℓ => f (e ℓ)) (fun n => f (a n)) := by
  refine ⟨by simp only [h.1, map_one], fun ℓ hℓ n => ?_⟩
  have key := congrArg f (h.2 ℓ hℓ n)
  simp only [map_add, map_mul] at key
  convert key using 2
  split_ifs <;> simp

end FormalHecke

theorem chiNegThree_mod (n : ℕ) : chiNegThree (n % 3) = chiNegThree n := by
  unfold chiNegThree
  rw [Nat.mod_mod]

theorem chiNegThree_eq_of_mod_eq {m n : ℕ} (h : m % 3 = n % 3) : chiNegThree m = chiNegThree n := by
  rw [← chiNegThree_mod m, h, chiNegThree_mod]

theorem chiNegThree_zmod_val (n : ℕ) : chiNegThree ((n : ZMod 3).val) = chiNegThree n := by
  rw [ZMod.val_natCast, chiNegThree_mod]

theorem chiNegThree_one : chiNegThree 1 = 1 := by decide

theorem chiNegThree_sq_of_not_dvd {n : ℕ} (h : ¬ 3 ∣ n) : chiNegThree n * chiNegThree n = 1 := by
  unfold chiNegThree
  have : n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases this with h1 | h2
  · simp [h1]
  · simp [h2]

theorem chiNegThree_of_dvd {n : ℕ} (h : 3 ∣ n) : chiNegThree n = 0 := by
  unfold chiNegThree
  have : n % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  simp [this]

theorem chiNegThree_mem (n : ℕ) : chiNegThree n = 0 ∨ chiNegThree n = 1 ∨ chiNegThree n = -1 := by
  unfold chiNegThree; split_ifs <;> simp

theorem red_apply (x : ℤ√(-2)) : red x = ((x.re - x.im : ℤ) : ZMod 3) := by
  rw [red, Zsqrtd.lift_apply_apply]
  push_cast
  ring

theorem red_intCast (n : ℤ) : red (n : ℤ√(-2)) = (n : ZMod 3) := map_intCast red n

theorem embedding_apply (ι : ℤ√(-2) →+* ℂ) (x : ℤ√(-2)) :
    ι x = (x.re : ℂ) + (x.im : ℂ) * ι sqrtd := by
  conv_lhs => rw [show ι = Zsqrtd.lift (Zsqrtd.lift.symm ι) from (Equiv.apply_symm_apply _ _).symm]
  rw [Zsqrtd.lift_apply_apply]
  rfl

theorem embedding_sqrtd_re (ι : ℤ√(-2) →+* ℂ) : (ι sqrtd).re = 0 := by
  have h : ι sqrtd * ι sqrtd = -2 := by
    rw [← map_mul, Zsqrtd.dmuld]; simp [map_ofNat]
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.mul_re, Complex.mul_im] at hre him
  norm_num at hre him

  by_contra hne
  have him0 : (ι sqrtd).im = 0 := by
    have : 2 * ((ι sqrtd).re * (ι sqrtd).im) = 0 := by linear_combination him
    rcases mul_eq_zero.mp this with h2 | h2
    · norm_num at h2
    · exact (mul_eq_zero.mp h2).resolve_left hne
  rw [him0, mul_zero, sub_zero] at hre
  nlinarith [mul_self_nonneg (ι sqrtd).re]

theorem embedding_sqrtd_im_ne (ι : ℤ√(-2) →+* ℂ) : (ι sqrtd).im ≠ 0 := by
  intro h0
  have h : ι sqrtd * ι sqrtd = -2 := by
    rw [← map_mul, Zsqrtd.dmuld]; simp [map_ofNat]
  have hre := congrArg Complex.re h
  simp only [Complex.mul_re, h0, mul_zero, sub_zero] at hre
  norm_num at hre
  nlinarith [mul_self_nonneg (ι sqrtd).re]

theorem embedding_injective (ι : ℤ√(-2) →+* ℂ) : Function.Injective ι := by
  rw [show ι = Zsqrtd.lift (Zsqrtd.lift.symm ι) from (Equiv.apply_symm_apply _ _).symm]
  refine Zsqrtd.lift_injective _ fun n hn => ?_
  nlinarith [mul_self_nonneg n]

def theta (ι : ℤ√(-2) →+* ℂ) : ℂ →ₗ[ℝ] ℂ :=
  Complex.ofRealCLM.toLinearMap ∘ₗ
    (Complex.reLm - ((ι sqrtd).im)⁻¹ • Complex.imLm)

theorem theta_apply (ι : ℤ√(-2) →+* ℂ) (z : ℂ) :
    theta ι z = ((z.re - ((ι sqrtd).im)⁻¹ * z.im : ℝ) : ℂ) := by
  simp [theta]

theorem theta_embedding (ι : ℤ√(-2) →+* ℂ) (x : ℤ√(-2)) :
    theta ι (ι x) = ((x.re - x.im : ℤ) : ℂ) := by
  rw [theta_apply, embedding_apply]
  have hr := embedding_sqrtd_re ι
  have hi := embedding_sqrtd_im_ne ι
  have key : (((x.re : ℂ) + (x.im : ℂ) * ι sqrtd).re
      - ((ι sqrtd).im)⁻¹ * ((x.re : ℂ) + (x.im : ℂ) * ι sqrtd).im : ℝ) = ((x.re - x.im : ℤ) : ℝ) := by
    simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.intCast_im, hr,
      mul_zero, zero_mul, sub_zero, add_zero, Complex.add_im, Complex.mul_im, zero_add]
    rw [mul_comm ((x.im : ℝ)) _, ← mul_assoc, inv_mul_cancel₀ hi, one_mul]
    push_cast; ring
  rw [key, Complex.ofReal_intCast]

theorem theta_intCast (ι : ℤ√(-2) →+* ℂ) (n : ℤ) : theta ι (n : ℂ) = n := by
  rw [theta_apply]
  simp

theorem theta_intCast_mul (ι : ℤ√(-2) →+* ℂ) (n : ℤ) (z : ℂ) :
    theta ι ((n : ℂ) * z) = (n : ℂ) * theta ι z := by
  have : (n : ℂ) * z = (n : ℝ) • z := by
    rw [Complex.real_smul]; push_cast; ring
  rw [this, LinearMap.map_smul, Complex.real_smul]
  push_cast; ring

section Groups

variable (M : ℕ)

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀(" M ")" => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem T_mem_Gamma1 : ModularGroup.T ∈ Gamma1 M := by
  simp [Gamma1_mem, ModularGroup.T]

theorem one_mem_strictPeriods_Gamma1 : (1 : ℝ) ∈ (Γ₁(M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

theorem T_mem_Gamma0 : ModularGroup.T ∈ Gamma0 M := by
  simp [Gamma0_mem, ModularGroup.T]

theorem one_mem_strictPeriods_Gamma0 : (1 : ℝ) ∈ (Γ₀(M)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma0 M)]
  exact AddSubgroup.mem_zmultiples 1

variable {M}

theorem intCast_zmod_of_dvd {d : ℕ} (hd : d ∣ M) {x : ℤ} {y : ℤ} (h : (x : ZMod M) = y) :
    (x : ZMod d) = y := by
  have := congrArg (ZMod.castHom hd (ZMod d)) h
  simpa using this

theorem Gamma1_le_of_dvd {d : ℕ} (hd : d ∣ M) : Gamma1 M ≤ Gamma1 d := by
  intro γ hγ
  rw [Gamma1_mem] at hγ ⊢
  refine ⟨?_, ?_, ?_⟩
  · have := intCast_zmod_of_dvd (M := M) hd (x := γ 0 0) (y := 1) (by simpa using hγ.1)
    simpa using this
  · have := intCast_zmod_of_dvd (M := M) hd (x := γ 1 1) (y := 1) (by simpa using hγ.2.1)
    simpa using this
  · have := intCast_zmod_of_dvd (M := M) hd (x := γ 1 0) (y := 0) (by simpa using hγ.2.2)
    simpa using this

theorem Gamma0_le_of_dvd {d : ℕ} (hd : d ∣ M) : Gamma0 M ≤ Gamma0 d := by
  intro γ hγ
  rw [Gamma0_mem] at hγ ⊢
  have := intCast_zmod_of_dvd (M := M) hd (x := γ 1 0) (y := 0) (by simpa using hγ)
  simpa using this

def sgn (γ : SL(2, ℤ)) : ℂ := ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ)

theorem sgn_def (γ : SL(2, ℤ)) : sgn γ = ((chiNegThree (((γ 1 1 : ℤ) : ZMod 3).val) : ℤ) : ℂ) :=
  rfl

theorem zmod3_cases (x : ZMod 3) (hx : x ≠ 0) : x = 1 ∨ x = 2 := by
  revert x; decide

theorem det_mod {N : ℕ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  have hdet := γ.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using Gamma0_mem.mp hγ
  have := congrArg (Int.cast : ℤ → ZMod N) hdet
  push_cast at this
  rw [hc] at this
  linear_combination this

theorem gamma0_three_dichotomy (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 3) :
    (γ ∈ Gamma1 3 ∧ sgn γ = 1) ∨ (-γ ∈ Gamma1 3 ∧ sgn γ = -1) := by
  have hprod := det_mod γ hγ
  have hc : ((γ 1 0 : ℤ) : ZMod 3) = 0 := by simpa using Gamma0_mem.mp hγ
  have hd0 : ((γ 1 1 : ℤ) : ZMod 3) ≠ 0 := by
    intro h; rw [h, mul_zero] at hprod; exact zero_ne_one hprod
  rcases zmod3_cases _ hd0 with hd | hd
  · left
    have ha : ((γ 0 0 : ℤ) : ZMod 3) = 1 := by rw [hd, mul_one] at hprod; exact hprod
    refine ⟨(Gamma1_mem 3 γ).mpr ⟨by simpa using ha, by simpa using hd, by simpa using hc⟩, ?_⟩
    rw [sgn_def, hd]
    simp [ZMod.val_one, chiNegThree]
  · right
    have ha : ((γ 0 0 : ℤ) : ZMod 3) = 2 := by
      rw [hd] at hprod
      have : ∀ x : ZMod 3, x * 2 = 1 → x = 2 := by decide
      exact this _ hprod
    refine ⟨(Gamma1_mem 3 (-γ)).mpr ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, ha]; decide
    · rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, hd]; decide
    · rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply, Int.cast_neg, hc, neg_zero]
    · rw [sgn_def, hd]
      have : (2 : ZMod 3).val = 2 := rfl
      rw [this]
      simp [chiNegThree]

theorem sgn_mul_self (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 3) : sgn γ * sgn γ = 1 := by
  rcases gamma0_three_dichotomy γ hγ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> norm_num

theorem slash_neg_one_weight_one (f : ℍ → ℂ) : f ∣[(1 : ℤ)] (-1 : SL(2, ℤ)) = -f := by
  ext τ
  rw [SL_slash_apply]
  simp [denom]

theorem slash_eq_sgn_smul_of_gamma1_three
    (E : ModularForm ((Gamma1 3 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 1)
    (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 3) : (⇑E : ℍ → ℂ) ∣[(1 : ℤ)] γ = sgn γ • (⇑E : ℍ → ℂ) := by
  rcases gamma0_three_dichotomy γ hγ with ⟨h1, hs⟩ | ⟨h1, hs⟩
  · rw [hs, one_smul]
    exact SlashInvariantFormClass.slash_action_eq E _ (Subgroup.mem_map_of_mem _ h1)
  · have hE : (⇑E : ℍ → ℂ) ∣[(1 : ℤ)] (-γ) = ⇑E :=
      SlashInvariantFormClass.slash_action_eq E _ (Subgroup.mem_map_of_mem _ h1)
    rw [hs, show γ = (-1) * (-γ) by simp, SlashAction.slash_mul, slash_neg_one_weight_one,
      SlashAction.neg_slash, hE]
    simp

def restrictMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ} (f : ModularForm Γ k) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' := fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ (hle hγ)
  holo' := f.holo'
  bdd_at_cusps' := fun hc => f.bdd_at_cusps' (hc.mono hle)

@[scoped simp] theorem coe_restrictMF {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} (hle : Γ' ≤ Γ) {k : ℤ}
    (f : ModularForm Γ k) : ⇑(restrictMF hle f) = ⇑f := rfl

end Groups

section Eisenstein

theorem abs_sigmaChi_le (n : ℕ) : |sigmaChi n| ≤ n := by
  unfold sigmaChi
  calc |∑ d ∈ n.divisors, chiNegThree d| ≤ ∑ d ∈ n.divisors, |chiNegThree d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors, (1 : ℤ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        rcases chiNegThree_mem d with h | h | h <;> rw [h] <;> norm_num
    _ = n.divisors.card := by simp
    _ ≤ n := by exact_mod_cast Nat.card_divisors_le_self n

theorem norm_coeff_e1Chi3_le (n : ℕ) :
    ‖((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ)‖ ≤ 7 * n + 1 := by
  rw [EisensteinWeightOne.coeff_e1Chi3]
  split_ifs with h
  · subst h; simp
  · rw [Complex.norm_intCast]
    have := abs_sigmaChi_le n
    have h6 : |((6 * sigmaChi n : ℤ) : ℝ)| ≤ 6 * n := by
      rw [Int.cast_mul, abs_mul]
      push_cast
      rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 6)]
      have h' : ((|sigmaChi n| : ℤ) : ℝ) ≤ n := by exact_mod_cast this
      rw [← Int.cast_abs]
      linarith
    linarith [Nat.cast_nonneg (α := ℝ) n]

theorem exists_E1 :
    ∃ E : ModularForm ((Gamma1 3 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 1,
      ∀ n : ℕ, ModularFormClass.qCoeff (⇑E) n = ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ) := by
  obtain ⟨E, hE⟩ := EisensteinWeightOne.e1Chi3IsModular
  refine ⟨E, fun n => ?_⟩

  have hsum : ∀ z : ℍ, HasSum (fun m : ℕ =>
      ((PowerSeries.coeff m e1Chi3 : ℤ) : ℂ) • Function.Periodic.qParam 1 (z : ℂ) ^ m) (E z) := by
    intro z
    have hq : ‖Function.Periodic.qParam 1 (z : ℂ)‖ < 1 := by
      simpa using z.norm_qParam_lt_one 1
    have hS : Summable fun m : ℕ =>
        ((PowerSeries.coeff m e1Chi3 : ℤ) : ℂ) • Function.Periodic.qParam 1 (z : ℂ) ^ m := by
      have h1 : Summable fun m : ℕ => ((m : ℝ) ^ 1 * ‖Function.Periodic.qParam 1 (z : ℂ)‖ ^ m) :=
        summable_pow_mul_geometric_of_norm_lt_one 1 (by simpa using hq)
      have h0 : Summable fun m : ℕ => ‖Function.Periodic.qParam 1 (z : ℂ)‖ ^ m :=
        summable_geometric_of_lt_one (norm_nonneg _) hq
      refine Summable.of_norm_bounded ((h1.mul_left 7).add h0) fun m => ?_
      rw [norm_smul, norm_pow]
      have := norm_coeff_e1Chi3_le m
      calc ‖((PowerSeries.coeff m e1Chi3 : ℤ) : ℂ)‖ * ‖Function.Periodic.qParam 1 (z:ℂ)‖ ^ m
          ≤ (7 * m + 1) * ‖Function.Periodic.qParam 1 (z:ℂ)‖ ^ m :=
            mul_le_mul_of_nonneg_right this (pow_nonneg (norm_nonneg _) _)
        _ = 7 * ((m : ℝ) ^ 1 * ‖Function.Periodic.qParam 1 (z:ℂ)‖ ^ m)
              + ‖Function.Periodic.qParam 1 (z:ℂ)‖ ^ m := by ring
    convert hS.hasSum using 1
    rw [hE z]
    refine tsum_congr fun m => ?_
    rw [smul_eq_mul, Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 2
    push_cast
    ring
  have := qExpansion_coeff_unique E one_pos
    (ModularFormClass.analyticAt_cuspFunction_zero E one_pos (one_mem_strictPeriods_Gamma1 3)) hsum n
  rw [ModularFormClass.qCoeff]
  exact this.symm

end Eisenstein

section Trick

variable {M : ℕ} [NeZero M]

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀(" M ")" => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem isCusp_gamma1_of_isCusp_gamma0 {c : OnePoint ℝ} (hc : IsCusp c Γ₀(M)) : IsCusp c Γ₁(M) := by
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact hc

def trickForm (h3 : 3 ∣ M) (h : CuspForm Γ₁(M) 1)
    (hh : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → (⇑h : ℍ → ℂ) ∣[(1 : ℤ)] γ = sgn γ • (⇑h : ℍ → ℂ))
    (E : ModularForm ((Gamma1 3 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 1) :
    CuspForm Γ₀(M) 2 where
  toFun := ⇑h * ⇑E
  slash_action_eq' := by
    intro A hA
    obtain ⟨γ, hγ, rfl⟩ := hA
    have hγ3 : γ ∈ Gamma0 3 := Gamma0_le_of_dvd h3 hγ
    change (⇑h * ⇑E) ∣[(1 : ℤ) + 1] (γ : GL (Fin 2) ℝ) = ⇑h * ⇑E
    rw [← SL_slash, mul_slash_SL2, hh γ hγ, slash_eq_sgn_smul_of_gamma1_three E γ hγ3]
    ext τ
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    have := sgn_mul_self γ hγ3
    linear_combination (h τ * E τ) * this
  holo' := (h.mulModularForm (restrictMF (Subgroup.map_mono (Gamma1_le_of_dvd h3)) E)).holo'
  zero_at_cusps' := fun hc =>
    (h.mulModularForm (restrictMF (Subgroup.map_mono (Gamma1_le_of_dvd h3)) E)).zero_at_cusps'
      (isCusp_gamma1_of_isCusp_gamma0 hc)

theorem coe_trickForm (h3 : 3 ∣ M) (h : CuspForm Γ₁(M) 1)
    (hh : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → (⇑h : ℍ → ℂ) ∣[(1 : ℤ)] γ = sgn γ • (⇑h : ℍ → ℂ))
    (E : ModularForm ((Gamma1 3 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 1) :
    ⇑(trickForm h3 h hh E) = ⇑h * ⇑E := rfl

theorem qCoeff_trickForm (h3 : 3 ∣ M) (h : CuspForm Γ₁(M) 1)
    (hh : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → (⇑h : ℍ → ℂ) ∣[(1 : ℤ)] γ = sgn γ • (⇑h : ℍ → ℂ))
    (E : ModularForm ((Gamma1 3 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 1)
    (hE : ∀ n : ℕ, ModularFormClass.qCoeff (⇑E) n = ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ))
    (ι : ℤ√(-2) →+* ℂ) (c : ℕ → ℤ√(-2)) (hc : ∀ n, ModularFormClass.qCoeff (⇑h) n = ι (c n))
    (n : ℕ) :
    ModularFormClass.qCoeff (⇑(trickForm h3 h hh E)) n
      = ι (PowerSeries.coeff n (PowerSeries.mk c * e1Chi3In (ℤ√(-2)))) := by
  rw [ModularFormClass.qCoeff, coe_trickForm,
    qExpansion_mul (ModularFormClass.analyticAt_cuspFunction_zero h one_pos
        (one_mem_strictPeriods_Gamma1 M))
      (ModularFormClass.analyticAt_cuspFunction_zero E one_pos (one_mem_strictPeriods_Gamma1 3)),
    PowerSeries.coeff_mul, PowerSeries.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [map_mul, PowerSeries.coeff_mk, e1Chi3In, PowerSeries.coeff_map, Int.coe_castRingHom,
    map_intCast]
  have h1 := hc ij.1
  have h2 := hE ij.2
  rw [ModularFormClass.qCoeff] at h1 h2
  rw [h1, h2]

end Trick

section Descent

variable {M : ℕ} [NeZero M]

local notation "Γ₀(" M ")" => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def qCoeffLM (M : ℕ) [NeZero M] (n : ℕ) : CuspForm Γ₀(M) 2 →ₗ[ℂ] ℂ where
  toFun f := ModularFormClass.qCoeff (⇑f) n
  map_add' f g := by
    simp only [ModularFormClass.qCoeff, CuspForm.coe_add]
    rw [qExpansion_add
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_Gamma0 M))
      (ModularFormClass.analyticAt_cuspFunction_zero g one_pos (one_mem_strictPeriods_Gamma0 M)),
      map_add]
  map_smul' a f := by
    simp only [ModularFormClass.qCoeff, CuspForm.IsGLPos.coe_smul, RingHom.id_apply]
    rw [qExpansion_smul
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods_Gamma0 M)),
      map_smul, smul_eq_mul]

@[scoped simp] theorem qCoeffLM_apply (n : ℕ) (f : CuspForm Γ₀(M) 2) :
    qCoeffLM M n f = ModularFormClass.qCoeff (⇑f) n := rfl

theorem exists_qCoeff_eq_theta (hbasis : HasIntegralBasis M) (θ : ℂ →ₗ[ℝ] ℂ)
    (hθ : ∀ (m : ℤ) (z : ℂ), θ ((m : ℂ) * z) = (m : ℂ) * θ z)
    (F : CuspForm Γ₀(M) 2) :
    ∃ f : CuspForm Γ₀(M) 2, ∀ n : ℕ,
      ModularFormClass.qCoeff (⇑f) n = θ (ModularFormClass.qCoeff (⇑F) n) := by
  have hF : F ∈ Submodule.span ℂ (qIntegralSet M) := by rw [hbasis]; exact Submodule.mem_top
  obtain ⟨w, t, hts, -, hsum⟩ := Submodule.mem_span_iff_exists_finset_subset.mp hF
  refine ⟨∑ v ∈ t, θ (w v) • v, fun n => ?_⟩
  have hlin : ∀ G : CuspForm Γ₀(M) 2, ModularFormClass.qCoeff (⇑G) n = qCoeffLM M n G :=
    fun G => rfl
  rw [hlin, map_sum, ← hsum, hlin, map_sum, map_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, qCoeffLM_apply]
  obtain ⟨m, hm⟩ := Subring.mem_bot.mp (hts hv n)
  rw [← hm, mul_comm (w v), hθ, mul_comm]

end Descent

section Character

theorem chiNegThree_val_mul (x y : ZMod 3) :
    chiNegThree (x * y).val = chiNegThree x.val * chiNegThree y.val := by
  revert x y; decide

def chi3 : DirichletCharacter ℂ 3 where
  toFun x := (chiNegThree x.val : ℂ)
  map_one' := by
    rw [ZMod.val_one]; simp [chiNegThree]
  map_mul' x y := by
    simp only [chiNegThree_val_mul, Int.cast_mul]
  map_nonunit' x hx := by
    have h0 : x = 0 := by
      by_contra h
      rcases zmod3_cases x h with rfl | rfl
      · exact hx isUnit_one
      · exact hx (IsUnit.of_mul_eq_one (2 : ZMod 3) (by decide))
    subst h0
    simp [chiNegThree]

theorem chi3_apply (x : ZMod 3) : chi3 x = (chiNegThree x.val : ℂ) := rfl

variable {M : ℕ} [NeZero M]

def chiM (h3 : 3 ∣ M) : DirichletCharacter ℂ M := DirichletCharacter.changeLevel h3 chi3

theorem chiM_apply_of_isUnit (h3 : 3 ∣ M) {x : ZMod M} (hx : IsUnit x) :
    chiM h3 x = (chiNegThree ((ZMod.castHom h3 (ZMod 3) x).val) : ℂ) := by
  obtain ⟨u, rfl⟩ := hx
  rw [chiM, DirichletCharacter.changeLevel_eq_cast_of_dvd, chi3_apply, ZMod.castHom_apply]

theorem chiM_intCast (h3 : 3 ∣ M) {d : ℤ} (hd : IsUnit (d : ZMod M)) :
    chiM h3 (d : ZMod M) = ((chiNegThree (((d : ℤ) : ZMod 3).val) : ℤ) : ℂ) := by
  rw [chiM_apply_of_isUnit h3 hd, map_intCast]

theorem chiM_natCast_prime (h3 : 3 ∣ M) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) :
    chiM h3 (p : ZMod M) = (chiNegThree p : ℂ) := by
  rw [chiM_apply_of_isUnit h3 (ZMod.isUnit_prime_of_not_dvd hp hpM), map_natCast,
    chiNegThree_zmod_val]

theorem chiM_gamma (h3 : 3 ∣ M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    chiM h3 ((γ 1 1 : ℤ) : ZMod M) = sgn γ := by
  have hu : IsUnit (((γ 1 1 : ℤ) : ZMod M)) :=
    IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact det_mod γ hγ)
  rw [chiM_intCast h3 hu, sgn_def]

end Character

section Package

variable {M : ℕ} [NeZero M]

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀(" M ")" => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem map_e1Chi3In {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    PowerSeries.map f (e1Chi3In R) = e1Chi3In S := by
  rw [e1Chi3In, e1Chi3In]
  ext n
  simp only [PowerSeries.coeff_map, Int.coe_castRingHom, map_intCast]

theorem map_mk_comp {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : ℕ → R) :
    PowerSeries.map f (PowerSeries.mk c) = PowerSeries.mk (fun n => f (c n)) := by
  ext n
  simp

theorem map_coeff_mk_mul_e1 {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : ℕ → R)
    (n : ℕ) :
    f (PowerSeries.coeff n (PowerSeries.mk c * e1Chi3In R))
      = PowerSeries.coeff n (PowerSeries.mk (fun m => f (c m)) * e1Chi3In S) := by
  rw [← PowerSeries.coeff_map, map_mul, map_mk_comp, map_e1Chi3In]

theorem isLatticeRealized_of_form (h3 : 3 ∣ M) (hbasis : HasIntegralBasis M)
    (E : ModularForm ((Gamma1 3 : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) 1)
    (hE : ∀ n : ℕ, ModularFormClass.qCoeff (⇑E) n = ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ))
    (ι : ℤ√(-2) →+* ℂ) (h : CuspForm Γ₁(M) 1)
    (hh : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → (⇑h : ℍ → ℂ) ∣[(1 : ℤ)] γ = sgn γ • (⇑h : ℍ → ℂ))
    (c : ℕ → ℤ√(-2)) (hc : ∀ n, ModularFormClass.qCoeff (⇑h) n = ι (c n))
    (a : ℕ → ℤ) (ha : ∀ n, ((a n : ℤ) : ZMod 3) = red (c n)) :
    IsLatticeRealized M a := by
  set F := trickForm h3 h hh E with hFdef
  set c' : ℕ → ℤ√(-2) := fun n => PowerSeries.coeff n (PowerSeries.mk c * e1Chi3In (ℤ√(-2)))
    with hc'
  have hF : ∀ n, ModularFormClass.qCoeff (⇑F) n = ι (c' n) :=
    fun n => qCoeff_trickForm h3 h hh E hE ι c hc n
  obtain ⟨f, hf⟩ := exists_qCoeff_eq_theta hbasis (theta ι) (theta_intCast_mul ι) F
  set af : ℕ → ℤ := fun n => (c' n).re - (c' n).im with haf
  have hfq : ∀ n, ModularFormClass.qCoeff (⇑f) n = ((af n : ℤ) : ℂ) := fun n => by
    rw [hf n, hF n, theta_embedding]
  refine ⟨f, fun n => Subring.mem_bot.mpr ⟨af n, (hfq n).symm⟩, af, fun n => (hfq n).symm,
    fun n => ?_⟩

  rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, ← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub,
    sub_eq_zero]
  have hL : ((af n : ℤ) : ZMod 3) = red (c' n) := by rw [red_apply]
  have hR : red (c' n) = PowerSeries.coeff n
      (PowerSeries.mk (fun m => ((a m : ℤ) : ZMod 3)) * e1Chi3In (ZMod 3)) := by
    rw [hc', map_coeff_mk_mul_e1 red c n]
    congr 2
    ext m
    simp only [PowerSeries.coeff_mk, ha]
  have hB : (((bridgeProduct a).coeff n : ℤ) : ZMod 3) = PowerSeries.coeff n
      (PowerSeries.mk (fun m => ((a m : ℤ) : ZMod 3)) * e1Chi3In (ZMod 3)) := by
    have := map_coeff_mk_mul_e1 (Int.castRingHom (ZMod 3)) a n
    rw [bridgeProduct]
    exact this
  rw [hL, hR, hB]

end Package

section Assembly

variable {M : ℕ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem main (M : ℕ) [hM : NeZero M] (h3 : 3 ∣ M) (b : ℕ → ℤ√(-2))
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b)
    (hbasis : CuspForm.HasIntegralBasis M)
    (hreal : CuspForm.IsWeightOneChiNegThreeRealized M b) :
    ∃ a : ℕ → ℤ,
      FormalHecke.IsEigensystem (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
      CuspForm.IsLatticeRealized M a ∧
      ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = red (b n) := by
  obtain ⟨ι, g, hg⟩ := hreal

  set eS : ℕ → ℤ√(-2) := fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2)) with heS
  set eZ : ℕ → ℤ := fun ℓ => if ℓ ∣ M then 0 else chiNegThree ℓ with heZ
  have heS_apply : ∀ ℓ, eS ℓ = ((eZ ℓ : ℤ) : ℤ√(-2)) := fun ℓ => by
    simp only [heS, heZ]; split_ifs <;> simp

  have hb0 : b 0 = 0 := by
    have h0 : ModularFormClass.qCoeff (⇑g) 0 = 0 :=
      CuspFormClass.qExpansion_coeff_zero g one_pos (one_mem_strictPeriods_Gamma1 M)
    rw [hg 0] at h0
    exact embedding_injective ι (by rw [h0, map_zero])

  have hneb : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑g : ℍ → ℂ) ∣[(1 : ℤ)] γ = sgn γ • (⇑g : ℍ → ℂ) := by
    intro γ hγ
    have key := CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen (1 : ℤ) g (chiM h3)
      (fun p hp hpM => ⟨ι (b p), fun n => ?_⟩) γ hγ
    · rw [chiM_gamma h3 γ hγ] at key
      exact key
    · have H := congrArg ι (heig.2 p hp n)
      simp only [map_add, map_mul, heS_apply, heZ, if_neg hpM, map_intCast, apply_ite ι,
        map_zero] at H
      rw [hg, hg, chiM_natCast_prime h3 hp hpM, sub_self, zpow_zero, mul_one, mul_comm n p]
      convert H using 3
      exact hg n
  obtain ⟨E, hE⟩ := exists_E1

  set cZ : ℕ → ℤ := fun ℓ => (b ℓ).re - (b ℓ).im with hcZ
  refine ⟨ext eZ cZ, ext_isEigensystem eZ cZ, ?_, ?_⟩
  · refine isLatticeRealized_of_form h3 hbasis E hE ι g hneb b hg _ fun n => ?_
    exact (congr_ext_red h3 b heig hb0 n)
  · exact congr_ext_red h3 b heig hb0
  where

    congr_ext_red {M : ℕ} (h3 : 3 ∣ M) (b : ℕ → ℤ√(-2))
        (heig : FormalHecke.IsEigensystem
          (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b)
        (hb0 : b 0 = 0) (n : ℕ) :
        (((ext (fun ℓ => if ℓ ∣ M then 0 else chiNegThree ℓ)
            (fun ℓ => (b ℓ).re - (b ℓ).im) n : ℤ) : ZMod 3)) = red (b n) := by
      have hL := map_ext (fun ℓ => if ℓ ∣ M then (0:ℤ) else chiNegThree ℓ)
        (fun ℓ => (b ℓ).re - (b ℓ).im) (Int.castRingHom (ZMod 3)) n
      have hredE : FormalHecke.IsEigensystem (fun ℓ => red (if ℓ ∣ M then 0 else
          ((chiNegThree ℓ : ℤ) : ℤ√(-2)))) (fun m => red (b m)) := isEigensystem_map red heig
      have hR := eq_ext_of_isEigensystem hredE (by simp [hb0]) n
      rw [Int.coe_castRingHom] at hL
      simp only [] at hL
      rw [hL, hR]
      congr 1
      · funext ℓ
        split_ifs <;> simp
      · funext ℓ
        rw [red_apply]

end Assembly

end WeightTwoCongruenceLiftThree
p2m_reactivate "P2MW.S_CuspForm_exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd.WeightTwoCongruenceLiftThree"

end
p2m_reactivate "P2MW.S_CuspForm_exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd.WeightTwoCongruenceLiftThree"

theorem solution
    (M : ℕ) [NeZero M] (h3 : 3 ∣ M) (b : ℕ → ℤ√(-2))
    (heig : FormalHecke.IsEigensystem
      (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ√(-2))) b)
    (hbasis : CuspForm.HasIntegralBasis M)
    (hreal : CuspForm.IsWeightOneChiNegThreeRealized M b) :
    ∃ a : ℕ → ℤ,
      FormalHecke.IsEigensystem (fun ℓ => if ℓ ∣ M then 0 else ((chiNegThree ℓ : ℤ) : ℤ)) a ∧
      CuspForm.IsLatticeRealized M a ∧
      ∀ n : ℕ, ((a n : ℤ) : ZMod 3) = red (b n) :=
  WeightTwoCongruenceLiftThree.main M h3 b heig hbasis hreal

end S_CuspForm_exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd
end P2MW
export P2MW.S_CuspForm_exists_isLatticeRealized_of_isWeightOneChiNegThreeRealized_of_three_dvd (solution)
