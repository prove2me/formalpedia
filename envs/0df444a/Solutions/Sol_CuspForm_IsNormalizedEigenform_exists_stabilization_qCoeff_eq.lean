-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.exists_stabilization_qCoeff_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c188edb7-e3e1-5da2-83b5-419de8a90425

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_stabilization_qCoeff_eq

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup
open scoped ModularForm MatrixGroups

namespace DichR4

theorem one_mem_strictPeriods (R : ℕ) :
    (1 : ℝ) ∈ ((Gamma0 R : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples _

theorem analyticAt_cusp {M : ℕ} {k : ℤ} (f : CuspForm (Gamma0 M) k) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 ⇑f) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero f one_pos (one_mem_strictPeriods M)

theorem qCoeff_smul {M : ℕ} {k : ℤ} (c : ℂ) (f : CuspForm (Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(c • f)) n = c * ModularFormClass.qCoeff (⇑f) n := by
  unfold ModularFormClass.qCoeff
  rw [show (⇑(c • f) : UpperHalfPlane → ℂ) = c • (⇑f) from by ext z; rfl,
    UpperHalfPlane.qExpansion_smul (analyticAt_cusp f), map_smul, smul_eq_mul]

theorem qCoeff_add {M : ℕ} {k : ℤ} (f g : CuspForm (Gamma0 M) k) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(f + g)) n
      = ModularFormClass.qCoeff (⇑f) n + ModularFormClass.qCoeff (⇑g) n := by
  unfold ModularFormClass.qCoeff
  rw [CuspForm.coe_add,
    UpperHalfPlane.qExpansion_add (analyticAt_cusp f) (analyticAt_cusp g), map_add]

theorem qCoeff_rescaleLin {R d N : ℕ} [NeZero N] (hdRN : d * R ∣ N)
    (f : CuspForm (Gamma0 R) 2) (n : ℕ) :
    ModularFormClass.qCoeff (⇑(FreyPackage.ModMCarrier.rescaleLin hdRN 2 f)) n
      = (d : ℂ) * (if d ∣ n then ModularFormClass.qCoeff (⇑f) (n / d) else 0) := by
  have hd : d ≠ 0 := by
    rintro rfl
    exact NeZero.ne N (Nat.eq_zero_of_zero_dvd (by simpa using hdRN))
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd
  set G := FreyPackage.ModMCarrier.rescaleLin hdRN 2 f with hG
  have hcoe : ⇑G = fun τ => (d : ℂ) * f (ModularForm.heckeDiagMatrix d • τ) := by
    funext τ
    show (⇑f ∣[(2 : ℤ)] ModularForm.heckeDiagMatrix d) τ = _
    rw [ModularForm.slash_heckeDiagMatrix_apply 2 hd]
    norm_num
  have hcoe2 : ⇑((d : ℂ)⁻¹ • G) = fun τ => f (ModularForm.heckeDiagMatrix d • τ) := by
    funext τ
    rw [CuspForm.IsGLPos.coe_smul, Pi.smul_apply, hcoe, smul_eq_mul,
      inv_mul_cancel_left₀ hdC]
  calc ModularFormClass.qCoeff (⇑G) n
      = ModularFormClass.qCoeff (⇑((d : ℂ) • ((d : ℂ)⁻¹ • G))) n := by
        rw [smul_smul, mul_inv_cancel₀ hdC, one_smul]
    _ = (d : ℂ) * ModularFormClass.qCoeff (⇑((d : ℂ)⁻¹ • G)) n := qCoeff_smul _ _ n
    _ = (d : ℂ) * (if d ∣ n then ModularFormClass.qCoeff (⇑f) (n / d) else 0) := by
        rw [hcoe2]
        congr 1
        exact ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul f
          (one_mem_strictPeriods R) hd n

end DichR4

end

open DichR4 in
theorem solution
    {M : ℕ} [NeZero M] {g : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hg : g.IsNormalizedEigenform) (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M)
    (ε : ℂ) (hε : ε ^ 2 - ModularFormClass.qCoeff g p * ε + p = 0) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 (M * p)) 2, f.IsNormalizedEigenform ∧
      (∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) ∧
      ModularFormClass.qCoeff f p = ε := by
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero (NeZero.ne M) hp.ne_zero⟩
  have hp0 : p ≠ 0 := hp.ne_zero
  have hpC : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0

  set a : ℕ → ℂ := fun n => ModularFormClass.qCoeff (⇑g) n with ha
  set ε' : ℂ := a p - ε with hε'
  have hvieta : ε * ε' = p := by
    simp only [hε', ha]
    linear_combination -hε
  have hsum : ε + ε' = a p := by simp only [hε']; ring

  have h1 : 1 * M ∣ M * p := ⟨p, by ring⟩
  have h2 : p * M ∣ M * p := dvd_of_eq (Nat.mul_comm p M)
  let V₁ : CuspForm (CongruenceSubgroup.Gamma0 (M * p)) 2 := FreyPackage.ModMCarrier.rescaleLin h1 2 g
  let Vp : CuspForm (CongruenceSubgroup.Gamma0 (M * p)) 2 := FreyPackage.ModMCarrier.rescaleLin h2 2 g
  let f : CuspForm (CongruenceSubgroup.Gamma0 (M * p)) 2 := V₁ + (-(ε' * (p : ℂ)⁻¹)) • Vp

  set b : ℕ → ℂ := fun n => if p ∣ n then a (n / p) else 0 with hb
  have hmul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n := hg.qCoeff_mul_of_coprime
  have hc : ∀ n : ℕ, ModularFormClass.qCoeff (⇑f) n = a n - ε' * b n := by
    intro n
    show ModularFormClass.qCoeff (⇑(V₁ + (-(ε' * (p : ℂ)⁻¹)) • Vp)) n = _
    rw [qCoeff_add, qCoeff_smul, qCoeff_rescaleLin h1 g n, qCoeff_rescaleLin h2 g n]
    simp only [hb, ha, Nat.cast_one, one_mul, one_dvd, if_true, Nat.div_one]
    by_cases hpn : p ∣ n
    · simp only [if_pos hpn]
      field_simp
      ring
    · simp only [if_neg hpn]
      ring

  have hb_of_not : ∀ n : ℕ, ¬ p ∣ n → b n = 0 := fun n hn => by simp only [hb, if_neg hn]
  have hb_of_dvd : ∀ n : ℕ, p ∣ n → b n = a (n / p) := fun n hn => by simp only [hb, if_pos hn]
  have hc_of_not : ∀ n : ℕ, ¬ p ∣ n → ModularFormClass.qCoeff (⇑f) n = a n := fun n hn => by
    rw [hc n, hb_of_not n hn, mul_zero, sub_zero]
  have ha1 : a 1 = 1 := hg.qCoeff_one
  have hc1 : ModularFormClass.qCoeff (⇑f) 1 = 1 := by
    rw [hc_of_not 1 hp.not_dvd_one, ha1]
  have hcp : ModularFormClass.qCoeff (⇑f) p = ε := by
    rw [hc p, hb_of_dvd p dvd_rfl, Nat.div_self hp.pos, ha1, mul_one, hε']
    ring

  have hpow_div : ∀ k : ℕ, p ^ (k + 1) / p = p ^ k := fun k =>
    Nat.div_eq_of_eq_mul_left hp.pos (pow_succ p k)
  have hcpow : ∀ k : ℕ, ModularFormClass.qCoeff (⇑f) (p ^ (k + 1)) =
      ε * ModularFormClass.qCoeff (⇑f) (p ^ k) := by
    intro k
    cases k with
    | zero =>
      rw [zero_add, pow_one, pow_zero, hcp, hc1, mul_one]
    | succ j =>

      rw [hc (p ^ (j + 1 + 1)), hb_of_dvd _ (dvd_pow_self p (Nat.succ_ne_zero _)), hpow_div,
        hc (p ^ (j + 1)), hb_of_dvd _ (dvd_pow_self p (Nat.succ_ne_zero _)), hpow_div]
      have hrec := hg.qCoeff_prime_pow_of_not_dvd p j hp hpM

      have hrec' : a (p ^ (j + 1 + 1)) = a p * a (p ^ (j + 1)) - (p : ℂ) * a (p ^ j) := hrec
      rw [hrec', ← hsum, ← hvieta]
      ring

  have hnot_dvd_pow : ∀ (q : ℕ), q.Prime → q ≠ p → ∀ k : ℕ, ¬ p ∣ q ^ k := by
    intro q hq hqp k h
    exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)).symm
  refine ⟨f, ⟨hc1, ?_, ?_, ?_⟩, hc_of_not, hcp⟩
  ·
    intro m n hmn
    by_cases hpm : p ∣ m
    · have hpn : ¬ p ∣ n := fun hpn =>
        hp.ne_one (Nat.eq_one_of_dvd_one (hmn.gcd_eq_one ▸ Nat.dvd_gcd hpm hpn))
      have hmpn : (m / p).Coprime n := Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hpm) hmn
      have hdiv : m * n / p = m / p * n := by
        rw [Nat.mul_comm m n, Nat.mul_div_assoc n hpm, Nat.mul_comm]
      rw [hc (m * n), hb_of_dvd _ (dvd_mul_of_dvd_left hpm n), hdiv, hc m, hb_of_dvd m hpm,
        hc_of_not n hpn]
      show a (m * n) - ε' * a (m / p * n) = (a m - ε' * a (m / p)) * a n
      rw [hmul m n hmn, hmul (m / p) n hmpn]
      ring
    · by_cases hpn : p ∣ n
      · have hmnp : m.Coprime (n / p) := Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hpn) hmn
        have hdiv : m * n / p = m * (n / p) := Nat.mul_div_assoc m hpn
        rw [hc (m * n), hb_of_dvd _ (dvd_mul_of_dvd_right hpn m), hdiv, hc_of_not m hpm, hc n,
          hb_of_dvd n hpn]
        show a (m * n) - ε' * a (m * (n / p)) = a m * (a n - ε' * a (n / p))
        rw [hmul m n hmn, hmul m (n / p) hmnp]
        ring
      · have hpmn : ¬ p ∣ m * n := fun h => ((hp.dvd_mul).mp h).elim hpm hpn
        rw [hc_of_not _ hpmn, hc_of_not m hpm, hc_of_not n hpn]
        exact hg.qCoeff_mul_of_coprime m n hmn
  ·
    intro q r hq hqN
    have hqp : q ≠ p := fun h => hqN (h ▸ dvd_mul_left p M)
    have hqM : ¬ q ∣ M := fun h => hqN (dvd_mul_of_dvd_left h p)
    rw [hc_of_not _ (hnot_dvd_pow q hq hqp (r + 2)), hc_of_not _ (hnot_dvd_pow q hq hqp (r + 1)),
      hc_of_not _ (hnot_dvd_pow q hq hqp r), hc_of_not q (by simpa using hnot_dvd_pow q hq hqp 1)]
    exact hg.qCoeff_prime_pow_of_not_dvd q r hq hqM
  ·
    intro q r hq hqN
    by_cases hqp : q = p
    · subst hqp
      rw [hcpow (r + 1), hcp]
    · have hqM : q ∣ M := ((hq.dvd_mul).mp hqN).resolve_right
        (fun h => hqp ((Nat.prime_dvd_prime_iff_eq hq hp).mp h))
      rw [hc_of_not _ (hnot_dvd_pow q hq hqp (r + 2)), hc_of_not _ (hnot_dvd_pow q hq hqp (r + 1)),
        hc_of_not q (by simpa using hnot_dvd_pow q hq hqp 1)]
      exact hg.qCoeff_prime_pow_of_dvd q r hq hqM

end S_CuspForm_IsNormalizedEigenform_exists_stabilization_qCoeff_eq
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_exists_stabilization_qCoeff_eq (solution)
