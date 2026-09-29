-- Prove2me | solution 1 for CuspForm.IsNormalizedEigenform.exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/be974406-fe7c-5b53-a789-1580316ba52d

import Definitions.Def_FreyPackage_ModMCarrier_Rescale
import Definitions.Def_ModularForm_HeckeOperatorForms
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul
import Theorems.Thm_ModularFormClass_qCoeff_heckeU
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite

set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

namespace K1C3Deplete

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

theorem qCoeff_heckeULin {M p : ℕ} [NeZero M] (hp : p ≠ 0) (hpM : p ∣ M)
    (F : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (n : ℕ) :
    ModularFormClass.qCoeff (CuspForm.heckeULin 2 hpM F) n = ModularFormClass.qCoeff F (n * p) := by
  rw [CuspForm.coe_heckeULin_apply]
  exact ModularFormClass.qCoeff_heckeU F (hΓ M) hp n

theorem qCoeff_deplete {L L' q : ℕ} [NeZero L] [NeZero L'] (hq : q ≠ 0) (hqL' : q ∣ L')
    (hqL : q * L' ∣ L)
    (F : CuspForm (CongruenceSubgroup.Gamma0 L) 2) (F' : CuspForm (CongruenceSubgroup.Gamma0 L') 2)
    (a : ℕ → ℂ) (hF : ∀ n, ModularFormClass.qCoeff F n = a n)
    (hF' : ∀ n, ModularFormClass.qCoeff F' n = a n) (n : ℕ) :
    ModularFormClass.qCoeff
        (⇑(F - (q : ℂ)⁻¹ • FreyPackage.ModMCarrier.rescaleLin hqL 2 (CuspForm.heckeULin 2 hqL' F'))) n
      = if q ∣ n then 0 else a n := by
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  rw [qCoeff_sub_smul, hF, qCoeff_rescaleLin hqL hq]
  split_ifs with hqn
  · rw [qCoeff_heckeULin hq hqL', hF', Nat.div_mul_cancel hqn, ← mul_assoc, inv_mul_cancel₀ hqC,
      one_mul, sub_self]
  · rw [mul_zero, sub_zero]

theorem isNormalizedEigenform_of_qCoeff_eq_ite {M L : ℕ} [NeZero M]
    {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2} (hf : f.IsNormalizedEigenform)
    {q : ℕ} (hq : q.Prime) (hqL : q ∣ L)
    (hLM : ∀ p : ℕ, p.Prime → p ≠ q → (p ∣ L ↔ p ∣ M))
    (g : CuspForm (CongruenceSubgroup.Gamma0 L) 2)
    (hg : ∀ n : ℕ, ModularFormClass.qCoeff g n =
      if q ∣ n then 0 else ModularFormClass.qCoeff f n) :
    g.IsNormalizedEigenform := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hg, if_neg hq.not_dvd_one, hf.qCoeff_one]
  · intro m n hmn
    rw [hg, hg, hg]
    by_cases hm : q ∣ m
    · rw [if_pos (dvd_mul_of_dvd_left hm n), if_pos hm, zero_mul]
    by_cases hn : q ∣ n
    · rw [if_pos (dvd_mul_of_dvd_right hn m), if_pos hn, mul_zero]
    rw [if_neg (fun h => (hq.dvd_mul.mp h).elim hm hn), if_neg hm, if_neg hn,
      hf.qCoeff_mul_of_coprime m n hmn]
  · intro p r hp hpL
    have hpq : p ≠ q := fun h => hpL (h ▸ hqL)
    have hpM : ¬ p ∣ M := fun h => hpL ((hLM p hp hpq).mpr h)
    have hnd : ∀ i : ℕ, ¬ q ∣ p ^ i := fun i h =>
      hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)).symm
    rw [hg, hg, hg, hg, if_neg (hnd _), if_neg (hnd _), if_neg (hnd _),
      if_neg (by simpa using hnd 1)]
    exact hf.qCoeff_prime_pow_of_not_dvd p r hp hpM
  · intro p r hp hpL
    by_cases hpq : p = q
    · subst hpq
      rw [hg, hg, if_pos (dvd_pow_self p (Nat.succ_ne_zero _)), if_pos (dvd_refl p), zero_mul]
    · have hpM : p ∣ M := (hLM p hp hpq).mp hpL
      have hnd : ∀ i : ℕ, ¬ q ∣ p ^ i := fun i h =>
        hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow h)).symm
      rw [hg, hg, hg, if_neg (hnd _), if_neg (hnd _), if_neg (by simpa using hnd 1)]
      exact hf.qCoeff_prime_pow_of_dvd p r hp hpM

end K1C3Deplete

open K1C3Deplete in
theorem solution
    {M : ℕ} [NeZero M] {f : CuspForm (CongruenceSubgroup.Gamma0 M) 2}
    (hf : f.IsNormalizedEigenform) {q : ℕ} (hq : q.Prime) (e : ℕ) (he : 1 ≤ e)
    (he2 : ¬ q ∣ M → 2 ≤ e) [NeZero (M * q ^ e)] :
    ∃ g : CuspForm (CongruenceSubgroup.Gamma0 (M * q ^ e)) 2, g.IsNormalizedEigenform ∧
      ∀ n : ℕ, ModularFormClass.qCoeff g n =
        if q ∣ n then 0 else ModularFormClass.qCoeff f n := by

  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  haveI hL' : NeZero (M * q ^ e') := ⟨mul_ne_zero (NeZero.ne M) (pow_ne_zero _ hq.ne_zero)⟩
  have hqL' : q ∣ M * q ^ e' := by
    rcases Nat.eq_zero_or_pos e' with h0 | hpos
    · subst h0
      have hqM : q ∣ M := by
        by_contra h
        have := he2 h
        omega
      simpa using hqM
    · exact dvd_mul_of_dvd_right (dvd_pow_self q hpos.ne') M
  have hqL : q * (M * q ^ e') ∣ M * q ^ (e' + 1) := ⟨1, by ring⟩
  have h1L : 1 * M ∣ M * q ^ (e' + 1) := ⟨q ^ (e' + 1), by ring⟩
  have h1L' : 1 * M ∣ M * q ^ e' := ⟨q ^ e', by ring⟩
  set F : CuspForm (CongruenceSubgroup.Gamma0 (M * q ^ (e' + 1))) 2 :=
    FreyPackage.ModMCarrier.rescaleLin h1L 2 f with hFdef
  set F' : CuspForm (CongruenceSubgroup.Gamma0 (M * q ^ e')) 2 :=
    FreyPackage.ModMCarrier.rescaleLin h1L' 2 f with hF'def
  refine ⟨F - (q : ℂ)⁻¹ • FreyPackage.ModMCarrier.rescaleLin hqL 2 (CuspForm.heckeULin 2 hqL' F'),
    ?_, ?_⟩
  · refine isNormalizedEigenform_of_qCoeff_eq_ite hf hq
      (dvd_mul_of_dvd_right (dvd_pow_self q (Nat.succ_ne_zero e')) M) (fun p hp hpq => ?_) _
      (fun n => ?_)
    · constructor
      · intro h
        rcases hp.dvd_mul.mp h with h | h
        · exact h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow h)) hpq
      · exact fun h => dvd_mul_of_dvd_left h _
    · exact qCoeff_deplete hq.ne_zero hqL' hqL F F' (fun n => ModularFormClass.qCoeff f n)
        (fun n => qCoeff_rescaleLin_one h1L f n) (fun n => qCoeff_rescaleLin_one h1L' f n) n
  · intro n
    exact qCoeff_deplete hq.ne_zero hqL' hqL F F' (fun n => ModularFormClass.qCoeff f n)
      (fun n => qCoeff_rescaleLin_one h1L f n) (fun n => qCoeff_rescaleLin_one h1L' f n) n

end

end S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite
end P2MW
export P2MW.S_CuspForm_IsNormalizedEigenform_exists_isNormalizedEigenform_level_mul_pow_qCoeff_eq_ite (solution)
