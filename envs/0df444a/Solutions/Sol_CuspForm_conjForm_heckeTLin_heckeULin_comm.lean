-- Prove2me | solution 1 for CuspForm.conjForm_heckeTLin_heckeULin_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ef355b8a-8fbb-51e4-99f9-63c442b263be

import Definitions.Def_ModularForm_HeckeOperatorForms
import Mathlib.NumberTheory.ModularForms.Identities
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_conjForm_heckeTLin_heckeULin_comm
set_option autoImplicit false

noncomputable section

open UpperHalfPlane ModularForm

namespace ConjFormHecke

private def refl (τ : ℍ) : ℍ := ⟨-((starRingEnd ℂ) (τ : ℂ)), by simpa using τ.im_pos⟩

private theorem coe_refl (τ : ℍ) : ((refl τ : ℍ) : ℂ) = -((starRingEnd ℂ) (τ : ℂ)) := rfl

private def reflectFun (g : ℍ → ℂ) : ℍ → ℂ := fun τ => (starRingEnd ℂ) (g (refl τ))

private theorem reflectFun_apply (g : ℍ → ℂ) (τ : ℍ) :
    reflectFun g τ = (starRingEnd ℂ) (g (refl τ)) := rfl

private theorem refl_heckeDiagMatrix_smul {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    refl (heckeDiagMatrix p • τ) = heckeDiagMatrix p • refl τ := by
  apply UpperHalfPlane.ext
  simp only [coe_refl, coe_heckeDiagMatrix_smul hp, map_mul, Complex.conj_natCast, mul_neg]

private theorem refl_heckeMatrix_smul_of_le {p j : ℕ} (hp : p ≠ 0) (hjp : j ≤ p) (τ : ℍ) :
    refl (heckeMatrix p j • τ) = (-1 : ℝ) +ᵥ (heckeMatrix p (p - j) • refl τ) := by
  apply UpperHalfPlane.ext
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hs : ((p - j : ℕ) : ℂ) = (p : ℂ) - (j : ℂ) := Nat.cast_sub hjp
  simp only [coe_refl, coe_heckeMatrix_smul hp, UpperHalfPlane.coe_vadd, map_div₀, map_add,
    Complex.conj_natCast, Complex.ofReal_neg, Complex.ofReal_one, hs]
  field_simp
  ring

private theorem refl_heckeMatrix_smul_zero {p : ℕ} (hp : p ≠ 0) (τ : ℍ) :
    refl (heckeMatrix p 0 • τ) = heckeMatrix p 0 • refl τ := by
  apply UpperHalfPlane.ext
  simp only [coe_refl, coe_heckeMatrix_smul hp, Nat.cast_zero, add_zero, map_div₀,
    Complex.conj_natCast, neg_div]

private theorem neg_one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (-1 : ℝ) ∈ ((CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
      Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.neg_mem _ (AddSubgroup.mem_zmultiples _)

private theorem sum_apply_refl_heckeMatrix_smul {p : ℕ} (hp : p ≠ 0) (g : ℍ → ℂ)
    (hg : ∀ τ : ℍ, g ((-1 : ℝ) +ᵥ τ) = g τ) (τ : ℍ) :
    ∑ j ∈ Finset.range p, g (refl (heckeMatrix p j • τ))
      = ∑ j ∈ Finset.range p, g (heckeMatrix p j • refl τ) := by

  have hterm : ∀ j ∈ Finset.range p,
      g (refl (heckeMatrix p j • τ)) = g (heckeMatrix p ((p - j) % p) • refl τ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [refl_heckeMatrix_smul_zero hp, Nat.sub_zero, Nat.mod_self]
    · rw [refl_heckeMatrix_smul_of_le hp hj.le, hg, Nat.mod_eq_of_lt (by omega)]
  rw [Finset.sum_congr rfl hterm]
  have hmem : ∀ j ∈ Finset.range p, (p - j) % p ∈ Finset.range p := fun j _ =>
    Finset.mem_range.2 (Nat.mod_lt _ (Nat.pos_of_ne_zero hp))
  have hinv : ∀ j ∈ Finset.range p, (p - (p - j) % p) % p = j := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp
    · rw [Nat.mod_eq_of_lt (by omega : p - j < p), Nat.sub_sub_self hj.le, Nat.mod_eq_of_lt hj]
  exact Finset.sum_nbij' (fun j => (p - j) % p) (fun j => (p - j) % p) hmem hmem hinv hinv
    (fun j _ => rfl)

private theorem heckeU_reflectFun {p : ℕ} (hp : p ≠ 0) (k : ℤ) (g : ℍ → ℂ)
    (hg : ∀ τ : ℍ, g ((-1 : ℝ) +ᵥ τ) = g τ) :
    heckeU k p (reflectFun g) = reflectFun (heckeU k p g) := by
  funext τ
  have hsum : ∑ j ∈ Finset.range p, (starRingEnd ℂ) (g (refl (heckeMatrix p j • τ)))
      = ∑ j ∈ Finset.range p, (starRingEnd ℂ) (g (heckeMatrix p j • refl τ)) :=
    sum_apply_refl_heckeMatrix_smul hp (fun x => (starRingEnd ℂ) (g x)) (fun x => by simp only [hg]) τ
  rw [heckeU_apply k hp]
  simp only [reflectFun_apply]
  rw [heckeU_apply k hp]
  simp only [map_mul, map_inv₀, Complex.conj_natCast, map_sum, hsum]

private theorem heckeT_reflectFun {p : ℕ} (hp : p ≠ 0) (k : ℤ) (g : ℍ → ℂ)
    (hg : ∀ τ : ℍ, g ((-1 : ℝ) +ᵥ τ) = g τ) :
    heckeT k p (reflectFun g) = reflectFun (heckeT k p g) := by
  funext τ
  have hsum : ∑ j ∈ Finset.range p, (starRingEnd ℂ) (g (refl (heckeMatrix p j • τ)))
      = ∑ j ∈ Finset.range p, (starRingEnd ℂ) (g (heckeMatrix p j • refl τ)) :=
    sum_apply_refl_heckeMatrix_smul hp (fun x => (starRingEnd ℂ) (g x)) (fun x => by simp only [hg]) τ
  rw [heckeT_apply k hp]
  simp only [reflectFun_apply]
  rw [heckeT_apply k hp]
  simp only [map_add, map_mul, map_inv₀, map_zpow₀, Complex.conj_natCast, map_sum, hsum,
    refl_heckeDiagMatrix_smul hp]

private theorem coe_vadd_neg_one {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    f ((-1 : ℝ) +ᵥ τ) = f τ :=
  SlashInvariantForm.vAdd_apply_of_mem_strictPeriods f τ (neg_one_mem_strictPeriods_Gamma0 N)

private theorem coe_rho {N : ℕ} {k : ℤ} (ρ : CuspForm (CongruenceSubgroup.Gamma0 N) k → CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hρ : ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane),
      ρ f τ = (starRingEnd ℂ) (f ⟨-((starRingEnd ℂ) (τ : ℂ)), by simpa using τ.im_pos⟩))
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : ⇑(ρ f) = reflectFun ⇑f := by
  funext τ
  exact hρ f τ

private theorem comm_T {N : ℕ} {k : ℤ} (ρ : CuspForm (CongruenceSubgroup.Gamma0 N) k → CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hρ : ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane),
      ρ f τ = (starRingEnd ℂ) (f ⟨-((starRingEnd ℂ) (τ : ℂ)), by simpa using τ.im_pos⟩))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ρ (CuspForm.heckeTLin k hℓ hℓN f) = CuspForm.heckeTLin k hℓ hℓN (ρ f) := by
  refine DFunLike.coe_injective ?_
  show ⇑(ρ (CuspForm.heckeTLin k hℓ hℓN f)) = ⇑(CuspForm.heckeTLin k hℓ hℓN (ρ f))
  rw [coe_rho ρ hρ, CuspForm.coe_heckeTLin_apply, CuspForm.coe_heckeTLin_apply, coe_rho ρ hρ,
    heckeT_reflectFun hℓ.ne_zero k (⇑f) (coe_vadd_neg_one f)]

private theorem comm_U {N : ℕ} [NeZero N] {k : ℤ} (ρ : CuspForm (CongruenceSubgroup.Gamma0 N) k → CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hρ : ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane),
      ρ f τ = (starRingEnd ℂ) (f ⟨-((starRingEnd ℂ) (τ : ℂ)), by simpa using τ.im_pos⟩))
    {q : ℕ} (hqN : q ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ρ (CuspForm.heckeULin k hqN f) = CuspForm.heckeULin k hqN (ρ f) := by
  have hq : q ≠ 0 := ne_zero_of_dvd_ne_zero (NeZero.ne N) hqN
  refine DFunLike.coe_injective ?_
  show ⇑(ρ (CuspForm.heckeULin k hqN f)) = ⇑(CuspForm.heckeULin k hqN (ρ f))
  rw [coe_rho ρ hρ, CuspForm.coe_heckeULin_apply, CuspForm.coe_heckeULin_apply, coe_rho ρ hρ,
    heckeU_reflectFun hq k (⇑f) (coe_vadd_neg_one f)]

end ConjFormHecke

theorem solution (N : ℕ) [NeZero N] (k : ℤ)
    (ρ : CuspForm (CongruenceSubgroup.Gamma0 N) k → CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hρ : ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane),
      ρ f τ = (starRingEnd ℂ) (f ⟨-((starRingEnd ℂ) (τ : ℂ)), by simpa using τ.im_pos⟩)) :
    (∀ {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k),
        ρ (CuspForm.heckeTLin k hℓ hℓN f) = CuspForm.heckeTLin k hℓ hℓN (ρ f)) ∧
      (∀ {q : ℕ} (hqN : q ∣ N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k),
        ρ (CuspForm.heckeULin k hqN f) = CuspForm.heckeULin k hqN (ρ f))  :=
  ⟨fun hℓ hℓN f => ConjFormHecke.comm_T ρ hρ hℓ hℓN f, fun hqN f => ConjFormHecke.comm_U ρ hρ hqN f⟩

end

end S_CuspForm_conjForm_heckeTLin_heckeULin_comm
end P2MW
export P2MW.S_CuspForm_conjForm_heckeTLin_heckeULin_comm (solution)
