-- Prove2me | solution 1 for CuspForm.exists_qCoeff_eq_ite_dvd_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/18b0baba-befa-58b5-a059-ffaf5a480be3

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_qCoeff_eq_ite_dvd_of_prime

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups

namespace B6bProof

open ModularForm UpperHalfPlane Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup
open scoped Pointwise

noncomputable def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ) (f : CuspForm Γ k) :
    CuspForm Γ' k where
  toFun := f
  slash_action_eq' A hA := SlashInvariantForm.slash_action_eqn f A (h hA)
  holo' := f.holo'
  zero_at_cusps' hc := f.zero_at_cusps' (hc.mono h)

@[scoped simp] theorem coe_restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (h : Γ' ≤ Γ) (f : CuspForm Γ k) :
    ⇑(restrict h f) = ⇑f := rfl

theorem exists_conj_eq (N p : ℕ) (hp : 0 < p) (j : ℤ) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma1 (p ^ 2 * N)) :
    ∃ γ' : SL(2, ℤ), γ' ∈ Gamma1 N ∧
      upperRightHom ((j : ℝ) / p) * (mapGL ℝ γ : GL (Fin 2) ℝ) =
        (mapGL ℝ γ' : GL (Fin 2) ℝ) * upperRightHom ((j : ℝ) / p) := by
  obtain ⟨ha, hd, hc⟩ := (Gamma1_mem _ _).mp hγ

  have hM : ((p ^ 2 * N : ℕ) : ℤ) = (p : ℤ) ^ 2 * N := by push_cast; ring
  obtain ⟨c₃, hc₃⟩ : ∃ c₃ : ℤ, γ 1 0 = (p : ℤ) ^ 2 * N * c₃ := by
    obtain ⟨c₃, h⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hc
    exact ⟨c₃, by rw [h, hM]⟩
  obtain ⟨a₃, ha₃⟩ : ∃ a₃ : ℤ, γ 0 0 = 1 + (p : ℤ) ^ 2 * N * a₃ := by
    have h1 : ((γ 0 0 - 1 : ℤ) : ZMod (p ^ 2 * N)) = 0 := by rw [Int.cast_sub, ha, Int.cast_one, sub_self]
    obtain ⟨a₃, h⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1
    exact ⟨a₃, by rw [hM] at h; linear_combination h⟩
  obtain ⟨d₃, hd₃⟩ : ∃ d₃ : ℤ, γ 1 1 = 1 + (p : ℤ) ^ 2 * N * d₃ := by
    have h1 : ((γ 1 1 - 1 : ℤ) : ZMod (p ^ 2 * N)) = 0 := by rw [Int.cast_sub, hd, Int.cast_one, sub_self]
    obtain ⟨d₃, h⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h1
    exact ⟨d₃, by rw [hM] at h; linear_combination h⟩
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = (p : ℤ) * N * (d₃ - a₃) := ⟨_, rfl⟩
  have hde : γ 1 1 - γ 0 0 = p * e := by rw [ha₃, hd₃, he]; ring
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    exact this

  obtain ⟨a', ha'⟩ : ∃ a' : ℤ, a' = γ 0 0 + j * p * N * c₃ := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b' : ℤ, b' = γ 0 1 + j * e - j ^ 2 * N * c₃ := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c' : ℤ, c' = γ 1 0 := ⟨_, rfl⟩
  obtain ⟨d', hd'⟩ : ∃ d' : ℤ, d' = γ 1 1 - j * p * N * c₃ := ⟨_, rfl⟩
  have hdet' : Matrix.det !![a', b'; c', d'] = 1 := by
    rw [Matrix.det_fin_two_of]
    rw [ha', hb', hc', hd']
    linear_combination hdet + (j ^ 2 * N * c₃ - j * e) * hc₃ + (j * p * N * c₃) * hde
  refine ⟨⟨!![a', b'; c', d'], hdet'⟩, ?_, ?_⟩
  ·
    rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · show ((a' : ℤ) : ZMod N) = 1
      rw [ha', ha₃]
      push_cast
      simp
    · show ((d' : ℤ) : ZMod N) = 1
      rw [hd', hd₃]
      push_cast
      simp
    · show ((c' : ℤ) : ZMod N) = 0
      rw [hc', hc₃]
      push_cast
      simp
  ·
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    have hcR : ((γ 1 0 : ℤ) : ℝ) = (p : ℝ) ^ 2 * N * c₃ := by exact_mod_cast hc₃
    have hdeR : ((γ 1 1 : ℤ) : ℝ) - ((γ 0 0 : ℤ) : ℝ) = p * e := by exact_mod_cast hde
    subst ha' hb' hc' hd'
    ext i j'
    fin_cases i <;> fin_cases j' <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, upperRightHom_apply] <;>
      (try field_simp) <;>
      first
        | linear_combination (j : ℝ) * hcR
        | linear_combination (-(j : ℝ)) * hcR
        | linear_combination (j : ℝ) * hdeR

theorem gamma1_le_conj (N p : ℕ) (hp : 0 < p) (j : ℤ) :
    ((Gamma1 (p ^ 2 * N) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (upperRightHom ((j : ℝ) / p))⁻¹ • ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  intro x hx
  obtain ⟨γ, hγ, rfl⟩ := Subgroup.mem_map.mp hx
  rw [map_inv, Subgroup.mem_inv_pointwise_smul_iff, ConjAct.toConjAct_smul]
  obtain ⟨γ', hγ', heq⟩ := exists_conj_eq N p hp j γ hγ
  rw [heq, mul_inv_cancel_right]
  exact Subgroup.mem_map_of_mem _ hγ'

theorem gamma1_le (N p : ℕ) (hp : 0 < p) :
    ((Gamma1 (p ^ 2 * N) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  have := gamma1_le_conj N p hp 0
  simpa using this

theorem gamma1_le_conj' (N p : ℕ) (hp : 0 < p) (j : ℕ) :
    ((Gamma1 (p ^ 2 * N) : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (upperRightHom ((j : ℝ) / p))⁻¹ • ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) := by
  simpa using gamma1_le_conj N p hp j

theorem upperRightHom_smul (t : ℝ) (τ : ℍ) : upperRightHom t • τ = t +ᵥ τ := by
  ext
  simp [σ, num, denom, coe_vadd, UpperHalfPlane.coe_smul, add_comm]

theorem slash_upperRightHom_apply (f : ℍ → ℂ) (k : ℤ) (t : ℝ) (τ : ℍ) :
    (f ∣[k] upperRightHom t) τ = f (t +ᵥ τ) := by
  rw [ModularForm.slash_apply, upperRightHom_smul]
  simp [σ, denom, Matrix.GeneralLinearGroup.val_det_apply]

section Construction

variable (N : ℕ) (k : ℤ) (f : CuspForm (Gamma1 N) k) (p : ℕ) (hp : 0 < p)

noncomputable def translateRestrict (j : ℕ) : CuspForm (Gamma1 (p ^ 2 * N)) k :=
  restrict (gamma1_le_conj' N p hp j) (CuspForm.translate f (upperRightHom ((j : ℝ) / p)))

theorem translateRestrict_apply (j : ℕ) (τ : ℍ) :
    translateRestrict N k f p hp j τ = f (((j : ℝ) / p) +ᵥ τ) := by
  rw [translateRestrict, coe_restrict]
  show (⇑f ∣[k] upperRightHom ((j : ℝ) / p)) τ = _
  exact slash_upperRightHom_apply f k _ τ

noncomputable def depletion : CuspForm (Gamma1 (p ^ 2 * N)) k :=
  restrict (gamma1_le N p hp) f - (p : ℂ)⁻¹ • ∑ j ∈ Finset.range p, translateRestrict N k f p hp j

theorem depletion_apply (τ : ℍ) :
    depletion N k f p hp τ = f τ - (p : ℂ)⁻¹ * ∑ j ∈ Finset.range p, f (((j : ℝ) / p) +ᵥ τ) := by
  rw [depletion, CuspForm.sub_apply, CuspForm.IsGLPos.smul_apply, coe_restrict, smul_eq_mul]
  congr 2
  have : ⇑(∑ j ∈ Finset.range p, translateRestrict N k f p hp j) =
      ∑ j ∈ Finset.range p, ⇑(translateRestrict N k f p hp j) :=
    map_sum (FunLike.coeAddMonoidHom (CuspForm (Gamma1 (p ^ 2 * N)) k) ℍ ℂ) _ _
  rw [this, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ => translateRestrict_apply N k f p hp j τ

end Construction

section QExp

variable (N : ℕ) (k : ℤ) (f : CuspForm (Gamma1 N) k) (p : ℕ) (hp : p.Prime)

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp [ModularGroup.coe_T]

theorem one_mem_strictPeriods (M : ℕ) :
    (1 : ℝ) ∈ (((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem (T_mem_Gamma1 M)]
  exact AddSubgroup.mem_zmultiples 1

theorem hasSum_f (τ : ℍ) :
    HasSum (fun m : ℕ => (qExpansion 1 f).coeff m • Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  haveI : Fact (IsCusp OnePoint.infty (((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods N)⟩
  exact UpperHalfPlane.hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods N))
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ

noncomputable def ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / p)

theorem qParam_vadd (j : ℕ) (τ : ℍ) : Function.Periodic.qParam 1 ((((j : ℝ) / p : ℝ)) +ᵥ τ) = ζ p ^ j * Function.Periodic.qParam 1 τ := by
  simp only [Function.Periodic.qParam, coe_vadd, Complex.ofReal_one, div_one, ζ]
  rw [mul_add, Complex.exp_add, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

include hp in
theorem geom_sum_ζ (m : ℕ) :
    ∑ j ∈ Finset.range p, (ζ p ^ m) ^ j = if p ∣ m then (p : ℂ) else 0 := by
  have hζ : IsPrimitiveRoot (ζ p) p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).mpr h]
    simp
  · exact (hζ.pow_of_coprime m (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr h))).geom_sum_eq_zero
      hp.one_lt

include hp in

theorem hasSum_depletion (τ : ℍ) :
    HasSum (fun m : ℕ => (if p ∣ m then 0 else (qExpansion 1 f).coeff m) • Function.Periodic.qParam 1 τ ^ m)
      (depletion N k f p hp.pos τ) := by
  have hf := hasSum_f N k f
  have hsum : HasSum (fun m : ℕ => ∑ j ∈ Finset.range p, (qExpansion 1 f).coeff m • (ζ p ^ j * Function.Periodic.qParam 1 τ) ^ m)
      (∑ j ∈ Finset.range p, f ((((j : ℝ) / p : ℝ)) +ᵥ τ)) := by
    refine hasSum_sum fun j _ => ?_
    have := hf ((((j : ℝ) / p : ℝ)) +ᵥ τ)
    rwa [qParam_vadd] at this
  have htot := (hf τ).sub (hsum.mul_left ((p : ℂ)⁻¹))
  rw [← depletion_apply N k f p hp.pos τ] at htot
  convert htot using 1
  · rfl
  funext m
  simp only [smul_eq_mul]
  have hre : ∑ j ∈ Finset.range p, (qExpansion 1 f).coeff m * (ζ p ^ j * Function.Periodic.qParam 1 τ) ^ m =
      (qExpansion 1 f).coeff m * Function.Periodic.qParam 1 τ ^ m * ∑ j ∈ Finset.range p, (ζ p ^ m) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm j m]
    ring
  rw [hre, geom_sum_ζ p hp]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  split_ifs with h
  · field_simp
    ring
  · ring

include hp in
theorem qExpansion_depletion_coeff (m : ℕ) :
    (qExpansion 1 (depletion N k f p hp.pos)).coeff m = if p ∣ m then 0 else (qExpansion 1 f).coeff m :=
  (ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods (p ^ 2 * N))
    (f := depletion N k f p hp.pos) (hasSum_depletion N k f p hp) m).symm

end QExp

end B6bProof
p2m_reactivate "P2MW.S_CuspForm_exists_qCoeff_eq_ite_dvd_of_prime.B6bProof"

theorem solution
    (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k) (p : ℕ) (hp : p.Prime) :
    ∃ g : CuspForm (Gamma1 (p ^ 2 * N)) k,
      ∀ n : ℕ, ModularFormClass.qCoeff g n = if p ∣ n then 0 else ModularFormClass.qCoeff f n := by
  refine ⟨B6bProof.depletion N k f p hp.pos, fun n => ?_⟩
  simp only [ModularFormClass.qCoeff]
  exact B6bProof.qExpansion_depletion_coeff N k f p hp n

end S_CuspForm_exists_qCoeff_eq_ite_dvd_of_prime
end P2MW
export P2MW.S_CuspForm_exists_qCoeff_eq_ite_dvd_of_prime (solution)
