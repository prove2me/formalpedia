-- Prove2me | solution 1 for BrauerInduction.exists_trace_eq_sum_zsmul_induced_linearCharacter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fcf3cd5f-c18e-54f2-a77e-1e94e1fc6e44

import Mathlib
import Definitions.Def_ClassFunction_Induced
import Theorems.Thm_ClassFunction_exists_one_eq_sum_zsmul_induced_one_of_hyperelementary
import Theorems.Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false

noncomputable section

open scoped Classical
open scoped MatrixGroups

namespace BrauerProof

variable {G : Type} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ)

def chi : G → ℂ := fun g => ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace

theorem chi_conj (x g : G) : chi ρ (x⁻¹ * g * x) = chi ρ g := by
  simp only [chi, map_mul, Units.val_mul]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul,
    mul_inv_cancel, one_mul]

private def _root_.BrauerProof.ext (L : Subgroup G) (ψ : L →* ℂˣ) : G → ℂ :=
  fun x => if hx : x ∈ L then ((ψ ⟨x, hx⟩ : ℂˣ) : ℂ) else 0

p2m_export "BrauerProof" "ext"

theorem induced_ext_apply (L : Subgroup G) (ψ : L →* ℂˣ) (g : G) :
    ClassFunction.induced L (ext L ψ) g =
      (Nat.card L : ℂ)⁻¹ *
        ∑ x : G, if hx : x⁻¹ * g * x ∈ L then (((ψ ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ)) else 0 := by
  rw [ClassFunction.induced_apply]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x⁻¹ * g * x ∈ L
  · rw [if_pos hx, dif_pos hx, ext]
    beta_reduce
    rw [dif_pos hx]
  · rw [if_neg hx, dif_neg hx]

theorem solomon_complex :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (a : Fin k → ℤ),
      (∀ i, ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H i ∧ IsCyclic C ∧ (Nat.card C).Coprime q ∧
        (∀ h ∈ H i, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H i, ∃ m : ℕ, h ^ q ^ m ∈ C)) ∧
      ∀ g : G, (1 : ℂ) = ∑ i, (a i : ℂ) * ClassFunction.induced (H i) (fun _ => (1 : ℂ)) g := by
  obtain ⟨k, H, a, hH, h1⟩ :=
    ClassFunction.exists_one_eq_sum_zsmul_induced_one_of_hyperelementary (G := G)
  refine ⟨k, H, a, hH, fun g => ?_⟩
  have hcast : ∀ i, ((ClassFunction.induced (H i) (fun _ => (1 : ℚ)) g : ℚ) : ℂ) =
      ClassFunction.induced (H i) (fun _ => (1 : ℂ)) g := by
    intro i
    rw [ClassFunction.induced_apply, ClassFunction.induced_apply]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  have := congrArg (fun r : ℚ => (r : ℂ)) (h1 g)
  simp only [Rat.cast_one, Rat.cast_sum, Rat.cast_mul, Rat.cast_intCast, hcast] at this
  exact this

theorem induced_chi_hyper (H : Subgroup G)
    (hH : ∃ q : ℕ, q.Prime ∧ ∃ C : Subgroup G, C ≤ H ∧ IsCyclic C ∧ (Nat.card C).Coprime q ∧
      (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H, ∃ m : ℕ, h ^ q ^ m ∈ C)) :
    ∃ (k : ℕ) (L : Fin k → Subgroup G) (ψ : (j : Fin k) → (L j →* ℂˣ)),
      ∀ g : G, ClassFunction.induced H (chi ρ) g =
        ∑ j, ClassFunction.induced (L j) (ext (L j) (ψ j)) g := by
  obtain ⟨q, hq, C, hCH, hCcyc, -, hCnorm, hCpow⟩ := hH

  let A : Subgroup H := C.subgroupOf H
  have hAn : A.Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using hCnorm h h.2 a ha
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    haveI := hCcyc
    obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := C)
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hg₀ ⟨b, hb⟩)
    have hc : (⟨a, ha⟩ : C) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      rw [← hi, ← hj]; exact zpow_mul_comm g₀ i j
    have hc' := congrArg Subtype.val hc
    simp only [Subgroup.coe_mul] at hc'
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hc')
  have hApow : ∀ h : H, ∃ m : ℕ, h ^ q ^ m ∈ A := by
    intro h
    obtain ⟨m, hm⟩ := hCpow h h.2
    exact ⟨m, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact hm⟩
  obtain ⟨k, L, ψ, hL⟩ :=
    ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem
      hq A hAn hAcomm hApow (ρ.comp H.subtype)

  set extH : (j : Fin k) → (H → ℂ) := fun j x =>
    if hx : x ∈ L j then (((ψ j) ⟨x, hx⟩ : ℂˣ) : ℂ) else 0 with hextH

  let L' : Fin k → Subgroup G := fun j => (L j).map H.subtype
  let ψ' : (j : Fin k) → (L' j →* ℂˣ) := fun j =>
    (ψ j).comp ((L j).equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom
  refine ⟨k, L', ψ', fun g => ?_⟩

  have step1 : ClassFunction.induced H (chi ρ) =
      ClassFunction.induced H (fun x => ∑ j, (fun y : G =>
        if hy : y ∈ H then ClassFunction.induced (L j) (extH j) ⟨y, hy⟩ else 0) x) := by
    apply ClassFunction.induced_congr
    intro y hy
    have := hL ⟨y, hy⟩
    simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at this
    rw [chi]
    beta_reduce
    rw [this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dif_pos hy]
  rw [step1, ClassFunction.induced_sum]
  refine Finset.sum_congr rfl fun j _ => ?_

  rw [ClassFunction.induced_induced H (L j) (extH j)]
  apply congrFun (ClassFunction.induced_congr _ ?_) g
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hy
  simp only [Subgroup.coe_subtype]
  rw [dif_pos z.2]
  have hz' : (⟨(z : G), z.2⟩ : H) ∈ L j := by simpa using hz
  have hmem : (z : G) ∈ L' j := ⟨z, hz, rfl⟩
  simp only [hextH, ext, dif_pos hz', dif_pos hmem]
  change _ = (((ψ j) (((L j).equivMapOfInjective H.subtype H.subtype_injective).symm
    ⟨(z : G), hmem⟩) : ℂˣ) : ℂ)
  congr 2
  apply ((L j).equivMapOfInjective H.subtype H.subtype_injective).injective
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  rfl

theorem main : ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
    ∀ g : G, chi ρ g = ∑ i, (a i : ℂ) * ClassFunction.induced (H i) (ext (H i) (ψ i)) g := by

  obtain ⟨k, H, a, hH, h1⟩ := solomon_complex (G := G)
  have h2 : ∀ g : G, chi ρ g = ∑ i, (a i : ℂ) * ClassFunction.induced (H i) (chi ρ) g := by
    intro g
    have := congrArg (fun t => t * chi ρ g) (h1 g)
    simp only [one_mul, Finset.sum_mul, mul_assoc] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ClassFunction.induced_mul_of_conj_invariant (H i) _ _ (chi_conj ρ) g]
    simp only [one_mul]

  have h3 := fun i => induced_chi_hyper ρ (H i) (hH i)
  choose kf Lf ψf hf using h3

  let ι := Σ i : Fin k, Fin (kf i)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun m => Lf (e.symm m).1 (e.symm m).2,
    fun m => ψf (e.symm m).1 (e.symm m).2, fun m => a (e.symm m).1, fun g => ?_⟩
  rw [h2 g]
  simp_rw [hf]
  rw [← Fintype.sum_equiv e (fun s : ι => (a s.1 : ℂ) *
      ClassFunction.induced (Lf s.1 s.2) (ext (Lf s.1 s.2) (ψf s.1 s.2)) g) _
      (fun s => by rw [Equiv.symm_apply_apply])]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

end BrauerProof

theorem solution
    {G : Type} [Group G] [Fintype G] {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)) (a : Fin k → ℤ),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, (a i : ℂ) * ((Nat.card (H i) : ℂ)⁻¹ *
          ∑ x : G, if hx : x⁻¹ * g * x ∈ H i then (((ψ i) ⟨x⁻¹ * g * x, hx⟩ : ℂˣ) : ℂ) else 0) := by
  obtain ⟨k, H, ψ, a, h⟩ := BrauerProof.main ρ
  refine ⟨k, H, ψ, a, fun g => ?_⟩
  have := h g
  rw [BrauerProof.chi] at this
  rw [this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [BrauerProof.induced_ext_apply]

end

end S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter
end P2MW
export P2MW.S_BrauerInduction_exists_trace_eq_sum_zsmul_induced_linearCharacter (solution)
