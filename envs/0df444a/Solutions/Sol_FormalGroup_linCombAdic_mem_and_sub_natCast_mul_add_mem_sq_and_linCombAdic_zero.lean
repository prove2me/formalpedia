-- Prove2me | solution 1 for FormalGroup.linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/4981f6dd-50ce-5ccd-a3e9-c73f588c80a0

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero

set_option autoImplicit false

p2m_open "IsLocalRing FormalGroup P2MW.S_FormalGroup_linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero.FormalGroup"

namespace FormalGroup
p2m_export "FormalGroup" "zero_constantCoeff lin_coeff_Y lin_coeff_X toPowerSeries eval evalNSMul evalNSMul_zero evalNSMul_succ linCombAdic IsDrinfeldBasisAdic"
namespace LinApproxAux
p2m_open "FormalGroup"

open MvPowerSeries Filter Topology

section Values

variable {R₀ : Type*} [CommRing R₀] [UniformSpace R₀] [DiscreteUniformity R₀]
  {A : Type*} [CommRing A] [Algebra R₀ A] (I : Ideal A) [IsAdicComplete I A]

theorem hasEval_of_mem {σ : Type*} [Finite σ] (a : σ → A) (ha : ∀ s, a s ∈ I) :
    letI : WithIdeal A := ⟨I⟩; MvPowerSeries.HasEval a := by
  letI : WithIdeal A := ⟨I⟩
  refine ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (ha s), ?_⟩
  rw [Filter.cofinite_eq_bot]; exact tendsto_bot

theorem eval₂_mem {σ : Type*} [Finite σ] (a : σ → A) (ha : ∀ s, a s ∈ I) (f : MvPowerSeries σ R₀)
    (hf : algebraMap R₀ A (MvPowerSeries.constantCoeff f) ∈ I) :
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) a f) ∈ I := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hφ : Continuous (algebraMap R₀ A) := continuous_of_discreteTopology
  have hsum := MvPowerSeries.hasSum_eval₂ hφ (hasEval_of_mem I a ha) f
  have hopen : IsOpen ((Submodule.toAddSubgroup I : AddSubgroup A) : Set A) := by
    apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    rw [(I.hasBasis_nhds_zero_adic).mem_iff]
    exact ⟨1, trivial, by simp⟩
  have hclosed : IsClosed (I : Set A) := AddSubgroup.isClosed_of_isOpen _ hopen
  refine hclosed.mem_of_tendsto hsum (Filter.Eventually.of_forall fun s => ?_)
  refine I.sum_mem fun d _ => ?_
  by_cases hd : d = 0
  · subst hd; simpa using hf
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
    have hi' : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    refine I.mul_mem_left _ ?_
    rw [Finsupp.prod]
    exact I.prod_mem hi (I.pow_mem_of_mem (ha i) _ (Nat.pos_of_ne_zero hi'))

theorem eval₂_sub_add_mem_sq (F : FormalGroup R₀) (x y : A) (hx : x ∈ I) (hy : y ∈ I) :
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) ![x, y] F.toPowerSeries) - (x + y) ∈ I ^ 2 := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hφ : Continuous (algebraMap R₀ A) := continuous_of_discreteTopology
  have ha : ∀ s, (![x, y] : Fin 2 → A) s ∈ I := fun s => by fin_cases s <;> simp [hx, hy]
  have hsum := MvPowerSeries.hasSum_eval₂ hφ (hasEval_of_mem I (![x, y] : Fin 2 → A) ha) F.toPowerSeries
  have hopen : IsOpen ((Submodule.toAddSubgroup (I ^ 2) : AddSubgroup A) : Set A) := by
    apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    rw [(I.hasBasis_nhds_zero_adic).mem_iff]
    exact ⟨2, trivial, by simp⟩
  have hclosed : IsClosed ((I ^ 2 : Ideal A) : Set A) := AddSubgroup.isClosed_of_isOpen _ hopen
  have hclosed' : IsClosed {z : A | z - (x + y) ∈ I ^ 2} :=
    hclosed.preimage (continuous_id.sub continuous_const)
  refine hclosed'.mem_of_tendsto hsum (Filter.eventually_atTop.mpr ⟨{Finsupp.single 0 1, Finsupp.single 1 1}, ?_⟩)
  intro s hs
  have h01 : (Finsupp.single (0 : Fin 2) 1) ≠ Finsupp.single 1 1 := by
    intro h; have := congrArg (fun e => e 0) h; simp at this
  have hmem0 : Finsupp.single (0 : Fin 2) 1 ∈ s := hs (by simp)
  have hmem1 : Finsupp.single (1 : Fin 2) 1 ∈ s := hs (by simp)
  show (∑ d ∈ s, _) - (x + y) ∈ I ^ 2
  rw [← Finset.add_sum_erase s _ hmem0, ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨h01.symm, hmem1⟩)]
  have hprod : ∀ d : Fin 2 →₀ ℕ, (d.prod fun s e => (![x, y] : Fin 2 → A) s ^ e) = x ^ (d 0) * y ^ (d 1) := by
    intro d; rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]; rfl
  have t0 : algebraMap R₀ A (MvPowerSeries.coeff (Finsupp.single (0 : Fin 2) 1) F.toPowerSeries) *
      ((Finsupp.single (0 : Fin 2) 1).prod fun s e => (![x, y] : Fin 2 → A) s ^ e) = x := by
    rw [F.lin_coeff_X, map_one, one_mul, hprod]; simp
  have t1 : algebraMap R₀ A (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1) F.toPowerSeries) *
      ((Finsupp.single (1 : Fin 2) 1).prod fun s e => (![x, y] : Fin 2 → A) s ^ e) = y := by
    rw [F.lin_coeff_Y, map_one, one_mul, hprod]; simp
  rw [t0, t1, show ∀ S : A, x + (y + S) - (x + y) = S from fun S => by ring]
  refine Ideal.sum_mem _ fun d hd => ?_
  rw [Finset.mem_erase, Finset.mem_erase] at hd
  obtain ⟨hd1, hd0, -⟩ := hd
  by_cases hz : d = 0
  · subst hz; rw [MvPowerSeries.coeff_zero_eq_constantCoeff, F.zero_constantCoeff, map_zero, zero_mul]; exact Submodule.zero_mem _
  refine Ideal.mul_mem_left _ _ ?_
  rw [hprod]
  have hdeg : 2 ≤ d 0 + d 1 := by
    by_contra hlt
    push_neg at hlt
    have h0 : d 0 ≤ 1 := by omega
    have h1 : d 1 ≤ 1 := by omega
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h0 with e0 | e0 <;>
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with e1 | e1
    · exact hz (by ext i; fin_cases i <;> simp [e0, e1])
    · exact hd1 (by ext i; fin_cases i <;> simp [e0, e1])
    · exact hd0 (by ext i; fin_cases i <;> simp [e0, e1])
    · omega
  have hxy : x ^ d 0 * y ^ d 1 ∈ I ^ (d 0 + d 1) := by
    rw [pow_add]; exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hx _) (Ideal.pow_mem_pow hy _)
  exact Ideal.pow_le_pow_right hdeg hxy

theorem eval₂_zero_zero (F : FormalGroup R₀) :
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) ![(0 : A), 0] F.toPowerSeries) = 0 := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hφ : Continuous (algebraMap R₀ A) := continuous_of_discreteTopology
  have ha : ∀ s, (![(0 : A), 0] : Fin 2 → A) s ∈ I := fun s => by fin_cases s <;> simp
  have hsum := MvPowerSeries.hasSum_eval₂ hφ (hasEval_of_mem I (![(0 : A), 0] : Fin 2 → A) ha) F.toPowerSeries
  have hzero : (fun d : Fin 2 →₀ ℕ => algebraMap R₀ A (MvPowerSeries.coeff d F.toPowerSeries) *
      d.prod (fun s e => (![(0 : A), 0] : Fin 2 → A) s ^ e)) = fun _ => 0 := by
    funext d
    by_cases hd : d = 0
    · subst hd
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff, F.zero_constantCoeff, map_zero, zero_mul]
    · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
      have hi' : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
      have : d.prod (fun s e => (![(0 : A), 0] : Fin 2 → A) s ^ e) = 0 := by
        rw [Finsupp.prod]
        refine Finset.prod_eq_zero hi ?_
        have : (![(0 : A), 0] : Fin 2 → A) i = 0 := by fin_cases i <;> simp
        rw [this, zero_pow hi']
      rw [this, mul_zero]
  rw [hzero] at hsum
  exact (hasSum_zero.unique hsum).symm

end Values

end FormalGroup.LinApproxAux

open FormalGroup.LinApproxAux in
theorem solution
    (R : Type) [CommRing R] (I : Ideal R) [IsAdicComplete I R] (F : FormalGroup R)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (a b : ℕ) :
    F.linCombAdic I x₀ x₁ a b ∈ I ∧
      F.linCombAdic I x₀ x₁ a b - ((a : R) * x₀ + (b : R) * x₁) ∈ I ^ 2 ∧
      F.linCombAdic I x₀ x₁ 0 0 = 0 := by
  classical
  letI inst : WithIdeal R := ⟨I⟩

  have hmem : ∀ x y : R, x ∈ I → y ∈ I → F.eval x y ∈ I := by
    intro x y hx hy
    unfold FormalGroup.eval
    exact @eval₂_mem R _ ⊥ inferInstance R _ _ I _ (Fin 2) _ ![x, y]
      (fun s => by fin_cases s <;> simp [hx, hy]) F.toPowerSeries
      (by rw [F.zero_constantCoeff, map_zero]; exact Submodule.zero_mem _)
  have hlin : ∀ x y : R, x ∈ I → y ∈ I → F.eval x y - (x + y) ∈ I ^ 2 := by
    intro x y hx hy
    unfold FormalGroup.eval
    exact @eval₂_sub_add_mem_sq R _ ⊥ inferInstance R _ _ I _ F x y hx hy
  have h00 : F.eval (0 : R) (0 : R) = 0 := by
    unfold FormalGroup.eval
    exact @eval₂_zero_zero R _ ⊥ inferInstance R _ _ I _ F

  have hns : ∀ (x : R), x ∈ I → ∀ n : ℕ, F.evalNSMul n x ∈ I ∧ F.evalNSMul n x - (n : R) * x ∈ I ^ 2 := by
    intro x hx n
    induction n with
    | zero => exact ⟨by simp, by simp⟩
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      rw [FormalGroup.evalNSMul_succ]
      refine ⟨hmem _ _ ih1 hx, ?_⟩
      have e : F.eval (F.evalNSMul n x) x - ((n + 1 : ℕ) : R) * x =
          (F.eval (F.evalNSMul n x) x - (F.evalNSMul n x + x)) + (F.evalNSMul n x - (n : R) * x) := by
        push_cast; ring
      rw [e]
      exact Ideal.add_mem _ (hlin _ _ ih1 hx) ih2

  have eℓ : F.linCombAdic I x₀ x₁ a b = F.eval (F.evalNSMul a x₀) (F.evalNSMul b x₁) := rfl
  have e00 : F.linCombAdic I x₀ x₁ 0 0 = F.eval (F.evalNSMul 0 x₀) (F.evalNSMul 0 x₁) := rfl
  obtain ⟨ha1, ha2⟩ := hns x₀ hx₀ a
  obtain ⟨hb1, hb2⟩ := hns x₁ hx₁ b
  refine ⟨?_, ?_, ?_⟩
  · rw [eℓ]; exact hmem _ _ ha1 hb1
  · rw [eℓ]
    have e : F.eval (F.evalNSMul a x₀) (F.evalNSMul b x₁) - ((a : R) * x₀ + (b : R) * x₁) =
        (F.eval (F.evalNSMul a x₀) (F.evalNSMul b x₁) - (F.evalNSMul a x₀ + F.evalNSMul b x₁)) +
        (F.evalNSMul a x₀ - (a : R) * x₀) + (F.evalNSMul b x₁ - (b : R) * x₁) := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.add_mem _ (hlin _ _ ha1 hb1) ha2) hb2
  · rw [e00, FormalGroup.evalNSMul_zero, FormalGroup.evalNSMul_zero]; exact h00

end S_FormalGroup_linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero
end P2MW
export P2MW.S_FormalGroup_linCombAdic_mem_and_sub_natCast_mul_add_mem_sq_and_linCombAdic_zero (solution)
