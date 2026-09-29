-- Prove2me | solution 1 for FormalGroup.IsDrinfeldBasisAdic.map_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/a3db05b2-7eea-54c5-baf7-08dd485a1e0b

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport
import Theorems.Thm_FormalGroup_IsBaseChange_nthSeries_eq_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_IsDrinfeldBasisAdic_map_of_isBaseChange

set_option autoImplicit false

open FormalGroup IsLocalRing

namespace QuotIsoAux

open MvPowerSeries Filter Topology

theorem eval₂_mem {R : Type*} [CommRing R] [UniformSpace R] [DiscreteUniformity R]
    {A : Type*} [CommRing A] [Algebra R A] (I : Ideal A) [IsAdicComplete I A]
    {σ : Type*} [Finite σ] (a : σ → A) (ha : ∀ s, a s ∈ I) (f : MvPowerSeries σ R)
    (hf : algebraMap R A (MvPowerSeries.constantCoeff f) ∈ I) :
    (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R A) a f) ∈ I := by
  letI : WithIdeal A := ⟨I⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  have hφ : Continuous (algebraMap R A) := continuous_of_discreteTopology
  have hev : MvPowerSeries.HasEval a := by
    refine ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (ha s), ?_⟩
    rw [Filter.cofinite_eq_bot]; exact tendsto_bot
  have hsum := MvPowerSeries.hasSum_eval₂ hφ hev f

  have hopen : IsOpen ((Submodule.toAddSubgroup I : AddSubgroup A) : Set A) := by
    apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    rw [(I.hasBasis_nhds_zero_adic).mem_iff]
    exact ⟨1, trivial, by simp⟩
  have hclosed : IsClosed (I : Set A) := AddSubgroup.isClosed_of_isOpen _ hopen
  refine hclosed.mem_of_tendsto hsum (Filter.Eventually.of_forall fun s => ?_)
  refine I.sum_mem fun d _ => ?_
  by_cases hd : d = 0
  · subst hd
    simpa using hf
  · obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd
    have hi' : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
    refine I.mul_mem_left _ ?_
    rw [Finsupp.prod]
    exact I.prod_mem hi (I.pow_mem_of_mem (ha i) _ (Nat.pos_of_ne_zero hi'))

end QuotIsoAux

namespace QuotIsoAux

theorem eval_mem {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T)
    (x y : T) (hx : x ∈ I) (hy : y ∈ I) :
    (letI : WithIdeal T := ⟨I⟩; F.eval x y) ∈ I := by
  have h := @eval₂_mem T _ ⊥ inferInstance T _ _ I _ (Fin 2) _ ![x, y]
    (fun s => by fin_cases s <;> simp [hx, hy]) F.toPowerSeries
    (by rw [F.zero_constantCoeff, map_zero]; exact I.zero_mem)
  unfold FormalGroup.eval
  exact h

theorem evalNSMul_mem {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T)
    (n : ℕ) (x : T) (hx : x ∈ I) :
    (letI : WithIdeal T := ⟨I⟩; F.evalNSMul n x) ∈ I := by
  letI : WithIdeal T := ⟨I⟩
  induction n with
  | zero => rw [FormalGroup.evalNSMul_zero]; exact I.zero_mem
  | succ n ih => rw [FormalGroup.evalNSMul_succ]; exact eval_mem I F _ _ ih hx

theorem linCombAdic_mem {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T)
    (x₀ x₁ : T) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (a b : ℕ) :
    F.linCombAdic I x₀ x₁ a b ∈ I := by
  unfold FormalGroup.linCombAdic FormalGroup.linComb
  exact eval_mem I F _ _ (evalNSMul_mem I F a x₀ hx₀) (evalNSMul_mem I F b x₁ hx₁)

theorem coeff_one_mul_X {T : Type*} [CommRing T] (p : PowerSeries T) :
    PowerSeries.coeff 1 (p * PowerSeries.X) = PowerSeries.coeff 0 p := by
  simpa using PowerSeries.coeff_succ_mul_X 0 p

theorem coeff_mul_prod_mem {T : Type*} [CommRing T] (I : Ideal T) {ι : Type*} (s : Finset ι) (c : ι → T)
    (hc : ∀ i ∈ s, c i ∈ I) (u : PowerSeries T) :
    PowerSeries.coeff 0 (u * ∏ i ∈ s, (PowerSeries.X - PowerSeries.C (c i))) ∈ I ^ s.card ∧
    PowerSeries.coeff 1 (u * ∏ i ∈ s, (PowerSeries.X - PowerSeries.C (c i))) ∈ I ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
    have hci : c i ∈ I := hc i (Finset.mem_insert_self i s)
    have hcs : ∀ j ∈ s, c j ∈ I := fun j hj => hc j (Finset.mem_insert_of_mem hj)
    obtain ⟨h0, h1⟩ := ih hcs
    rw [Finset.prod_insert his, Finset.card_insert_of_notMem his]
    have hrw : u * ((PowerSeries.X - PowerSeries.C (c i)) * ∏ j ∈ s, (PowerSeries.X - PowerSeries.C (c j)))
        = (u * ∏ j ∈ s, (PowerSeries.X - PowerSeries.C (c j))) * PowerSeries.X
          - (u * ∏ j ∈ s, (PowerSeries.X - PowerSeries.C (c j))) * PowerSeries.C (c i) := by ring
    rw [hrw]
    constructor
    · rw [map_sub, PowerSeries.coeff_zero_mul_X, PowerSeries.coeff_mul_C, zero_sub, pow_succ]
      exact Submodule.neg_mem _ (Ideal.mul_mem_mul h0 hci)
    · rw [map_sub, coeff_one_mul_X, PowerSeries.coeff_mul_C, Nat.add_sub_cancel]
      refine (I ^ s.card).sub_mem ?_ ?_
      · exact h0
      · have hmul : PowerSeries.coeff 1 (u * ∏ j ∈ s, (PowerSeries.X - PowerSeries.C (c j))) * c i
            ∈ I ^ (s.card - 1) * I := Ideal.mul_mem_mul h1 hci
        have hle : I ^ (s.card - 1) * I ≤ I ^ s.card := by
          rw [← pow_succ]; exact Ideal.pow_le_pow_right (by omega)
        exact hle hmul

end QuotIsoAux

namespace QuotIsoAux

open MvPowerSeries Filter Topology

theorem map_eval₂ {R₀ : Type*} [CommRing R₀] [UniformSpace R₀] [DiscreteUniformity R₀]
    {S₀ : Type*} [CommRing S₀] [UniformSpace S₀] [DiscreteUniformity S₀]
    {A B : Type*} [CommRing A] [CommRing B] [Algebra R₀ A] [Algebra S₀ B]
    (I : Ideal A) (J : Ideal B) [IsAdicComplete I A] [IsAdicComplete J B]
    (g : R₀ →+* S₀) (ε : A →+* B) (hcomm : ∀ r, ε (algebraMap R₀ A r) = algebraMap S₀ B (g r))
    (hε : ∀ x ∈ I, ε x ∈ J) {σ : Type*} [Finite σ] (a : σ → A) (ha : ∀ s, a s ∈ I)
    (F : MvPowerSeries σ R₀) :
    ε (letI : WithIdeal A := ⟨I⟩; MvPowerSeries.eval₂ (algebraMap R₀ A) a F) =
      (letI : WithIdeal B := ⟨J⟩; MvPowerSeries.eval₂ (algebraMap S₀ B) (ε ∘ a) (MvPowerSeries.map g F)) := by
  letI iA : WithIdeal A := ⟨I⟩
  letI iB : WithIdeal B := ⟨J⟩
  have hI : IsAdic I := rfl
  have hJ : IsAdic J := rfl
  obtain ⟨hcA, htA⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I A)
  obtain ⟨hcB, htB⟩ := hJ.isAdicComplete_iff.mp (inferInstance : IsAdicComplete J B)
  have hφA : Continuous (algebraMap R₀ A) := continuous_of_discreteTopology
  have hφB : Continuous (algebraMap S₀ B) := continuous_of_discreteTopology
  have hevA : MvPowerSeries.HasEval a := by
    refine ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (ha s), ?_⟩
    rw [Filter.cofinite_eq_bot]; exact tendsto_bot
  have hevB : MvPowerSeries.HasEval (ε ∘ a) := by
    refine ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (hε _ (ha s)), ?_⟩
    rw [Filter.cofinite_eq_bot]; exact tendsto_bot
  have hεc : Continuous ε := by
    refine (WithIdeal.uniformContinuous_of_map_le (f := ε) ?_).continuous
    change I.map ε ≤ J
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact hε x hx
  have h1 := (MvPowerSeries.hasSum_eval₂ hφA hevA F).map (ε : A →+ B) hεc
  have h2 := MvPowerSeries.hasSum_eval₂ hφB hevB (MvPowerSeries.map g F)
  refine HasSum.unique h1 ?_
  convert h2 using 2 with d
  simp only [Function.comp_apply, AddMonoidHom.coe_coe, map_mul, hcomm,
    MvPowerSeries.coeff_map, map_finsuppProd, map_pow]

end QuotIsoAux

namespace QuotIsoAux

theorem map_eval {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    [IsAdicComplete I R] [IsAdicComplete J S] (f : R →+* S) (hf : ∀ r ∈ I, f r ∈ J)
    (F : FormalGroup R) (G : FormalGroup S) (h : F.IsBaseChange f G)
    (x y : R) (hx : x ∈ I) (hy : y ∈ I) :
    f (letI : WithIdeal R := ⟨I⟩; F.eval x y) = (letI : WithIdeal S := ⟨J⟩; G.eval (f x) (f y)) := by
  have k := @map_eval₂ R _ ⊥ inferInstance S _ ⊥ inferInstance R S _ _ _ _ I J _ _ f f
    (fun r => rfl) hf (Fin 2) _ ![x, y] (fun s => by fin_cases s <;> simp [hx, hy]) F.toPowerSeries
  have hv : (f ∘ ![x, y] : Fin 2 → S) = ![f x, f y] := by
    funext s; fin_cases s <;> rfl
  unfold FormalGroup.eval
  unfold FormalGroup.IsBaseChange at h
  rw [h, ← hv]
  exact k

theorem map_evalNSMul {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    [IsAdicComplete I R] [IsAdicComplete J S] (f : R →+* S) (hf : ∀ r ∈ I, f r ∈ J)
    (F : FormalGroup R) (G : FormalGroup S) (h : F.IsBaseChange f G)
    (n : ℕ) (x : R) (hx : x ∈ I) :
    f (letI : WithIdeal R := ⟨I⟩; F.evalNSMul n x) = (letI : WithIdeal S := ⟨J⟩; G.evalNSMul n (f x)) := by
  induction n with
  | zero =>
    letI : WithIdeal R := ⟨I⟩
    have h0 : F.evalNSMul 0 x = 0 := FormalGroup.evalNSMul_zero F x
    rw [h0, map_zero]
    letI : WithIdeal S := ⟨J⟩
    exact (FormalGroup.evalNSMul_zero G (f x)).symm
  | succ n ih =>
    have hR : (letI : WithIdeal R := ⟨I⟩; F.evalNSMul (n + 1) x) =
        (letI : WithIdeal R := ⟨I⟩; F.eval (F.evalNSMul n x) x) := rfl
    have hS : (letI : WithIdeal S := ⟨J⟩; G.evalNSMul (n + 1) (f x)) =
        (letI : WithIdeal S := ⟨J⟩; G.eval (G.evalNSMul n (f x)) (f x)) := rfl
    rw [hR, hS, map_eval I J f hf F G h _ _ (evalNSMul_mem I F n x hx) hx, ih]

theorem map_linCombAdic {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S)
    [IsAdicComplete I R] [IsAdicComplete J S] (f : R →+* S) (hf : ∀ r ∈ I, f r ∈ J)
    (F : FormalGroup R) (G : FormalGroup S) (h : F.IsBaseChange f G)
    (x₀ x₁ : R) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (a b : ℕ) :
    f (F.linCombAdic I x₀ x₁ a b) = G.linCombAdic J (f x₀) (f x₁) a b := by
  unfold FormalGroup.linCombAdic FormalGroup.linComb
  rw [map_eval I J f hf F G h _ _ (evalNSMul_mem I F a x₀ hx₀) (evalNSMul_mem I F b x₁ hx₁),
    map_evalNSMul I J f hf F G h a x₀ hx₀, map_evalNSMul I J f hf F G h b x₁ hx₁]

end QuotIsoAux

theorem solution
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) [IsAdicComplete I R] [IsAdicComplete J S]
    (f : R →+* S) (hf : ∀ r ∈ I, f r ∈ J) (F : FormalGroup R) (G : FormalGroup S) (h : F.IsBaseChange f G)
    (q : ℕ) (x₀ x₁ : R) (hx₀ : x₀ ∈ I) (hx₁ : x₁ ∈ I) (hD : F.IsDrinfeldBasisAdic I q x₀ x₁) :
    G.IsDrinfeldBasisAdic J q (f x₀) (f x₁) := by
  classical
  obtain ⟨u, hu, hqu⟩ := (FormalGroup.isDrinfeldBasisAdic_iff F I q x₀ x₁).mp hD
  rw [FormalGroup.isDrinfeldBasisAdic_iff]
  refine ⟨PowerSeries.map f u, hu.map _, ?_⟩
  rw [FormalGroup.IsBaseChange.nthSeries_eq_map F f G h q, hqu, map_mul]
  congr 1
  show PowerSeries.map f (∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q,
      (PowerSeries.X - PowerSeries.C (F.linCombAdic I x₀ x₁ a b))) =
    ∏ a ∈ Finset.range q, ∏ b ∈ Finset.range q,
      (PowerSeries.X - PowerSeries.C (G.linCombAdic J (f x₀) (f x₁) a b))
  simp only [map_prod, map_sub, PowerSeries.map_X, PowerSeries.map_C]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => ?_
  rw [QuotIsoAux.map_linCombAdic I J f hf F G h x₀ x₁ hx₀ hx₁ a b]

end S_FormalGroup_IsDrinfeldBasisAdic_map_of_isBaseChange
end P2MW
export P2MW.S_FormalGroup_IsDrinfeldBasisAdic_map_of_isBaseChange (solution)
