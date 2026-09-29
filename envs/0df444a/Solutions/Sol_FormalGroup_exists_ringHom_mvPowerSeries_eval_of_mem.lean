-- Prove2me | solution 1 for FormalGroup.exists_ringHom_mvPowerSeries_eval_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/1350dd00-bd88-5351-b52f-69ef9722dca2

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_PointTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_exists_ringHom_mvPowerSeries_eval_of_mem

set_option autoImplicit false

universe u

open FormalGroup

namespace AE2Aux

open scoped PowerSeries.WithPiTopology MvPowerSeries.WithPiTopology

attribute [local instance] DiscreteTopology.instContinuousSMul

section
variable {A R₀ S : Type*} [CommRing A] [UniformSpace A] [DiscreteUniformity A]
  [CommRing R₀] [UniformSpace R₀] [DiscreteUniformity R₀]
  [CommRing S] [UniformSpace S] [IsUniformAddGroup S] [IsTopologicalRing S] [IsLinearTopology S S] [T2Space S] [CompleteSpace S]

theorem eval₂_map {σ : Type*} (g : R₀ →+* S) (f : A →+* R₀) (a : σ → S) (ha : MvPowerSeries.HasEval a)
    (F : MvPowerSeries σ A) :
    MvPowerSeries.eval₂ g a (MvPowerSeries.map f F) = MvPowerSeries.eval₂ (g.comp f) a F := by
  have hg : Continuous g := continuous_of_discreteTopology
  have hgf : Continuous (g.comp f) := continuous_of_discreteTopology
  have h1 := MvPowerSeries.hasSum_eval₂ hg ha (MvPowerSeries.map f F)
  have h2 := MvPowerSeries.hasSum_eval₂ hgf ha F
  simp only [MvPowerSeries.coeff_map, RingHom.comp_apply] at h1 h2
  exact h1.unique h2

theorem eval₂_map₁ (g : R₀ →+* S) (f : A →+* R₀) (b : S) (hb : PowerSeries.HasEval b) (p : PowerSeries A) :
    PowerSeries.eval₂ g b (PowerSeries.map f p) = PowerSeries.eval₂ (g.comp f) b p := by
  have hg : Continuous g := continuous_of_discreteTopology
  have hgf : Continuous (g.comp f) := continuous_of_discreteTopology
  have h1 := PowerSeries.hasSum_eval₂ hg hb (PowerSeries.map f p)
  have h2 := PowerSeries.hasSum_eval₂ hgf hb p
  simp only [PowerSeries.coeff_map, RingHom.comp_apply] at h1 h2
  exact h1.unique h2

theorem eval₂_subst_X {σ : Type*} [Algebra A S] (a : σ → S) (ha : MvPowerSeries.HasEval a) (p : PowerSeries A) (i : σ) :
    MvPowerSeries.eval₂ (algebraMap A S) a (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ A) p) =
      PowerSeries.eval₂ (algebraMap A S) (a i) p := by
  have hX : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ A) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i)
  have e1 : MvPowerSeries.eval₂ (algebraMap A S) a (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries σ A) p) =
      ((MvPowerSeries.aeval ha).comp (PowerSeries.substAlgHom hX)) p := by
    rw [AlgHom.comp_apply, PowerSeries.coe_substAlgHom hX, MvPowerSeries.coe_aeval ha]
  rw [e1, PowerSeries.substAlgHom_eq_aeval hX, PowerSeries.comp_aeval _ (MvPowerSeries.continuous_aeval ha),
    PowerSeries.coe_aeval]
  congr 1
  show (MvPowerSeries.aeval ha) (MvPowerSeries.X i) = a i
  rw [MvPowerSeries.coe_aeval ha, MvPowerSeries.eval₂_X]

end

end AE2Aux

theorem solution
    {A T : Type u} [CommRing A] [CommRing T] (f : A →+* T) (I : Ideal T) [IsAdicComplete I T]
    (ζ₀ ζ₁ : T) (h₀ : ζ₀ ∈ I) (h₁ : ζ₁ ∈ I) :
    ∃ e : MvPowerSeries (Fin 2) A →+* T,
      (∀ a : A, e (MvPowerSeries.C a) = f a) ∧ e (MvPowerSeries.X 0) = ζ₀ ∧ e (MvPowerSeries.X 1) = ζ₁ ∧
      (∀ (F : FormalGroup A) (G : FormalGroup T), F.IsBaseChange f G →
        (letI : WithIdeal T := ⟨I⟩; G.eval ζ₀ ζ₁) = e F.toPowerSeries) ∧
      (∀ (p : PowerSeries A) (i : Fin 2),
        e (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) A) p) =
          (letI : WithIdeal T := ⟨I⟩; FormalGroup.evalSeries (PowerSeries.map f p) (if i = 0 then ζ₀ else ζ₁))) ∧
      (∀ (n : ℕ) (F : MvPowerSeries (Fin 2) A), (∀ d : Fin 2 →₀ ℕ, d 0 + d 1 < n → MvPowerSeries.coeff d F = 0) →
        e F ∈ I ^ n) := by
  classical
  letI wI : WithIdeal T := ⟨I⟩
  letI uA : UniformSpace A := ⊥
  haveI hdA : DiscreteUniformity A := ⟨rfl⟩
  have hI : IsAdic I := rfl
  obtain ⟨hcs, ht2⟩ := hI.isAdicComplete_iff.mp (inferInstance : IsAdicComplete I T)
  let a : Fin 2 → T := ![ζ₀, ζ₁]
  have hamem : ∀ s, a s ∈ I := fun s => by fin_cases s <;> simp [a, h₀, h₁]
  have ha : MvPowerSeries.HasEval a :=
    ⟨fun s => WithIdeal.isTopologicallyNilpotent_of_mem (hamem s), by
      rw [Filter.cofinite_eq_bot]; exact Filter.tendsto_bot⟩
  have hf : Continuous f := continuous_of_discreteTopology
  have hid : (algebraMap T T).comp f = f := RingHom.ext fun _ => rfl
  refine ⟨MvPowerSeries.eval₂Hom hf ha, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c; rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]
  · rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]; rfl
  · rw [MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]; rfl
  ·
    intro F G hbc
    rw [MvPowerSeries.coe_eval₂Hom]
    unfold FormalGroup.eval
    rw [show G.toPowerSeries = MvPowerSeries.map f F.toPowerSeries from hbc]
    have key := @AE2Aux.eval₂_map A T T _ uA hdA _ ⊥ inferInstance _ _ _ _ _ ht2 hcs (Fin 2)
      (algebraMap T T) f a ha F.toPowerSeries
    rw [hid] at key
    exact key
  ·
    intro p i
    rw [MvPowerSeries.coe_eval₂Hom]
    letI : Algebra A T := f.toAlgebra
    have hfa : algebraMap A T = f := rfl
    have h1 := @AE2Aux.eval₂_subst_X A T _ uA hdA _ _ _ _ _ ht2 hcs (Fin 2) _ a ha p i
    rw [hfa] at h1
    rw [h1]
    unfold FormalGroup.evalSeries
    have hb : PowerSeries.HasEval (if i = 0 then ζ₀ else ζ₁) :=
      (PowerSeries.hasEval_def _).mpr (WithIdeal.isTopologicallyNilpotent_of_mem (by split_ifs <;> assumption))
    have key := @AE2Aux.eval₂_map₁ A T T _ uA hdA _ ⊥ inferInstance _ _ _ _ _ ht2 hcs (algebraMap T T) f _ hb p
    rw [hid] at key
    rw [key]
    congr 1
    fin_cases i <;> rfl
  ·
    intro n F hF
    rw [MvPowerSeries.coe_eval₂Hom]
    have hsum := MvPowerSeries.hasSum_eval₂ hf ha F
    have hopen : IsOpen ((I ^ n : Ideal T) : Set T) := (isAdic_iff.mp hI).1 n
    have hcl : IsClosed ((I ^ n : Ideal T) : Set T) := AddSubgroup.isClosed_of_isOpen (I ^ n).toAddSubgroup hopen
    refine hcl.mem_of_tendsto hsum (Filter.Eventually.of_forall fun s => ?_)
    refine Ideal.sum_mem _ fun d _ => ?_
    by_cases hd : d 0 + d 1 < n
    · rw [hF d hd, map_zero, zero_mul]; exact Ideal.zero_mem _
    · push Not at hd
      refine Ideal.mul_mem_left _ _ ?_
      rw [Finsupp.prod_fintype _ _ (fun i => pow_zero (a i)), Fin.prod_univ_two]
      have hm : a 0 ^ d 0 * a 1 ^ d 1 ∈ I ^ (d 0 + d 1) := by
        rw [pow_add]; exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (hamem 0) _) (Ideal.pow_mem_pow (hamem 1) _)
      exact Ideal.pow_le_pow_right hd hm

end S_FormalGroup_exists_ringHom_mvPowerSeries_eval_of_mem
end P2MW
export P2MW.S_FormalGroup_exists_ringHom_mvPowerSeries_eval_of_mem (solution)
