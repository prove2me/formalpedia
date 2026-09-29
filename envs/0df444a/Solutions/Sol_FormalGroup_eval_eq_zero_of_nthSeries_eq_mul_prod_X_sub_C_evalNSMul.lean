-- Prove2me | solution 1 for FormalGroup.eval_eq_zero_of_nthSeries_eq_mul_prod_X_sub_C_evalNSMul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/69d79d4c-04af-58b3-a51b-39a0d5aac3ff

import Mathlib
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_FormalGroup_eval_eq_zero_of_nthSeries_eq_mul_prod_X_sub_C_evalNSMul

set_option autoImplicit false

open PowerSeries Polynomial

namespace R4IgusaNec

theorem exists_isUnit_eq_mul_iff_eq_of_isWeierstrassFactorization
    {B : Type*} [CommRing B] [IsLocalRing B] [IsHausdorff (IsLocalRing.maximalIdeal B) B]
    {g : B⟦X⟧} {P : B[X]} {u : B⟦X⟧} (hfac : g.IsWeierstrassFactorization P u)
    (D : B[X]) (hD : D.Monic) (hdeg : D.natDegree = P.natDegree) :
    (∃ w : B⟦X⟧, IsUnit w ∧ g = w * (D : B⟦X⟧)) ↔ D = P := by
  constructor
  · rintro ⟨w, hw, hgw⟩

    have hred : (PowerSeries.X : (IsLocalRing.ResidueField B)⟦X⟧) ^ P.natDegree *
          PowerSeries.map (IsLocalRing.residue B) u =
        PowerSeries.map (IsLocalRing.residue B) w * ((D.map (IsLocalRing.residue B) : (IsLocalRing.ResidueField B)[X]) :
          (IsLocalRing.ResidueField B)⟦X⟧) := by
      have e := congrArg (PowerSeries.map (IsLocalRing.residue B)) (hfac.eq_mul.symm.trans hgw)
      rw [map_mul, map_mul, ← Polynomial.polynomial_map_coe, ← Polynomial.polynomial_map_coe] at e
      have hP : P.map (IsLocalRing.residue B) = Polynomial.X ^ P.natDegree :=
        hfac.isDistinguishedAt.map_eq_X_pow
      rw [hP, Polynomial.coe_pow, Polynomial.coe_X] at e
      exact e

    have hwu : IsUnit (PowerSeries.map (IsLocalRing.residue B) w) := hw.map _
    obtain ⟨wi, hwi⟩ := hwu.exists_left_inv
    have hDbar : ((D.map (IsLocalRing.residue B) : (IsLocalRing.ResidueField B)[X]) : (IsLocalRing.ResidueField B)⟦X⟧) =
        (PowerSeries.X : (IsLocalRing.ResidueField B)⟦X⟧) ^ P.natDegree * (PowerSeries.map (IsLocalRing.residue B) u * wi) := by
      calc ((D.map (IsLocalRing.residue B) : (IsLocalRing.ResidueField B)[X]) : (IsLocalRing.ResidueField B)⟦X⟧)
          = wi * (PowerSeries.map (IsLocalRing.residue B) w *
              ((D.map (IsLocalRing.residue B) : (IsLocalRing.ResidueField B)[X]) : (IsLocalRing.ResidueField B)⟦X⟧)) := by
            rw [← mul_assoc, hwi, one_mul]
        _ = (PowerSeries.X : (IsLocalRing.ResidueField B)⟦X⟧) ^ P.natDegree *
              (PowerSeries.map (IsLocalRing.residue B) u * wi) := by
            rw [← hred]; ring
    have hdist : D.IsDistinguishedAt (IsLocalRing.maximalIdeal B) := by
      refine ⟨⟨fun {i} hi => ?_⟩, hD⟩
      rw [← IsLocalRing.residue_eq_zero_iff]
      have hc := congrArg (PowerSeries.coeff i) hDbar
      rw [Polynomial.coeff_coe, Polynomial.coeff_map, PowerSeries.coeff_X_pow_mul', if_neg (by omega)] at hc
      exact hc
    have hfac' : g.IsWeierstrassFactorization D w := ⟨hdist, hw, by rw [hgw, mul_comm]⟩
    exact (hfac'.elim hfac).1
  · rintro rfl
    exact ⟨u, hfac.isUnit, by rw [hfac.eq_mul, mul_comm]⟩

section SubstInv

variable {R : Type*} [CommRing R]

theorem subst_X_self (f : R⟦X⟧) : f.subst PowerSeries.X = f := by
  ext n
  rw [PowerSeries.coeff_subst' PowerSeries.HasSubst.X', finsum_eq_single _ n]
  · rw [PowerSeries.coeff_X_pow, if_pos rfl, smul_eq_mul, mul_one]
  · intro d hd
    rw [PowerSeries.coeff_X_pow, if_neg (Ne.symm hd), smul_zero]

theorem subst_inner_injective (P : R⟦X⟧) (hP : P.constantCoeff = 0) [Invertible (PowerSeries.coeff 1 P)]
    {F F' : R⟦X⟧} (h : F.subst P = F'.subst P) : F = F' := by
  have hPs : PowerSeries.HasSubst P := PowerSeries.HasSubst.of_constantCoeff_zero' hP
  have key : ∀ S : R⟦X⟧, PowerSeries.subst P.substInv (PowerSeries.subst P S) = S := by
    intro S
    rw [PowerSeries.subst_comp_subst_apply hPs (PowerSeries.HasSubst.substInv P) S,
      PowerSeries.subst_substInv_right P hP, subst_X_self]
  rw [← key F, ← key F', h]

theorem subst_zero' {τ : Type*} {a : MvPowerSeries τ R} (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a (0 : PowerSeries R) = 0 := by
  have h := map_zero (PowerSeries.substAlgHom (R := R) ha)
  rwa [PowerSeries.coe_substAlgHom] at h

theorem eq_X_of_subst_self_eq_self {f : PowerSeries R}
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f = 1)
    (hidem : f.subst f = f) : f = PowerSeries.X := by
  haveI : Invertible (PowerSeries.coeff 1 f) := by
    rw [hf1]; exact invertibleOne
  have hfP : PowerSeries.HasSubst f := PowerSeries.HasSubst.of_constantCoeff_zero' hf0
  exact subst_inner_injective f hf0 (hidem.trans (PowerSeries.subst_X hfP).symm)

end SubstInv

section MvHelpers

theorem subst_zero_of_constantCoeff_zero {σ τ S : Type*} [CommRing S]
    {f : MvPowerSeries σ S} (hf : MvPowerSeries.constantCoeff f = 0) :
    MvPowerSeries.subst (fun _ : σ => (0 : MvPowerSeries τ S)) f = 0 := by
  classical
  ext e
  rw [MvPowerSeries.coeff_subst MvPowerSeries.HasSubst.zero, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  rcases eq_or_ne d 0 with rfl | hd
  · simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
      by_contra! hc
      exact hd (Finsupp.ext hc)
    have hzero : (d.prod fun _ n => (0 : MvPowerSeries τ S) ^ n) = 0 := by
      apply Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      exact zero_pow hi
    simp only [hzero, map_zero, smul_zero]

theorem subst_subst_X_X {υ τ R : Type*} [CommRing R] {b : υ → MvPowerSeries τ R}
    (hb : MvPowerSeries.HasSubst b) (i j : υ) (f : MvPowerSeries (Fin 2) R) :
    MvPowerSeries.subst b
        (MvPowerSeries.subst
          (![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries υ R) f)
      = MvPowerSeries.subst (![b i, b j] : Fin 2 → MvPowerSeries τ R) f := by
  rw [MvPowerSeries.subst_comp_subst_apply MvPowerSeries.HasSubst.X_X hb]
  have hfam : (fun s => MvPowerSeries.subst b
      ((![MvPowerSeries.X i, MvPowerSeries.X j] : Fin 2 → MvPowerSeries υ R) s))
      = (![b i, b j] : Fin 2 → MvPowerSeries τ R) := by
    funext s
    fin_cases s
    · show MvPowerSeries.subst b (MvPowerSeries.X i : MvPowerSeries υ R) = b i
      exact MvPowerSeries.subst_X hb i
    · show MvPowerSeries.subst b (MvPowerSeries.X j : MvPowerSeries υ R) = b j
      exact MvPowerSeries.subst_X hb j
  rw [hfam]

theorem powerSeries_subst_subst_pair {R : Type*} [CommRing R] {A B g : PowerSeries R}
    (hAB : MvPowerSeries.HasSubst (![A, B] : Fin 2 → PowerSeries R))
    (hg : MvPowerSeries.HasSubst (fun _ : Unit => g)) (f : MvPowerSeries (Fin 2) R) :
    PowerSeries.subst g (MvPowerSeries.subst ![A, B] f)
      = MvPowerSeries.subst ![PowerSeries.subst g A, PowerSeries.subst g B] f := by
  rw [PowerSeries.subst_def, MvPowerSeries.subst_comp_subst_apply hAB hg]
  have hfam : (fun s => MvPowerSeries.subst (fun _ : Unit => g)
      ((![A, B] : Fin 2 → PowerSeries R) s))
      = ![PowerSeries.subst g A, PowerSeries.subst g B] := by
    funext s
    fin_cases s
    · rfl
    · rfl
  rw [hfam]

end MvHelpers

section Normalisation

variable {R : Type*} [CommRing R]

theorem hasSubst_zero_X :
    MvPowerSeries.HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
  fin_cases s
  · have h : MvPowerSeries.constantCoeff (0 : PowerSeries R) = 0 := map_zero _
    simp only [Matrix.cons_val_zero] at h ⊢
    exact h
  · have h__af := MvPowerSeries.constantCoeff_X (R := R) ()
    simp only [Matrix.cons_val_one, Matrix.head_cons] at h__af ⊢
    exact h__af

theorem subst_zero_zero (F : FormalGroup R) :
    MvPowerSeries.subst (![0, 0] : Fin 2 → PowerSeries R) F.toPowerSeries = 0 := by
  have h : (![0, 0] : Fin 2 → PowerSeries R) = fun _ => 0 := by
    funext s
    fin_cases s <;> rfl
  rw [h]
  exact subst_zero_of_constantCoeff_zero F.zero_constantCoeff

theorem subst_assoc (F : FormalGroup R) (c₀ c₁ c₂ : PowerSeries R)
    (h₀ : MvPowerSeries.constantCoeff c₀ = 0) (h₁ : MvPowerSeries.constantCoeff c₁ = 0)
    (h₂ : MvPowerSeries.constantCoeff c₂ = 0) :
    MvPowerSeries.subst ![MvPowerSeries.subst ![c₀, c₁] F.toPowerSeries, c₂] F.toPowerSeries
      = MvPowerSeries.subst ![c₀, MvPowerSeries.subst ![c₁, c₂] F.toPowerSeries]
          F.toPowerSeries := by
  classical
  have hc : MvPowerSeries.HasSubst (![c₀, c₁, c₂] : Fin 3 → PowerSeries R) := by
    refine MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => ?_
    fin_cases s
    · simp only [Matrix.cons_val_zero] at h₀ ⊢
      exact h₀
    · simp only [Matrix.cons_val_one, Matrix.head_cons] at h₁ ⊢
      exact h₁
    · simpa using h₂
  have ha₁ : MvPowerSeries.HasSubst
      (![(F.toPowerSeries).subst ![MvPowerSeries.X 0, MvPowerSeries.X 1], MvPowerSeries.X 2] :
        Fin 2 → MvPowerSeries (Fin 3) R) :=
    MvPowerSeries.HasSubst.cons_subst_zero_left (0 : Fin 3) 1 2 F.zero_constantCoeff
  have ha₂ : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 0, (F.toPowerSeries).subst ![MvPowerSeries.X 1, MvPowerSeries.X 2]] :
        Fin 2 → MvPowerSeries (Fin 3) R) :=
    MvPowerSeries.HasSubst.cons_subst_zero_right (0 : Fin 3) 1 2 F.zero_constantCoeff
  have key := congrArg
    (MvPowerSeries.subst (![c₀, c₁, c₂] : Fin 3 → PowerSeries R)) F.assoc
  rw [MvPowerSeries.subst_comp_subst_apply ha₁ hc,
    MvPowerSeries.subst_comp_subst_apply ha₂ hc] at key
  have hfam₁ : (fun s => MvPowerSeries.subst (![c₀, c₁, c₂] : Fin 3 → PowerSeries R)
      ((![(F.toPowerSeries).subst ![MvPowerSeries.X 0, MvPowerSeries.X 1], MvPowerSeries.X 2] :
        Fin 2 → MvPowerSeries (Fin 3) R) s))
      = ![MvPowerSeries.subst ![c₀, c₁] F.toPowerSeries, c₂] := by
    funext s
    fin_cases s
    · show MvPowerSeries.subst (![c₀, c₁, c₂] : Fin 3 → PowerSeries R)
          (MvPowerSeries.subst
            (![MvPowerSeries.X 0, MvPowerSeries.X 1] : Fin 2 → MvPowerSeries (Fin 3) R)
            F.toPowerSeries)
        = MvPowerSeries.subst (![c₀, c₁] : Fin 2 → PowerSeries R) F.toPowerSeries
      rw [subst_subst_X_X hc 0 1]
      rfl
    · show MvPowerSeries.subst (![c₀, c₁, c₂] : Fin 3 → PowerSeries R)
          (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) R) = c₂
      rw [MvPowerSeries.subst_X hc]
      rfl
  have hfam₂ : (fun s => MvPowerSeries.subst (![c₀, c₁, c₂] : Fin 3 → PowerSeries R)
      ((![MvPowerSeries.X 0, (F.toPowerSeries).subst ![MvPowerSeries.X 1, MvPowerSeries.X 2]] :
        Fin 2 → MvPowerSeries (Fin 3) R) s))
      = ![c₀, MvPowerSeries.subst ![c₁, c₂] F.toPowerSeries] := by
    funext s
    fin_cases s
    · show MvPowerSeries.subst (![c₀, c₁, c₂] : Fin 3 → PowerSeries R)
          (MvPowerSeries.X 0 : MvPowerSeries (Fin 3) R) = c₀
      rw [MvPowerSeries.subst_X hc]
      rfl
    · show MvPowerSeries.subst (![c₀, c₁, c₂] : Fin 3 → PowerSeries R)
          (MvPowerSeries.subst
            (![MvPowerSeries.X 1, MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) R)
            F.toPowerSeries)
        = MvPowerSeries.subst (![c₁, c₂] : Fin 2 → PowerSeries R) F.toPowerSeries
      rw [subst_subst_X_X hc 1 2]
      rfl
  rw [hfam₁, hfam₂] at key
  exact key

theorem nthSeries_one_eq_subst_zero_X (F : FormalGroup R) :
    F.nthSeries 1
      = MvPowerSeries.subst (![0, PowerSeries.X] : Fin 2 → PowerSeries R)
          F.toPowerSeries := by
  have h := F.nthSeries_succ 0
  rw [FormalGroup.nthSeries_zero, Nat.zero_add] at h
  exact h

theorem constantCoeff_subst_zero_X (F : FormalGroup R) :
    PowerSeries.constantCoeff
      (MvPowerSeries.subst (![0, PowerSeries.X] : Fin 2 → PowerSeries R)
        F.toPowerSeries) = 0 := by
  rw [← nthSeries_one_eq_subst_zero_X]
  exact F.constantCoeff_nthSeries 1

theorem coeff_one_subst_zero_X (F : FormalGroup R) :
    PowerSeries.coeff 1
      (MvPowerSeries.subst (![0, PowerSeries.X] : Fin 2 → PowerSeries R)
        F.toPowerSeries) = 1 := by
  classical
  have ha : MvPowerSeries.HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) := hasSubst_zero_X
  have hcoeff_eq : (PowerSeries.coeff (R := R) 1) = MvPowerSeries.coeff (Finsupp.single () 1) :=
    PowerSeries.coeff_def Finsupp.single_eq_same
  have hprod : ∀ d : Fin 2 →₀ ℕ,
      (d.prod fun s n => ((![0, PowerSeries.X] : Fin 2 → PowerSeries R) s) ^ n)
        = (0 : PowerSeries R) ^ (d 0) * PowerSeries.X ^ (d 1) := by
    intro d
    rw [Finsupp.prod_pow, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hcoeff_eq, MvPowerSeries.coeff_subst ha, finsum_eq_single _ (Finsupp.single (1 : Fin 2) 1)]
  · rw [hprod, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1), pow_one, pow_zero, one_mul,
      F.lin_coeff_Y, one_smul, ← hcoeff_eq, PowerSeries.coeff_one_X]
  · intro d hd
    rw [hprod]
    rcases eq_or_ne (d 0) 0 with h0 | h0
    · have hd1 : d 1 ≠ 1 := by
        intro h1
        apply hd
        refine Finsupp.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
        · rw [h0, Finsupp.single_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]
        · rw [h1, Finsupp.single_eq_same]
      rw [h0, pow_zero, one_mul, ← hcoeff_eq, PowerSeries.coeff_X_pow,
        if_neg (fun h => hd1 h.symm), smul_zero]
    · rw [zero_pow h0, zero_mul, map_zero, smul_zero]

theorem subst_zero_X (F : FormalGroup R) :
    MvPowerSeries.subst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) F.toPowerSeries
      = PowerSeries.X := by
  classical
  have hg0 := constantCoeff_subst_zero_X F
  have hg1 := coeff_one_subst_zero_X F
  have hgP := PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  have hgU : MvPowerSeries.HasSubst
      (fun _ : Unit =>
        MvPowerSeries.subst (![0, PowerSeries.X] : Fin 2 → PowerSeries R) F.toPowerSeries) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => hg0
  refine eq_X_of_subst_self_eq_self hg0 hg1 ?_
  rw [powerSeries_subst_subst_pair hasSubst_zero_X hgU,
    subst_zero' hgP, PowerSeries.subst_X hgP]
  have h := subst_assoc F 0 0 PowerSeries.X
    (map_zero _) (map_zero _) (MvPowerSeries.constantCoeff_X ())
  rw [subst_zero_zero F] at h
  exact h.symm

theorem nthSeries_one (F : FormalGroup R) : F.nthSeries 1 = PowerSeries.X := by
  rw [nthSeries_one_eq_subst_zero_X, subst_zero_X]

end Normalisation

section EvalOne

variable {T : Type*} [CommRing T] (I : Ideal T) [IsAdicComplete I T] (F : FormalGroup T)

theorem evalNSMul_one_of_mem_radical {x : T} (hx : x ∈ I.radical) :
    (letI : WithIdeal T := ⟨I⟩; F.evalNSMul 1 x) = x := by
  letI : WithIdeal T := ⟨I⟩
  show F.eval (F.evalNSMul 0 x) x = x
  rw [FormalGroup.evalNSMul_zero]
  change MvFormalGroup.adicEval (R := T) I (![(0 : T), x] : Fin 2 → T) F.toPowerSeries = x
  have hxr : ∀ s : Unit, (fun _ : Unit => x) s ∈ I.radical := fun _ => hx
  have key := congrArg (MvFormalGroup.adicEval (R := T) I (fun _ : Unit => x)) (subst_zero_X F)
  rw [MvFormalGroup.adicEval_subst (R := T) I hxr hasSubst_zero_X] at key
  have hfam : (fun t : Fin 2 => MvFormalGroup.adicEval (R := T) I (fun _ : Unit => x)
      ((![0, PowerSeries.X] : Fin 2 → PowerSeries T) t)) = ![(0 : T), x] := by
    funext t
    fin_cases t
    · show MvFormalGroup.adicEval (R := T) I (fun _ : Unit => x) (0 : MvPowerSeries Unit T) = 0
      rw [← MvPolynomial.coe_zero, MvFormalGroup.adicEval_coe, map_zero]
    · show MvFormalGroup.adicEval (R := T) I (fun _ : Unit => x) (MvPowerSeries.X () : MvPowerSeries Unit T) = x
      exact MvFormalGroup.adicEval_X (R := T) I (fun _ : Unit => x) ()
  rw [hfam] at key
  rw [key]
  exact MvFormalGroup.adicEval_X (R := T) I (fun _ : Unit => x) ()

end EvalOne

section Poly

variable {T : Type*} [CommRing T]

theorem X_isDistinguishedAt (I : Ideal T) : (Polynomial.X : T[X]).IsDistinguishedAt I := by
  refine ⟨⟨fun {i} hi => ?_⟩, Polynomial.monic_X⟩
  have hi' : i < 1 := lt_of_lt_of_le hi Polynomial.natDegree_X_le
  obtain rfl : i = 0 := by omega
  rw [Polynomial.coeff_X_zero]
  exact Submodule.zero_mem _

theorem X_mul_cancel {a b : T[X]} (h : Polynomial.X * a = Polynomial.X * b) : a = b := by
  ext n
  have := congrArg (fun p : T[X] => p.coeff (n + 1)) h
  simpa only [Polynomial.coeff_X_mul] using this

theorem coe_prod_X_sub_C (s : Finset ℕ) (c : ℕ → T) :
    ((∏ a ∈ s, (Polynomial.X - Polynomial.C (c a)) : T[X]) : T⟦X⟧) =
      ∏ a ∈ s, (PowerSeries.X - PowerSeries.C (c a)) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [map_sub, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coe_X, Polynomial.coe_C]

theorem monic_prod_X_sub_C (s : Finset ℕ) (c : ℕ → T) :
    (∏ a ∈ s, (Polynomial.X - Polynomial.C (c a)) : T[X]).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun _ _ => Polynomial.monic_X_sub_C _

theorem natDegree_prod_X_sub_C [Nontrivial T] (s : Finset ℕ) (c : ℕ → T) :
    (∏ a ∈ s, (Polynomial.X - Polynomial.C (c a)) : T[X]).natDegree = s.card := by
  rw [Polynomial.natDegree_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C _]
  simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]

end Poly

end R4IgusaNec

open IsLocalRing Polynomial in

theorem solution
    (T : Type*) [CommRing T] [IsLocalRing T] [IsNoetherianRing T] [IsAdicComplete (maximalIdeal T) T]
    (F : FormalGroup T) (q : ℕ) [Fact q.Prime]
    (g : T[X]) (hmonic : g.Monic) (hdeg : g.natDegree = q - 1)
    (hdist : ∀ i < q - 1, g.coeff i ∈ maximalIdeal T)
    (v : PowerSeries T) (hv : IsUnit v)
    (hF : F.nthSeries q = PowerSeries.X * (↑g : PowerSeries T) * v)
    (x : T) (hx : x ∈ maximalIdeal T)
    (hgen : ∃ u : PowerSeries T, IsUnit u ∧
        F.nthSeries q = u * ∏ a ∈ Finset.range q,
          (PowerSeries.X - PowerSeries.C (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.evalNSMul a x))) :
    g.eval x = 0 := by
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le

  set c : ℕ → T := fun a => (letI : WithIdeal T := ⟨maximalIdeal T⟩; F.evalNSMul a x) with hc
  have hc0 : c 0 = 0 := rfl
  have hc1 : c 1 = x :=
    R4IgusaNec.evalNSMul_one_of_mem_radical (maximalIdeal T) F (Ideal.le_radical hx)

  set P : T[X] := ∏ a ∈ Finset.range q, (Polynomial.X - Polynomial.C (c a)) with hP
  have hPcoe : (P : T⟦X⟧) = ∏ a ∈ Finset.range q, (PowerSeries.X - PowerSeries.C (c a)) :=
    R4IgusaNec.coe_prod_X_sub_C _ c
  have hPmonic : P.Monic := R4IgusaNec.monic_prod_X_sub_C _ c
  have hPdeg : P.natDegree = q := by
    rw [hP, R4IgusaNec.natDegree_prod_X_sub_C, Finset.card_range]

  have hgdist : g.IsDistinguishedAt (maximalIdeal T) :=
    ⟨⟨fun {i} hi => hdist i (by rwa [hdeg] at hi)⟩, hmonic⟩
  have hXg_dist : (Polynomial.X * g).IsDistinguishedAt (maximalIdeal T) :=
    (R4IgusaNec.X_isDistinguishedAt _).mul hgdist
  have hg0 : g ≠ 0 := hmonic.ne_zero
  have hXg_deg : (Polynomial.X * g).natDegree = q := by
    rw [Polynomial.natDegree_X_mul hg0, hdeg]; omega
  have hfac : (F.nthSeries q).IsWeierstrassFactorization (Polynomial.X * g) v :=
    ⟨hXg_dist, hv, by rw [hF, Polynomial.coe_mul, Polynomial.coe_X]⟩

  obtain ⟨u, hu, hgen'⟩ := hgen
  have hPeq : P = Polynomial.X * g :=
    (R4IgusaNec.exists_isUnit_eq_mul_iff_eq_of_isWeierstrassFactorization hfac P hPmonic
      (by rw [hPdeg, hXg_deg])).mp ⟨u, hu, by rw [hPcoe]; exact hgen'⟩

  have hP' : P = Polynomial.X * ∏ a ∈ Finset.range (q - 1), (Polynomial.X - Polynomial.C (c (a + 1))) := by
    have hq : q = (q - 1) + 1 := by omega
    rw [hP]
    conv_lhs => rw [hq]
    rw [Finset.prod_range_succ', hc0, map_zero, sub_zero, mul_comm]

  have hg' : g = ∏ a ∈ Finset.range (q - 1), (Polynomial.X - Polynomial.C (c (a + 1))) :=
    R4IgusaNec.X_mul_cancel (hPeq.symm.trans hP')

  rw [hg', Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : 0 < q - 1)) ?_
  rw [Nat.zero_add, hc1, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

end S_FormalGroup_eval_eq_zero_of_nthSeries_eq_mul_prod_X_sub_C_evalNSMul
end P2MW
export P2MW.S_FormalGroup_eval_eq_zero_of_nthSeries_eq_mul_prod_X_sub_C_evalNSMul (solution)
